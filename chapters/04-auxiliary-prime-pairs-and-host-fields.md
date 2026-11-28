# Chapter 4. Auxiliary prime pairs and host fields

In Chapter 3 we reduced `ZeroFreeAll` — the non-vanishing of every primitive Dirichlet
$L$-function $L(s, \psi)$ on $\Re s > 1/2$ — to proving a one-sided Chebyshev-type bound
$\Lambda.\mathrm{Gm}(x) \le x^{1/2 + O(\varepsilon)}$ on sparse windows $[Z, Z^{3/2}]$ for each
cyclic character level $\Lambda = \mathrm{Level.cyc}(\psi)$ (Theorem 3.7) [Lean, read]. Chapter 5
will derive that bound at any scale $x$ equipped with an abelian **CM host field** $E$ (`HostAx`)
and a theta-lift chain (`CoreAtH`). Before either object can be used, however, we have to build
the host field $E$ itself — and building $E$ creates a family of auxiliary Dirichlet characters
whose analytic behaviour must be controlled **without circularity**, using classical unconditional
analytic number theory alone.

That unconditional construction is node `P13` of `notes/proof-map.md` (together with the field
predicates `IsChiField`, `WinPair`, and `PageN` of node `P12`). Every glue file in
`CharacterBoxes/` and `MeanSquareBounds/` that chooses the auxiliary primes, verifies the CM
field structure, bounds the parasitic twists, and rescales the windows has been read line by line
by us (`R3` / `[Lean, read]`). Of the classical analytic sub-packages imported at the bottom of
the sieve, the width-$1/400$ zero-density count and the Landau–Page step across moduli are also
read in full (Section 4.7). The prime number theorem in progressions modulo divisible-by-$8$
moduli, Siegel's lower bound and the internal lemmas of the Perron contour tail were read at
statement level (`R2` / `[Lean]`). Sections 4.8–4.10 later read local proof bodies for the Perron tail with its Perron and local-zero suppliers (§§4.8.7–4.8.8), the candidate count and the relative progression estimate, including its numerical lemma (§4.10.5), the differencing step of its far range (§4.10.6), the residual of the smoothed explicit formula (§4.10.7), its local expansion and rectangle identity (§4.10.8), and the uniform polynomial-growth supply in the half-plane $\Re s \ge 1/2$ (§4.10.9); the deeper analytic suppliers remain at `R2`. We distinguish the two tags explicitly throughout.

[Section 4.4.5.1](#4451-why-coprime-twists-stay-primitive) proves the exact conductor formula for the coprime twists used in both sieve stages.

[§4.10.28](#p13-spaced-zero-density) proves the character-fiber spacing estimates and assembles the far-range density witness from the two block counts.

[Section 4.11](#411-from-separated-inertia-lines-to-residual-irreducibility) follows the bad-prime handoff to residual irreducibility. [Section 4.11.1](#4111-why-a-prime-cycle-forces-primitivity-in-small-degree) proves the small-degree primitivity input to its Jordan call. [Section 4.11.2](#4112-why-three-fixed-points-suffice-in-jordans-theorem) proves the alternating containment step.

---

## 4.1 Motivation

### 4.1.1 Why a target character cannot live alone

Fix a primitive Dirichlet character $\psi \bmod M$ ($M = \psi.N \ge 1$) whose $L$-function we want
to prove zero-free on $\Re s > 1/2$. Why can the arithmetic engine of Part II not simply work
inside the cyclotomic field $\mathbb Q(\zeta_M)$ cut out by $\psi$? Three structural requirements
of the unitary theta-lift chain force us to embed $\psi$ into a larger abelian number field
$E \subset \mathbb Q(\zeta_{N_{\mathrm{cond}}})$ [Lean, read]
(`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:12,87`):

1. **A CM structure with an imaginary quadratic base $K = \mathbb Q(\sqrt{-d})$.** Definite
   unitary groups and Shimura-variety periods require a totally real base field $F = E^+$ and a
   quadratic CM extension $E = F(\sqrt{-d}) = F \cdot K$ in which the prime $2$, the auxiliary
   prime $q$, and every prime dividing $M$ **split completely** in $K = \mathbb Q(\sqrt{-d})$,
   while $d$ itself ramifies (`HostDer.cm`, `hostSplitK`,
   `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean:322`) [Lean, read].
2. **A parity partner $q \equiv 3 \pmod 8$ so both even and odd $\psi$ sit cleanly over $F$.**
   Under the Artin isomorphism $\operatorname{Gal}(\mathbb Q(\zeta_N)/\mathbb Q) \cong (\mathbb Z/N\mathbb Z)^\times$,
   complex conjugation is the residue class $-1 \bmod N$, and the totally real subfield $F = E^+$
   is the fixed field of complex conjugation (`conjE_mem_hostF_iff`,
   `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:199`) [Lean, read].
   An *odd* target character satisfies $\psi(-1) = -1$, so $\psi$ is nontrivial on complex
   conjugation and cannot factor through $\operatorname{Gal}(F/\mathbb Q)$ on its own! Introducing
   a second prime $q \equiv 3 \pmod 8$ supplies an odd quadratic character $(\frac{\cdot}{q})$
   (since $(\frac{-1}{q}) = -1$) whose discriminant $-q \equiv 5 \pmod 8$ is odd — unramified at
   $2$ — allowing odd powers of $\psi$ to pair with $(\frac{\cdot}{q})$ along $F$ while keeping
   complex conjugation nontrivial on both $\sqrt{-q}$ and $\sqrt{-d}$ [Lean, read].
3. **A growing $2$-power cyclotomic layer $2^{e+2}$ matching the chain scale $x$.** To manufacture
   enough independent congruence classes and Hida-type twists for a chain of $m \approx \sqrt{x}$
   theta lifts at scale $x$, the degree $[F : \mathbb Q] = 2\,\varphi.\mathrm{ord}$ must grow
   polynomially with $x$, specifically $\varphi.\mathrm{ord} \asymp x^{2 + 8\varepsilon}$ via a
   real $2$-cyclotomic tower $\mathbb Q(\zeta_{2^{e+2}})^+$ (`PageN`,
   `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:39`) [Lean, read].

### 4.1.2 The price of the host field: parasitic quadratic twists

Once $E$ is built from $\psi$, the real $2$-power layer, $(\frac{\cdot}{q})$, and $(\frac{\cdot}{d})$,
the Dedekind zeta function $\zeta_E(s)$ (or, after finite Fourier projection in Chapter 5, the
projected prime sum over the cyclic subgroup $A_0 \le \operatorname{Gal}(F/\mathbb Q)$) no longer
sees only the target characters $\xi \in \langle \psi \rangle$. Alongside the "kept" characters
of $\mathrm{Level.cyc}(\psi)$, the Fourier sum picks up **parasitic characters**
(`HostRaw.Bounded`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:136`) [Lean, read]
whose primitive conductors are divisible by $q$, by $d$, or by $qd$: concretely, every such
character is induced by a product
$$\mathrm{tw}(\xi, q, d, i, j)(a) := \xi(a)\,\Bigl(\frac{a}{q}\Bigr)^i\,\Bigl(\frac{a}{d}\Bigr)^j,
\qquad \xi \in \langle \psi \rangle,\quad (i, j) \in \{0, 1\}^2 \setminus \{(0, 0)\}$$
(`UpperTheory.Top.boundedTw_key`, `src/Development/AutomorphicArithmetic/CharacterBoxes/BoundedTw.lean:5`) [Lean, read].

Look at what Chapter 5 will need for those parasitic twists (`EAtH.bdG` and `EAtH.bdL`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:144`) [Lean, read]:
at the chain scale $x$, each parasitic primitive character $\chi$ must satisfy
$$\lvert G_\chi(x) \rvert \le x^{1/2 + \varepsilon}
\qquad\text{and}\qquad
\Bigl\lvert \frac{L'}{L}(1, \chi) \Bigr\rvert \le 4 \log x.$$
Hold on: $\lvert G_\chi(x) \rvert \le x^{1/2 + \varepsilon}$ looks like a square-root prime-sum
bound! If proving it for $\chi = \xi \cdot (\frac{\cdot}{q})$ required GRH, the entire argument
would be circular!

How do we get a square-root prime-sum bound for $\xi \cdot (\frac{\cdot}{q})$, $\xi \cdot (\frac{\cdot}{d})$,
and $\xi \cdot (\frac{\cdot}{qd})$ **unconditionally**, without knowing anything about the zeros of
$L(s, \psi)$? Because **we get to choose the primes $q$ and $d$ at each window scale $Y$!** We do
not need the bound for *every* prime $q$; we only need **one good pair $(q, d)$** inside a vast
candidate pool (`QH.pairEx`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112`) [Lean, read]:

- Choose $q \equiv 3 \pmod 8$ with $\log q \asymp Y^{\varepsilon/5}$, so $q \approx \exp(Y^{\varepsilon/5})$
  is **subexponential in $Y$** — vastly larger than any fixed power $Y^{800A}$ of the window
  endpoint $x \in [Y, Y^A]$, yet tiny enough that $\log\log q = \frac{\varepsilon}{5}\log Y + O(1)$!
- By a classical **zero-density estimate** (`zero_density_box`,
  `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`;
  proved in Section 4.7) [Lean, read], among all primitive characters of conductor $\le Q$, at most $O(Q^{1/4})$ can have a zero in the
  rectangle
  $$\mathcal B(Q) := \Bigl\{s \in \mathbb C : \Re s > 1 - \frac{1}{400},\ \lvert \Im s \rvert \le Q\Bigr\}.$$
  Since there are $\ge U^{9/10}$ candidate primes $q \le U$ in our progression (by the prime number
  theorem in progressions and Siegel's theorem), the $O((MU)^{1/4})$ zero-box failures eliminate a
  negligible fraction of candidates!
- For any surviving candidate $q$, the width-$1/400$ zero-free box lets Perron contour shifting
  truncate the explicit formula of $G_\chi(y)$ ($y \in [Y, Y^A]$) at $Z = (Y^A)^{400}$: the shift
  saves $Z^{-1/400} = Y^{-A}$, cancelling the factor $y \le Y^A$ in front of the tail! Meanwhile,
  on the finite Dirichlet polynomial up to $Z = Y^{400A}$, **averaging $\lvert \sum_{n \le Z} a_n (\frac{n}{q}) \rvert^2$
  over $q$** hits off-diagonal character sums $\sum_q (\frac{q}{s})$ for odd squarefree
  $1 < s \le Z^2 = Y^{800A} \ll \exp(\frac{1}{2}Y^{\varepsilon/5}) < q$. Quadratic reciprocity
  turns $(\frac{q}{s})$ into a Dirichlet character modulo $4s$ evaluated at primes $q$, and
  Landau–Page theory says **at most one** modulus $s = n_*$ can carry an exceptional real zero!
  Both the diagonal $s = 1$ and the single Landau–Page modulus $s = n_*$ contribute only
  $O(y \log y)$ on average — giving true square-root cancellation $\le y^{1/2 + \varepsilon/2}$
  for almost every $q$, and then by a second, sequential sieve stage (`stage2`) for almost every
  $d$!

That two-stage analytic sieve, together with the algebraic host assembly it feeds, is the whole
content of Chapter 4.

---

## 4.2 Small examples

Before stating the general definitions, we work through two concrete miniature calculations: first,
how congruences modulo $8$ and $16$ shape a concrete CM host field; second, how the constants
$1/400$, $401$, $\lambda = 3/2$, and $\varepsilon < 1/52$ lock together numerically.

### 4.2.1 Two concrete prime pairs: $(q, d) = (11, 7)$ and $(q, d) = (11, 263)$

First look at the archive's own sanity-check witness `HostExample : HostHyp 11 7`
(`src/Formalism/FrobeniusOrbits/Statement.lean:91`) [Lean, read]:

- $q = 11$ is prime with $11 \equiv 3 \pmod 8$, and $d = 7$ is prime with $7 \equiv 7 \pmod{16}$.
- Because $-7 \equiv 4 = 2^2 \pmod{11}$, the Jacobi symbol $(\frac{-7}{11}) = +1$: thus $q = 11$
  **splits** in $K = \mathbb Q(\sqrt{-7})$ (indeed $11 = \frac{5 + \sqrt{-7}}{2}\cdot\frac{5 - \sqrt{-7}}{2}$
  in $\mathcal O_K = \mathbb Z[\frac{1+\sqrt{-7}}{2}]$).
- Conversely, because $q \equiv d \equiv 3 \pmod 4$, quadratic reciprocity gives
  $$\Bigl(\frac{-11}{7}\Bigr) = \Bigl(\frac{-1}{7}\Bigr)\Bigl(\frac{11}{7}\Bigr)
  = (-1)\cdot\Bigl(-\Bigl(\frac{7}{11}\Bigr)\Bigr)
  = \Bigl(\frac{7}{11}\Bigr)
  = -\Bigl(\frac{-1}{11}\Bigr)\Bigl(\frac{7}{11}\Bigr)
  = -\Bigl(\frac{-7}{11}\Bigr) = -1$$
  (`HostRecip`, `src/Formalism/FrobeniusOrbits/Statement.lean:110`, and `jac_neg_recip`,
  `src/Development/AutomorphicArithmetic/CharacterBoxes/PairHyp.lean:15`) [Lean, read]. So $d = 7$
  is **inert** in $\mathbb Q(\sqrt{-11})$ while $q = 11$ **splits** in $\mathbb Q(\sqrt{-7})$.

In the window predicate `WinPair` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:27`), the archive enforces $(\frac{-d}{p}) = +1$
simultaneously for $p = q$ and for all small odd primes $p$ by the single clean divisibility
requirement $p \mid d + 1$ (`jac_neg_of_dvd`, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairHyp.lean:5`) [Lean, read]: if $p \mid d + 1$,
then $-d \equiv 1 \pmod p$, so $(\frac{-d}{p}) = (\frac{1}{p}) = +1$ automatically! To see a
concrete pair obeying those divisibility rules alongside $q \equiv 3 \pmod 8$ and
$d \equiv 7 \pmod{16}$, take
$$q = 11 \equiv 3 \pmod 8, \qquad d = 263 = 16 \times 16 + 7 \equiv 7 \pmod{16}.$$
Check the arithmetic by hand [Expository]:

1. $263$ is prime (no prime $\le \sqrt{263} < 17$ divides $263$), and
   $$d + 1 = 264 = 8 \times 3 \times 11,$$
   so both the small odd prime $p = 3$ and $q = 11$ divide $d + 1$! Hence $-263 \equiv 1 \pmod 3$
   and $-263 \equiv 1 \pmod{11}$, so $3$ and $11$ split completely in $K = \mathbb Q(\sqrt{-263})$.
2. What about the prime $2$? Because $d \equiv 7 \pmod{16}$, we have $-d \equiv -7 \equiv 1 \pmod 8$!
   By elementary algebraic number theory, $x^2 - x + \frac{1+d}{4} = x^2 - x + 66 \equiv x(x - 1) \pmod 2$,
   so **$2$ is unramified and splits completely in $K = \mathbb Q(\sqrt{-d})$** as well! Meanwhile,
   for $\mathbb Q(\sqrt{-q}) = \mathbb Q(\sqrt{-11})$, $-11 \equiv 5 \pmod 8$, so **$2$ is also
   unramified (inert) in $\mathbb Q(\sqrt{-q})$**! Because neither $\mathbb Q(\sqrt{-q})$ nor
   $\mathbb Q(\sqrt{-d})$ ramifies at $2$, the $2$-adic cyclotomic real subfield
   $F_1 = \mathbb Q(\zeta_{2^{e+2}})^+ = \mathbb Q(\zeta_{2^{e+2}} + \zeta_{2^{e+2}}^{-1})$ (which is
   totally ramified at $2$ of degree $2^e$ and unramified everywhere else) is linearly disjoint from
   $\mathbb Q(\sqrt{-q}, \sqrt{-d})$!
3. Now watch how complex conjugation behaves inside $\mathbb Q(\zeta_N)$ for
   $N = 2^{e+2} \cdot 3 \cdot 11 \cdot 263$, say with $e = 2$ ($2^{e+2} = 16$) and target character
   $\psi$ modulo $3$, $\psi(a) = (\frac{a}{3})$ (an **odd** character, $\psi(-1) = -1$!). Under
   $\operatorname{Gal}(\mathbb Q(\zeta_N)/\mathbb Q) \cong (\mathbb Z/N\mathbb Z)^\times$, complex
   conjugation corresponds to $a \equiv -1 \pmod N$:
   - Modulo $16$: $-1 \equiv -1 \pmod{16}$ satisfies $a \equiv \pm 1 \pmod{16}$, so complex
     conjugation **fixes** $F_1 = \mathbb Q(\zeta_{16})^+$ (`HostReal`,
     `src/Formalism/FrobeniusOrbits/Statement.lean:147`) [Lean, read].
   - Modulo $q = 11$ and $d = 263$: since $11 \equiv 3 \pmod 4$ and $263 \equiv 3 \pmod 4$, we have
     $$\Bigl(\frac{-1}{11}\Bigr) = -1, \qquad \Bigl(\frac{-1}{263}\Bigr) = -1.$$
   - Look at the subgroup $H_E \le (\mathbb Z/N\mathbb Z)^\times$ cutting out $E$ in `IsChiField`
     (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:24–25`):
     $$a \in H_E \iff a \equiv \pm 1 \pmod{16},\quad \psi(a) = 1,\quad
     \Bigl(\frac{a}{11}\Bigr) = 1,\quad \Bigl(\frac{a}{263}\Bigr) = 1.$$
     The four conditions on $(\mathbb Z/16\mathbb Z)^\times \times (\mathbb Z/3\mathbb Z)^\times \times (\mathbb Z/11\mathbb Z)^\times \times (\mathbb Z/263\mathbb Z)^\times$
     (of order $\varphi(N) = 8 \times 2 \times 10 \times 262 = 41{,}920$) are independent of indices
     $4, 2, 2, 2$, so $\lvert H_E \rvert = 1{,}310$ and $[E : \mathbb Q] = 32$ (`4 * φ.ord = 4 * 8 = 32`),
     cutting out $E = F_1(\sqrt{-3}, \sqrt{-11}, \sqrt{-263})$. At $a = -1$, $(\frac{-1}{11}) = -1 \neq 1$
     and $(\frac{-1}{263}) = -1 \neq 1$, so **$-1 \notin H_E$**, even if $\psi$ had been the trivial
     character $\psi = 1$! Specifically, complex conjugation $a \equiv -1 \pmod N$ fixes $F_1$ and
     negates $\sqrt{-3}$, $\sqrt{-11}$, and $\sqrt{-263}$, so its fixed field inside $E$ is the
     degree-$16$ totally real subfield
     $$F = E^+ = F_1\bigl(\sqrt{33},\,\sqrt{789}\bigr)
     = \mathbb Q(\zeta_{16})^+\bigl(\sqrt{(-3)(-11)},\,\sqrt{(-3)(-263)}\bigr),$$
     and $E = F(\sqrt{-263})$ is a **CM extension** of $F$ with
     $\operatorname{Gal}(E/\mathbb Q) \cong (\{\pm 1\} \times \{\pm 1\}) \times (\mathbb Z/2\mathbb Z \times \mathbb Z/4\mathbb Z)$
     (whereas e.g. $a = 17 \equiv 1 \pmod{16}$ fixes $F_1(\sqrt{33}, \sqrt{-263})$ yet satisfies
     $\psi(17) = (\frac{17}{3}) = -1$ and $(\frac{17}{11}) = -1$, so $17 \notin H_E$). Inside the
     character group of $\operatorname{Gal}(E/\mathbb Q)$, the even product $\psi^\flat(a) = \psi(a)(\frac{a}{11})$
     satisfies $\psi^\flat(-1) = (-1)(-1) = +1$, and multiplying $\psi^\flat$ back by the host sign
     character $(\frac{\cdot}{11})$ recovers our original odd target character $\psi$!

### 4.2.2 Why $1/400$, $401$, $\lambda = 3/2$, and $\varepsilon < 1/52$?

A reader inspecting the Lean files encounters four concrete rational numbers: box width $1/400$,
Tate–Shafarevich exponent $401$, window exponent $3/2$, and $\varepsilon < 1/52$. Every one of them
comes from a two-line calculation we can verify on the back of an envelope [Lean, read]:

1. **Why width $1/400$ matches truncation $Z = x^{400}$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:23–28`).** To bound
   $G_\chi(x) = -S_\chi(x) + x\,\frac{L'}{L}(1,\chi)$ for a non-principal primitive character $\chi$,
   the archive splits $-\frac{L'}{L}(1,\chi) = \sum_{n \le Z} \frac{\Lambda(n)\chi(n)}{n} + \mathrm{tailL}_\chi(Z)$
   at $Z = x^{400}$ (`box_of_S`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:28`) [Lean, read].
   When $L(s,\chi)$ has no zeros in $\{\Re s > 1 - 1/400,\ \lvert \Im s \rvert \le Q\}$, shifting a
   smoothed Perron integral to $\Re s = 1 - \frac{1}{400} + \delta$ bounds $\lvert \mathrm{tailL}_\chi(Z) \rvert$
   by roughly $(\log Q)^2 Z^{-1/400 + \delta}$. Multiplying by the prefactor $x$ in $x\,\mathrm{tailL}_\chi(Z)$
   gives
   $$x \cdot Z^{-1/400} = x \cdot \bigl(x^{400}\bigr)^{-1/400} = x^1 \cdot x^{-1} = 1!$$
   The exponent $400$ is simply the reciprocal of the zero-free box width $1/400$, chosen large
   enough that a $Q^{1/4}$ zero-density saving holds unconditionally on $\{\Re s > 1 - 1/400\}$.
2. **Why $\varepsilon < 1/52$ gives the constant $4$ in $\lvert L'(1,\chi)/L(1,\chi) \rvert \le 4\log Y$
   (`src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:9–25, 126–153`).** Apply that same zero-free box of width $1/400$ at a tiny auxiliary
   parameter $x_0 = (\log Q)^{10/4}$ (`s = (\log Q)^{1/4}`, `x = s^{10}`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:10, 56`) [Lean, read].
   Then the prime sum up to $x_0^{400} = (\log Q)^{1000}$ has length $\log(x_0^{400}) = 1000\log\log Q$,
   so Mertens's bound $\sum_{n \le Z} \Lambda(n)/n \le \log Z + O(1)$ gives
   $$\Bigl\lvert \frac{L'}{L}(1,\chi) \Bigr\rvert \le 1000 \log\log Q + O(1)$$
   (`kappa4_loglog`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:44`) [Lean, read].
   In Stage 2 of our sieve, $\log d \asymp Y^{\varepsilon/5}(\log Y)^2$, so $\log Q \le A\,Y^{\varepsilon/5}(\log Y)^2$
   and therefore
   $$1000 \log\log Q \le 1000 \cdot \frac{\varepsilon}{5}\log Y + 2000\log\log Y + O(1)
   = 200\varepsilon \log Y + o(\log Y).$$
   For $\varepsilon < \frac{1}{52}$, we have
   $$200\varepsilon < \frac{200}{52} = \frac{50}{13} = 4 - \frac{2}{13} \approx 3.846 < 4!$$
   That spare $\frac{2}{13}\log Y$ absorbs $2000\log\log Y + O(1)$ for large $Y$ (`13 * (...) ≤ u`
   at `src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:135`), yielding $\lvert \frac{L'}{L}(1,\chi) \rvert \le 4\log Y$ cleanly!
   (A second place also uses $\varepsilon < 1/52$: in `src/Development/AutomorphicArithmetic/CharacterBoxes/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5`,
   bounding all growth exponents using $\varepsilon < 1/52 < 0.02$ makes the Hodge–Tate/Selmer twist
   cutoff satisfy $R.t \le 10708\,x^{399.67} \le \lfloor x^{400} \rfloor$ for large $x$ [Lean, read].)
3. **Why $401 = 1 + 400$ and $\lambda = 3/2$ (`src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean:40–81`).** The global Tate–Shafarevich
   theorem `VWin` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49`) is proved on **quadratic** windows $x' \in [W, W^2]$ at
   pure $2$-power host scale $2^{e(x')} \asymp (x')^{2 + 8\varepsilon}$, controlling twists up to
   $e_{\mathrm{HT}} < \lfloor (x')^{401} \rfloor$. When $\psi$ has conductor $> 1$, `fieldChi`
   multiplies the frame order by a constant $c \ge 1$ depending on $\psi$:
   $\varphi.\mathrm{ord} = c \cdot 2^e$. Setting $k := c^{1/(2 + 8\varepsilon)} \ge 1$ and
   rescaling $x = k x'$ gives $c\,(x')^{2+8\varepsilon} = x^{2+8\varepsilon}$! Once $W \ge \max(k^3, k^{400})$:
   - for $Z := kW$, any $x \in [Z, Z^{3/2}]$ satisfies
     $$x \le (kW)^{3/2} = k^{3/2} W^{3/2} \le W^{1/2} W^{3/2} = W^2,$$
     so $x' = x/k$ lands inside $[W, W^2]$ (shrinking the window exponent from $2$ to $\lambda = 3/2$);
   - meanwhile $k^{400} \le W \le x'$, so
     $$x^{400} = k^{400} (x')^{400} \le x' \cdot (x')^{400} = (x')^{401},$$
     turning the upstream exponent $401$ at $x'$ into the required exponent $400$ (`R.t ≤ x^{400}`)
     at $x$!

---

## 4.3 Definitions

We now record the exact mathematical definitions and Lean structures of nodes `P13` and `P12`
(host-field interface).

### 4.3.1 Good prime pairs, quadratic twists, and zero-free boxes

**Definition 4.1 (Window prime pairs and $2$-power scalings).** Let $\varepsilon > 0$ and $Y \in \mathbb R$,
and let $q, d \in \mathbb N$.

1. **Window prime pair (`WinPair`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:27`).**
   We say $(q, d)$ is a **window prime pair** at $(\varepsilon, Y)$, written `WinPair eps Y q d`, if
   [Lean, read]:
   - $q$ is prime, $q \equiv 3 \pmod 8$, and $\frac{1}{2} Y^{\varepsilon/5} < \log q \le Y^{\varepsilon/5}$;
   - $d$ is prime, $d \equiv 7 \pmod{16}$, and
     $\frac{1}{2} Y^{\varepsilon/5}(\log Y)^2 < \log d \le Y^{\varepsilon/5}(\log Y)^2$;
   - $q \mid d + 1$, and $p \mid d + 1$ for every odd prime $p \le Y^{\varepsilon/5}$.
2. **Dyadic $2$-power exponent (`PageN`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:39`).**
   A function $e : \mathbb R \to \mathbb N$ satisfies `PageN eps e` if for every real $x \ge 1$,
   $$x^{2 + 8\varepsilon} \le 2^{e(x)} \le 2\,x^{2 + 8\varepsilon}$$
   [Lean, read].

**Definition 4.2 (Quadratic twists, zero-free boxes, and `PairGood`).** Let $M \ge 1$ (`[NeZero M]`),
let $\xi$ be an arithmetic sequence (specifically $\xi(a) = \chi_0(a \bmod M)$ for a Dirichlet
character $\chi_0 \bmod M$), and let $q, d \in \mathbb N$ and $(i, j) \in \{0, 1\}^2$ (`Fin 2`).

1. **Quadratic twist (`UpperTheory.Top.tw`, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:9`).**
   For every $a \in \mathbb N$, set [Lean, read]
   $$\mathrm{tw}(\xi, q, d, i, j)(a) := \xi(a)\,\Bigl(\Bigl(\frac{a}{q}\Bigr)^i\,\Bigl(\frac{a}{d}\Bigr)^j\Bigr),$$
   where $(\frac{a}{q}), (\frac{a}{d}) \in \{-1, 0, 1\}$ are Jacobi symbols (`jacobiSym (a : ℤ) q`).
   Note that when $\xi$ has period $M$, $\mathrm{tw}(\xi, q, d, i, j)$ is a Dirichlet character
   modulo $M q d$ (or $2 M q d$), and if $\chi \bmod N$ is its underlying primitive character,
   `An.Induces χ (tw ...) (2 * M * q * d)` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:26`)
   states that $N \mid 2Mqd$ and $\chi(a) = \mathrm{tw}(\xi, q, d, i, j)(a)$ whenever
   $\gcd(a, 2Mqd) = 1$ [Lean, read].
2. **Width-$1/400$ zero-free box (`ZeroBox` / `ZeroFreeBox`).** For $H > 0$ and a Dirichlet
   character $\chi \bmod N$, `ZeroBox H χ` (`src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:12`, identical on $H = Q$ to
   `ZeroFreeBox Q χ` at `src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:44`)
   holds if for every $s \in \mathbb C$ [Lean, read]:
   $$1 - \frac{1}{400} < \Re s \quad\text{and}\quad \lvert \Im s \rvert \le H
   \implies L(s, \chi) \neq 0.$$
   For $M \ge 1$, reals $\varepsilon, Y$, and $j \in \{0, 1\}$, the box height assigned to Stage
   $j$ is (`height`, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:15`) [Lean, read]:
   $$\mathrm{height}(M, \varepsilon, Y, j) := 8 M\,\exp\bigl(Y^{\varepsilon/5}\bigr)\,\Bigl(\exp\bigl(Y^{\varepsilon/5}(\log Y)^2\bigr)\Bigr)^j.$$
3. **Analytically good prime pair (`PairGood` and `PairEx`, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:18,28`).**
   Given $M \ge 1$ and reals $\varepsilon, Y, X$, a pair $(q, d)$ satisfies `PairGood M eps Y X q d`
   if `WinPair eps Y q d` holds, $\gcd(M, qd) = 1$, and [Lean, read]:
   - **(`bounds`)** for every Dirichlet character $\xi \bmod M$, every $(i, j) \in \{0, 1\}^2$ with
     $(i \neq 0 \lor j \neq 0)$, every $\chi \bmod N$ (`[NeZero N]`) satisfying
     `An.Induces χ (tw (fun a => ξ a) q d i j) (2 * M * q * d)` (note `An.Induces` includes
     `χ.IsPrimitive`), and every real $y \in [Y, X]$,
     $$\lVert G_\chi(y) \rVert \le y^{1/2 + \varepsilon/2}
     \qquad\text{and}\qquad
     \Bigl\lVert \frac{L'}{L}(1, \chi) \Bigr\rVert \le 4 \log y,$$
     where $G_\chi = \mathrm{An.gChi}\,\chi$ is the normalized Riesz prime sum of Chapter 3
     (Definition 3.1); and
   - **(`boxes`)** for every real primitive character $\rho \in \mathrm{PChar}$ (`ρ.IsReal`) with
     $\rho.N \mid 8M$, every $(i, j) \in \{0, 1\}^2$ with $(i \neq 0 \lor j \neq 0)$, and every
     $\chi \bmod N$ (`[NeZero N]`) satisfying `An.Induces χ (tw ρ.val q d i j) (2 * M * q * d)`,
     `ZeroBox (height M eps Y j) χ` holds.
   The global existence proposition `PairEx : Prop` (`src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:28`) asserts that for every
   $M \ge 1$, every $0 < \varepsilon < 1/52$, and every $A \ge 1$, there exists $Y_1$ such that
   for every $Y \ge Y_1$, there exist $q, d \in \mathbb N$ satisfying `PairGood M eps Y (Y^A) q d`
   [Lean, read].

### 4.3.2 Classical sieve inputs (`ZeroDensityBox`, `MeanSq`, and arithmetic progressions)

Inside `MeanSquareBounds/` and `GL3MeanSquares/`, the two-stage sieve operates on prime sets in
arithmetic progressions modulo a multiple of $8$: for $m_0, a_0 \in \mathbb N$ and $U \in \mathbb R$,
$$\mathrm{PPset}(m_0, a_0, U) := \bigl\{q \in [1, \lfloor U \rfloor] : q\text{ prime},\ q > U^{1/2},\ q \equiv a_0 \pmod{m_0}\bigr\}$$
(`PPset`, `src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:50`) [Lean, read].
Notice the dyadic lower bound $q > U^{1/2}$, which means $\frac{1}{2}\log U < \log q \le \log U$.

**Definition 4.3 (Zero-density and mean-square interfaces).**

1. **Zero-density bound in boxes of width $1/400$ (`ZeroDensityBox`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean:7`).**
   `ZeroDensityBox : Prop` asserts that there exists a constant $C \in \mathbb R$ such that for every
   real $Q \ge 3$, every finite set of pairs $(N, \chi)$ with $1 \le N \le Q$, $\chi \bmod N$ primitive,
   and $\neg\mathrm{ZeroFreeBox}(Q, \chi)$ has cardinality at most $C\,Q^{1/4}$ [Lean, read]. Definition 4.5
   gives the exact form.
   (Its proof term `zero_density_box : ZeroDensityBox` lives at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`
   and is read in full in Section 4.7 [Lean, read].)
2. **Truncated Riesz prime sum and $L^2$ family hypothesis (`QH.S` and `QH.MeanSq`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:13,26`).**
   For an arithmetic weight $\kappa : \mathbb N \to \mathbb C$ with $\lVert \kappa(n) \rVert \le 1$,
   truncation $Z \in \mathbb R$, scale $y \in \mathbb R$, and integer $q \in \mathbb N$, define
   $c_n(y) := \Lambda(n)\min(1, y/n) = \frac{\Lambda(n)}{n}\min(n, y)$ (`cN y n`,
   `src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:23`) and the truncated Jacobi-twisted prime
   sum [Lean, read]
   $$S(Z, y, q, \kappa) := \sum_{1 \le n \le \lfloor Z \rfloor} \Lambda(n)\,\min\Bigl(1, \frac{y}{n}\Bigr)\,\kappa(n)\,\Bigl(\frac{n}{q}\Bigr)
   = \sum_{1 \le n \le \lfloor Z \rfloor} \frac{\Lambda(n)}{n}\,\min(n, y)\,\kappa(n)\,\Bigl(\frac{n}{q}\Bigr).$$
   Observe the exact algebraic identity linking $\min(1, y/n)$ to the Riesz ramp $(y/n - 1)_+$:
   for $n \le y$ we have $\frac{y}{n} - (\frac{y}{n} - 1)_+ = 1 = \min(1, y/n)$, and for $n > y$
   we have $\frac{y}{n} - (\frac{y}{n} - 1)_+ = \frac{y}{n} = \min(1, y/n)$. Multiplying by
   $\Lambda(n)\kappa(n)(\frac{n}{q})$ and summing over $1 \le n \le \lfloor Z \rfloor$ ($Z \ge y > 0$)
   yields
   $$S(Z, y, q, \kappa) - y\sum_{1 \le n \le \lfloor Z \rfloor} \frac{\Lambda(n)\kappa(n)(\frac{n}{q})}{n}
   = -\sum_{1 \le n \le \lfloor y \rfloor} \Lambda(n)\Bigl(\frac{y}{n} - 1\Bigr)\kappa(n)\Bigl(\frac{n}{q}\Bigr)$$
   (`finite_splitting_of_group` and `src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:45–50`) [Lean, read]! That algebraic identity is
   why bounding $\lVert S(Z, y, q, \kappa) \rVert \le \frac{1}{2}y^{1/2 + \tau}$ directly bounds the
   Riesz prime sum on $[1, y]$ by $\frac{1}{2} y^{1/2 + \tau}$! Given $C, Z \in \mathbb R$, a finite
   prime set $P \subset \mathbb N$, and a scale set $A \subseteq \mathbb R$, the proposition
   `MeanSq C Z P A` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:26`) states that for every $y \in A$ and every
   $\kappa : \mathbb N \to \mathbb C$ with $\lVert \kappa(n) \rVert \le 1$,
   $$\sum_{q \in P} \bigl\lVert S(Z, y, q, \kappa) \bigr\rVert^2
   \le C\,y\,\log y\,\lvert P \rvert$$
   [Lean, read].

### 4.3.3 Frames, CM host fields, and the window bound interface

We finally state the field-theoretic structures linking `P13` to `VWin` (`P12`) and `core_gm` (`P6`).

**Definition 4.4 (`IsChiField`, `Frame`, `HostRaw` / `HostAx`, and `VWin`).**

1. **Character-cut cyclotomic subfield (`IsChiField`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:19`).**
   For a primitive character $\psi \in \mathrm{PChar}$, integers $e, q, d \in \mathbb N$, and a
   number field $E$ (`[Field E] [NumberField E]`), `IsChiField ψ e q d E` holds if there exist a
   modulus $N \ge 1$ (`[NeZero N]`), a field embedding $\iota : E \hookrightarrow \mathbb C$, and a
   primitive $N$-th root of unity $\zeta_N \in \mathbb C$ such that
   $2^{e+2} \mid N$, $\psi.N \mid N$, $q \mid N$, $d \mid N$, and for every field automorphism
   $\tau$ of $\mathbb C$ and every $a \in \mathbb N$ with $\tau(\zeta_N) = \zeta_N^a$, $\tau$ fixes
   $\iota(E)$ pointwise if and only if [Lean, read]:
   $$\bigl(a \equiv 1 \pmod{2^{e+2}} \lor a \equiv -1 \pmod{2^{e+2}}\bigr)
   \ \land\ \psi.\chi(a) = 1
   \ \land\ \Bigl(\frac{a}{q}\Bigr) = 1
   \ \land\ \Bigl(\frac{a}{d}\Bigr) = 1.$$
2. **Abelian Galois frame (`Formalism.HC.Frame`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:15`).**
   A `Frame` $\varphi$ specifies finite abelian group parameters $(r, s, v_i, e)$ with $2^e$
   dividing $v_0$, defining the additive finite abelian group $A := \bigoplus_{i=0}^{r-1} \mathbb Z/v_i\mathbb Z$
   of order $\varphi.\mathrm{ord} = \prod_i v_i$ (`card_A`, `:47`), a distinguished cyclic subgroup
   $A_0 = \langle a_0 \rangle \le A$ of index $\varphi.o = [\varphi.A : A_0]$ (`o`, `:70`), and the
   full Galois model group
   $$\varphi.\mathrm{GG} := (\mathbb Z^\times \times \mathbb Z^\times) \times \mathrm{Multiplicative}(A)$$
   of cardinality $4\,\varphi.\mathrm{ord}$ (`natCard_GG`, `:137`), with distinguished order-$2$
   elements $\mathrm{sg} = ((-1, 1), 1)$, $\mathrm{iod} = ((1, -1), 1)$, and complex conjugation
   $\mathrm{cc} = ((-1, -1), 1)$, and CM subset $\Psi = \{((u_1, u_2), m) : u_2 = 1\}$ of size
   $2\,\varphi.\mathrm{ord}$ (`Psi`, `:112`) [Lean, read].
3. **CM host datum (`HostRaw` and `HostAx`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:12,87,174`).**
   Given a frame $\varphi$, `HostRaw φ` packages an abelian number field $E$, primes $q, d$ obeying
   `HostHyp q d` ($q \equiv 3 \pmod 8$, $d \equiv 7 \pmod{16}$, $(\frac{-d}{q}) = 1$), a base
   modulus $QS$ coprime to $qd$ and divisible by $2^{e+2}$ (`condN = QS * q * d`), elements
   $\sqrt{-d}, b_E \in E$, a Galois isomorphism $\mathrm{gal} : \operatorname{Gal}(E/\mathbb Q) \xrightarrow{\sim} \varphi.\mathrm{GG}$
   sending complex conjugation to $\mathrm{cc} = ((-1,-1), 1)$, and an Artin map
   $\mathrm{art} : (\mathbb Z/\mathrm{condN}\,\mathbb Z)^\times \twoheadrightarrow \varphi.\mathrm{GG}$
   whose first two sign coordinates are $(\frac{\cdot}{q})$ and $(\frac{\cdot}{d})$ [Lean, read].
   `HostAx φ` (`:174`) pairs `HostRaw φ` with `HostDer` (`:87`), recording that $E$ is a CM field
   over its totally real subfield $F = E^{\langle \mathrm{cc} \rangle}$ (`[IsCMField E]`,
   `[IsTotallyReal F]`), $[E : \mathbb Q] = 4\,\varphi.\mathrm{ord}$, $[F : \mathbb Q] = 2\,\varphi.\mathrm{ord}$,
   and $K = \mathbb Q(\sqrt{-d}) \subset E$ [Lean, read].
4. **Window Tate–Shafarevich bound (`VVle`, `VAt`, `VWinAt`, `VWin`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12,41,44,49`).**
   For a number field $E$, $T \in \mathbb N$, and $B \in \mathbb R$, `VVle E T B` states that
   $B \ge 0$ and for every finite set $L$ of primes $\ell$,
   $$\sum_{\ell \in L} \log \ell \sum_{1 \le e < T}
   \operatorname{len}_{\mathbb Z_\ell}\,Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e)\bigr) \le B$$
   (`Formalism.GaloisCohomology.shaLen`, `src/Formalism/GaloisCohomology/Statement.lean:78`) [Lean, read].
   Then `VAt ψ k x e q d` (`:41`) asserts `VVle E ⌊x^k⌋₊ (exp(x^eps / 2))` (at $\varepsilon$ supplied
   by `VWinAt`) for every $E$ satisfying `IsChiField ψ e q d E`; `VWinAt ψ k` (`:44`) states that
   for every $0 < \varepsilon < 1/52$ and every `PageN eps e`, there exist $A \ge 1$ and $X_0$ such
   that for all $X \ge X_0$ and all $(q, d)$ satisfying `WinPair eps (X^{1/A}) q d`, there is a
   quadratic window $[W, W^2] \subseteq [X^{1/A}, X]$ on which `VAt ψ k eps x (e x) q d` holds; and
   $$\mathrm{VWin} :\iff \forall \psi : \mathrm{PChar},\ \mathrm{VWinAt}\,\psi\,401$$
   (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49`) [Lean, read].

---

## 4.4 Lemmas and proofs

We now prove the results of Chapter 4 in logical order: from the elementary dyadic and Jacobi-symbol
lemmas, through the single-stage sieve (`QH.stage` and its four components `count_bad`, `box_of_S`,
`meanSqK`/`twistK`, and the Sobolev–Markov inequality `bad_share`), to the two-stage prime-pair
theorem `pairEx`, and finally to `winPairs` and the host-supply theorem `supplyChi`.

### 4.4.1 Dyadic $2$-powers, splitting congruences, and CM exclusion of complex conjugation

**Lemma 4.1 (Existence of `PageN` and splitting properties of `WinPair`).**

1. *For every $\varepsilon > 0$, there exists $e : \mathbb R \to \mathbb N$ satisfying `PageN eps e`.*
   *(Lean: `UpperTheory.Top.exists_pageN`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:67`.)* [Lean, read]
2. *If `WinPair eps Y q d` holds, then `HostHyp q d` holds ($q \equiv 3 \pmod 8$ prime,
   $d \equiv 7 \pmod{16}$ prime, $(\frac{-d}{q}) = 1$), $(\frac{-q}{d}) = -1$, and $(\frac{-d}{p}) = 1$
   for every odd prime $p \le Y^{\varepsilon/5}$. Moreover, if $Y^{\varepsilon/5} \ge 4$, then $q > 3$.*
   *(Lean: `UpperTheory.Top.pairHyp`, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairHyp.lean:24`,
   and inline in `src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:88–94`.)* [Lean, read]

*Proof.*

1. For each real $x \ge 1$, set $y := x^{2 + 8\varepsilon} \ge 1$ (since $2 + 8\varepsilon > 0$), and
   choose the minimal $k \in \mathbb N$ with $y \le 2^k$ (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:69–77`). For $y = 1$,
   $k = 0$ satisfies $1 \le 2^0 \le 2$; for $y > 1$, minimality gives $k \ge 1$ and $2^{k-1} < y \le 2^k$,
   hence $y \le 2^k < 2y$. Setting $e(x) := k$ gives $x^{2 + 8\varepsilon} \le 2^{e(x)} \le 2\,x^{2 + 8\varepsilon}$.
2. Let $(q, d)$ satisfy `WinPair eps Y q d`. By definition $q$ is prime with $q \equiv 3 \pmod 8$
   and $d$ is prime with $d \equiv 7 \pmod{16}$. For any odd prime $p$ dividing $d + 1$ (which
   includes both $p = q$, by `d_q`, and every odd prime $p \le Y^{\varepsilon/5}$, by `d_small`),
   we have $d + 1 \equiv 0 \pmod p$, so $-d \equiv 1 \pmod p$. Since $p$ is odd,
   $$\Bigl(\frac{-d}{p}\Bigr) = \Bigl(\frac{1}{p}\Bigr) = 1$$
   (`jac_neg_of_dvd`, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairHyp.lean:5`). Taking $p = q$ gives `HostHyp q d`. Next, since
   $q \equiv 3 \pmod 8 \implies q \equiv 3 \pmod 4$ and $d \equiv 7 \pmod{16} \implies d \equiv 3 \pmod 4$,
   we have $q \neq d$ (they are incongruent modulo $8$) and $(\frac{-1}{q}) = (\frac{-1}{d}) = -1$.
   By quadratic reciprocity for distinct odd primes $q \equiv d \equiv 3 \pmod 4$,
   $$\Bigl(\frac{-q}{d}\Bigr) = -\Bigl(\frac{q}{d}\Bigr) = \Bigl(\frac{d}{q}\Bigr)
   = -\Bigl(\frac{-d}{q}\Bigr) = -1$$
   (`jac_neg_recip`, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairHyp.lean:15`). Finally, if $Y^{\varepsilon/5} \ge 4$ (`4 * ψ.N ≤ b` in
   `src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:45,88–94`), then $\log q > \frac{1}{2} Y^{\varepsilon/5} \ge 2$, so
   $q > e^2 > 7.38 > 3$. $\square$

**Lemma 4.2 (CM structure of the host field and characterisation of parasitic twists).** *Let
$\psi \in \mathrm{PChar}$, let $\varphi$ be a `Frame`, and let $H : \mathrm{HostRaw}\,\varphi$.*

1. *Complex conjugation $\mathrm{conj} = \mathrm{gal}^{-1}(\mathrm{cc})$ is a central involution of
   $\operatorname{Gal}(E/\mathbb Q)$ with $\mathrm{conj}(\sqrt{-d}) = -\sqrt{-d} \neq \sqrt{-d}$;
   its fixed field $F = E^{\langle\mathrm{conj}\rangle}$ is totally real of degree $2\,\varphi.\mathrm{ord}$,
   and $E = F(\sqrt{-d})$ is a CM field of degree $4\,\varphi.\mathrm{ord}$. Moreover, if `KerChi ψ H`
   holds ($\psi.N \mid H.QS$ and $\operatorname{ker} H.\mathrm{art} = \{a \bmod \mathrm{condN} : a \equiv \pm 1 \pmod{2^{e+2}},\ \psi(a)=1,\ (\frac{a}{q})=1,\ (\frac{a}{d})=1\}$),
   then `IsChiField ψ φ.e H.q H.d E` holds.*
   *(Lean: `HostDer` / `isCMField_hostE` / `conj_sqd`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:87,182`
   and `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean:254`; `UpperTheory.Top.isChiField`, `src/Development/AutomorphicArithmetic/CharacterBoxes/IsChiField.lean:5`.)* [Lean, read]
2. *Suppose in addition that `TwistForm ψ H` holds, $\psi.N \mid H.QS$, and every prime divisor of
   $H.QS$ divides $2\psi.N$. Then for every parasitic character
   $\theta \in H.\mathrm{Bounded}((\mathrm{Level.cyc}\,\psi).\mathrm{KEPT})$ and its primitive
   Dirichlet character $\chi \bmod N_\chi$, there exist $\xi \in \langle \psi.\chi \rangle$ and
   $(i, j) \in \{0, 1\}^2$ with $(i \neq 0 \lor j \neq 0)$ such that $\chi$ is induced by
   $\mathrm{tw}(\xi, H.q, H.d, i, j)$ modulo $2\,\psi.N\,H.q\,H.d$. Consequently, if
   `PairGood ψ.N eps Y x H.q H.d` holds with $1 \le Y \le x$, then $\lvert G_\chi(x) \rvert \le x^{1/2 + \varepsilon}$
   and $\lvert \frac{L'}{L}(1, \chi) \rvert \le 4\log x$.*
   *(Lean: `UpperTheory.Top.boundedTw_key` and `boundedTw`, `src/Development/AutomorphicArithmetic/CharacterBoxes/BoundedTw.lean:5,45`.)* [Lean, read]

*Proof.*

1. Because $\varphi.\mathrm{GG} = (\{\pm 1\} \times \{\pm 1\}) \times \mathrm{Multiplicative}(A)$ is
   abelian of order $4\,\varphi.\mathrm{ord}$, the element $\mathrm{cc} = ((-1, -1), 1)$ is central
   of order $2$. By the defining axiom `gal_spec` of `HostRaw` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:45`), under
   the cyclotomic embedding $\iota : E \hookrightarrow \mathbb C$, $\iota \circ \mathrm{gal}^{-1}(\mathrm{cc})$
   acts as complex conjugation on $\mathbb C$. Since $\sqrt{-d} \neq 0$ satisfies $(\sqrt{-d})^2 = -d < 0$,
   its image in $\mathbb C$ is purely imaginary, so $\mathrm{conj}(\sqrt{-d}) = -\sqrt{-d} \neq \sqrt{-d}$
   (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean:254`). Every complex embedding of $F = E^{\langle\mathrm{conj}\rangle}$ commutes
   with $\operatorname{Gal}(E/\mathbb Q)$ (as $E/\mathbb Q$ is abelian!), so complex conjugation
   restricts to the identity under *every* complex embedding of $F$ (making $F$ totally real) and is
   nontrivial under *every* complex embedding of $E$ (making $E$ totally imaginary, hence CM over
   $F$, with $[E : \mathbb Q] = \lvert \varphi.\mathrm{GG} \rvert = 4\,\varphi.\mathrm{ord}$ and
   $[F : \mathbb Q] = 2\,\varphi.\mathrm{ord}$). Finally, if `KerChi ψ H` holds and $\tau(\zeta_{\mathrm{condN}}) = \zeta_{\mathrm{condN}}^a$,
   preserving primitive roots forces $\gcd(a, \mathrm{condN}) = 1$; by `art_spec`, $\tau$ fixes
   $\iota(E)$ if and only if $H.\mathrm{art}(a) = 1$, which `KerChi` equates to the four conditions
   of `IsChiField` (`src/Development/AutomorphicArithmetic/CharacterBoxes/IsChiField.lean:22–51`).
2. Recall from `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:92–94, 136` that among characters $\theta \in \widehat{\varphi.\mathrm{GG}}$
   trivial on the cyclic subgroup $A_0 \le A$, the plus-space $X_p$ consists of those with
   $\theta(\mathrm{iod}) = +1$, the minus-space $X_m$ consists of those with $\theta(\mathrm{iod}) = -1$,
   and `Bounded` is $(X_p \setminus \mathrm{Kept}) \cup X_m$. By `TwistForm ψ H`, there exist
   $\xi \in \langle \psi.\chi \rangle$ and $(i, j) \in \{0, 1\}^2$ such that $\theta(\mathrm{iod}) = (-1)^j$
   and $\theta(H.\mathrm{art}(a)) = \mathrm{tw}(\xi, q, d, i, j)(a)$ for all $\gcd(a, \mathrm{condN}) = 1$.
   Suppose for a contradiction that $(i, j) = (0, 0)$ (`src/Development/AutomorphicArithmetic/CharacterBoxes/BoundedTw.lean:19–32`). Then:
   - $\theta(\mathrm{iod}) = (-1)^0 = +1$, so $\theta \notin X_m$;
   - $\mathrm{tw}(\xi, q, d, 0, 0)(a) = \xi(a)$ on $\gcd(a, \mathrm{condN}) = 1$, so the primitive
     character of $\theta$ is $\mathrm{PChar.of}(\xi) \in (\mathrm{Level.cyc}\,\psi).\mathrm{KEPT}$,
     meaning $\theta \in \mathrm{Kept}$!
   That contradicts $\theta \in (X_p \setminus \mathrm{Kept}) \cup X_m$. Hence $(i \neq 0 \lor j \neq 0)$.
   Since every prime dividing $\mathrm{condN} = QS \cdot q \cdot d$ divides $2\,\psi.N\,q\,d$,
   coprimality to $2\,\psi.N\,q\,d$ is equivalent to coprimality to $\mathrm{condN}$, so $\chi$ is
   induced by $\mathrm{tw}(\xi, q, d, i, j)$ modulo $2\,\psi.N\,q\,d$. Applying `PairGood.bounds` at
   $x \in [Y, x]$ gives $\lvert G_\chi(x) \rvert \le x^{1/2 + \varepsilon/2} \le x^{1/2 + \varepsilon}$
   (as $x \ge 1$ and $\varepsilon > 0$) and $\lvert \frac{L'}{L}(1,\chi) \rvert \le 4\log x$. $\square$

### 4.4.2 Bounding zero-free box failures via zero density (`count_bad`)

We now enter the analytic sieve for a single prime selection in $\mathrm{PPset}(m_0, a_0, U)$,
where $8 \mid m_0$, $\gcd(a_0, m_0) = 1$, and $U = \exp(z)$. Given a finite family $\Xi$ of at most
$R + 1$ base primitive characters $\xi_r \bmod f_r$ with odd-or-$2$-bounded conductors $f_r \le F$
(think of $\xi_r$ as the primitive characters of $\chi_0 \cdot \chi_8^\nu$ for $\chi_0 \bmod M$,
or in Stage 2 with $(\frac{\cdot}{q})$ adjoined, so $R + 1 \le 4M$ and $F \le 8Mq$), we want almost
every $q \in \mathrm{PPset}(m_0, a_0, U)$ to give twist characters $\psi_{r, q} = \xi_r \cdot (\frac{\cdot}{q})^*$
that are **zero-free** in $\mathcal B(Q)$ and have **small prime sums** on $[Y, Y^K]$.

First we bound the number of primes $q$ where the zero-free box fails.

**Lemma 4.3 (Zero-free box failures via `ZeroDensityBox`).** *Assume `ZeroDensityBox` with constant
$C_{\mathrm{ZD}} \ge 0$. Let $F \ge 1$, $U \ge 2$ and $Q \ge 3$ with $F < U^{1/2}$ and $FU \le Q$, and let
$(f_r, \xi_r)_{r \in I}$ be a family of at most $R + 1$ primitive characters with $1 \le f_r \le F$.
Suppose that for each $r \in I$ and each prime $q \in \mathrm{PPset}(m_0, a_0, U)$, we are given a
primitive character $\psi_{r, q}$ of conductor $f_r q$ (namely $\xi_r$ twisted by the primitive
quadratic character of prime conductor $q$, which is primitive because $q > U^{1/2} > F \ge f_r$ so
$\gcd(f_r, q) = 1$). Then the set of "zero-bad" primes*
$$B_1 := \bigl\{q \in \mathrm{PPset}(m_0, a_0, U) : \exists r \in I,\ \neg\mathrm{ZeroFreeBox}(Q, \psi_{r, q})\bigr\}$$
*has cardinality*
$$\lvert B_1 \rvert \le C_{\mathrm{ZD}}\,Q^{1/4}.$$
*(Lean: `QH.count_bad_core` and `QH.count_bad`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBadCore.lean:18`
and `src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean:9`, invoking `zero_density_box` [Lean, read] at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`.)* [Lean, read]

*Proof.* Notice something even sharper than a naive $(R + 1)\,C_{\mathrm{ZD}}\,Q^{1/4}$ union bound:
the factor $R + 1$ **disappears completely** (`src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBadCore.lean:34–59`)! Why? For each $q \in B_1$,
choose one witness $r(q) \in I$ such that $\psi_{r(q), q}$ fails `ZeroFreeBox Q`, and consider the
map
$$q \longmapsto \bigl(f_{r(q)} q,\ \psi_{r(q), q}\bigr).$$
First, its image lies in the zero-density exception set of level $\lfloor Q \rfloor$: indeed
$1 \le f_{r(q)} q \le F \lfloor U \rfloor \le FU \le Q$, $\psi_{r(q), q}$ is primitive, and
$\neg\mathrm{ZeroFreeBox}(Q, \psi_{r(q), q})$. Second, **this map is injective on $B_1$**! Suppose
$q_1, q_2 \in B_1$ satisfy $f_{r(q_1)} q_1 = f_{r(q_2)} q_2$. Every $q \in \mathrm{PPset}(m_0, a_0, U)$
is prime and satisfies
$$q > U^{1/2} > F \ge f_r.$$
Since $q_1$ is prime and divides $f_{r(q_2)} q_2$, Euclid's lemma says either $q_1 \mid f_{r(q_2)}$
(impossible, since $f_{r(q_2)} \le F < q_1$ and $f_{r(q_2)} \ge 1$) or $q_1 \mid q_2$. Because $q_1$
and $q_2$ are both prime, $q_1 \mid q_2$ forces $q_1 = q_2$! By `ZeroDensityBox`, the target set of
bad pairs $(N, \chi)$ with $N \le \lfloor Q \rfloor$ has cardinality at most $C_{\mathrm{ZD}}\,Q^{1/4}$,
so $\lvert B_1 \rvert \le C_{\mathrm{ZD}}\,Q^{1/4}$. $\square$

*(Remark on `zero_density_box`.)* In the archive, `zero_density_box`
(`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`)
is proved unconditionally inside the ten `CountZ*` files of `JacobiCharacterSums/`. The method is
mollifier zero detection followed by Bombieri's duality inequality, with off-diagonal terms bounded
trivially by complete character sums. The arithmetic large sieve is not used. Section 4.7 reads
these files and their direct dependencies line by line, so `zero_density_box` now carries
`[Lean, read]` (`R3`), as does the reduction `count_bad_core` / `count_bad` above.

### 4.4.3 Splitting $G_\chi(y)$ at $Z = (Y^K)^{400}$ (`box_of_S`, `tailK`, `kappa4`)

Once $q \notin B_1$, every twist $\chi = \psi_{r, q}$ has no zeros in $\mathcal B(Q)$. The next two
lemmas show that inside $q \notin B_1$, bounding $G_\chi(y)$ and $\frac{L'}{L}(1,\chi)$ reduces
completely to bounding the finite Jacobi-twisted sum $S(Z, y, q, \kappa)$ at $Z = (Y^K)^{400}$.

**Lemma 4.4 (Explicit-formula tail and logarithmic-derivative bound from `ZeroFreeBox`).** *Let
$0 < \varepsilon < 1/52$ and $K \ge 1$.*

1. **(`QH.tailK`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:92`, using
   `tail_contour` [Lean] at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContour.lean:14`; see Statement 4.18.)**
   *There exists $Y_1 \ge 3$ such that for all $Y \ge Y_1$, all $y \in [Y, Y^K]$, all $Q$ with
   $Y^{\varepsilon/6} \le \log Q \le Y^{\varepsilon/4}$, and every non-principal primitive character
   $\chi \bmod N$ with $N \le Q$ and `ZeroFreeBox Q χ`,*
   $$\Bigl\lvert y \cdot \mathrm{tailL}_\chi\bigl((Y^K)^{400}\bigr) \Bigr\rvert \le Y^\varepsilon,
   \qquad\text{where}\quad
   \mathrm{tailL}_\chi(Z) := -\frac{L'}{L}(1, \chi) - \sum_{1 \le n \le \lfloor Z \rfloor} \frac{\Lambda(n)\chi(n)}{n}.$$
   [Lean, read]
2. **(`QH.kappa4`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:126`.)**
   *For every $A \ge 1$, there exists $Y_2 \ge 3$ such that whenever $Y \ge Y_2$,
   $Y^{\varepsilon/6} \le \log Q \le A\,Y^{\varepsilon/5}(\log Y)^2$, and $\chi \bmod N$ is a
   non-principal primitive character with $N \le Q$ and `ZeroFreeBox Q χ`,*
   $$\Bigl\lvert \frac{L'}{L}(1, \chi) \Bigr\rvert \le 4 \log Y.$$
   [Lean, read]
3. **(`QH.box_of_S`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:28`.)**
   *There exists an absolute constant $C > 0$ (`kappaC`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/kappaC.lean:10`) such
   that for $0 < \varepsilon \le 1/4$, $\tau > 0$, $K \ge 1$, and all sufficiently large $Y$
   ($\ge 16$), whenever $Y^{\varepsilon/6} \le \log Q \le Y^{\varepsilon/4}$, `GoodC Q χ` holds
   (`χ ≠ 1 ∧ (N : ℝ) ≤ Q ∧ ZeroFreeBox Q χ`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:32`),
   $\chi(n) = \kappa(n)\,(\frac{n}{q})$ for all $n \in \mathbb N$, and
   $\lVert S((Y^K)^{400}, y, q, \kappa) \rVert \le \frac{1}{2} y^{1/2 + \tau}$ for all
   $y \in [Y, Y^K]$, then `Box Q C τ Y (Y^K) χ` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:35`) holds:*
   $$\lVert G_\chi(y) \rVert \le y^{1/2 + \tau} \quad \forall y \in [Y, Y^K],
   \qquad\text{and}\qquad
   \Bigl\lVert \frac{L'}{L}(1, \chi) \Bigr\rVert \le C \log Y.$$
   *(In `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:117,162`, the generic $C\log Y$ output of `box_of_S` is then sharpened to
   $4\log y$ on $[Y, Y^A]$ by applying part 2, `kappa4`, once $\varepsilon < 1/52$!)* [Lean, read]

*Proof.*

1. Set $x := Y^K$ and $Z := x^{400}$, with finite-difference step $\eta := x^{-2}$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:119–124`).
   Using the difference identity $\eta Z \cdot \mathrm{tailL}_\chi(Z) = -(S_\chi(Z + \eta Z) - S_\chi(Z) + \eta Z \frac{L'}{L}(1,\chi)) + (S_\chi(Z + \eta Z) - S_\chi(Z) - \eta Z \sum_{n \le Z} \frac{\Lambda(n)\chi(n)}{n})$,
   the contour estimate `tail_contour` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContour.lean:14` [Lean], called at `src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:102`) on $\mathcal B(Q)$ bounds the
   first term by $K_0 (\log Q)\bigl((\log Q)\eta Z^{1 - 1/400 + \varepsilon/(1600K)} + Z^2 / Q\bigr)$,
   while Mertens's bound controls the short sum over $(Z, Z + \eta Z]$. Dividing by $\eta Z$ and
   multiplying by $x = Y^K$ (`tailK_num`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:23–89`), watch each of the three pieces:
   - The zero-free boundary term has size
     $$K_0 (\log Q)^2 \cdot x \cdot Z^{-1/400 + \varepsilon/(1600K)}
     = K_0 (\log Q)^2 \cdot x \cdot x^{-1 + \varepsilon/(4K)}
     = K_0 (\log Q)^2\,Y^{\varepsilon/4} \le K_0\,Y^{3\varepsilon/4} \le \frac{1}{3} Y^\varepsilon$$
     since $\log Q \le Y^{\varepsilon/4}$!
   - The horizontal contour height term has size
     $$K_0 (\log Q) \cdot x \cdot \frac{Z}{\eta Q} = K_0 (\log Q)\,\frac{Y^{403K}}{Q}
     \le K_0\,Y^{404K}\,\exp(-Y^{\varepsilon/6}) \le \frac{1}{3} \le \frac{1}{3} Y^\varepsilon$$
     since $Q \ge \exp(Y^{\varepsilon/6})$ crushes every power of $Y$ (`tailK_exp`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:8`)!
   - The short interval $(Z, Z + \eta Z]$ has relative width $\eta = x^{-2}$, contributing
     $x \cdot O(\eta \log Z) = O(Y^{-K} \log Y) \le \frac{1}{3} Y^\varepsilon$.
   Since $y \le Y^K = x$, $\lvert y\,\mathrm{tailL}_\chi(Z) \rvert \le x\,\lvert \mathrm{tailL}_\chi(Z) \rvert \le Y^\varepsilon$.
2. For `kappa4`, set $s := (\log Q)^{1/4}$ and $x_0 := s^{10} = (\log Q)^{5/2}$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:10, 56`).
   Because $Q = \exp(s^4)$ grows superpolynomially in $s$, $(s^4)^{1006} \le Q$ for large $s$, so
   the exact same contour bound at $z_0 = x_0^{400} = (\log Q)^{1000}$ gives
   $\lvert \mathrm{tailL}_\chi(z_0) \rvert \le 2K_0 + 802$ (`kappa4_num`, `:9`). Adding Mertens's
   estimate $\sum_{n \le z_0} \Lambda(n)/n \le \log z_0 + C_M = 1000\log\log Q + C_M$ yields
   $$\Bigl\lvert \frac{L'}{L}(1, \chi) \Bigr\rvert \le 1000\log\log Q + C'$$
   (`kappa4_loglog`, `:44`). Substituting $\log Q \le A\,Y^{\varepsilon/5}(\log Y)^2$ gives
   $$1000\log\log Q + C' \le 200\varepsilon \log Y + 2000\log\log Y + 1000\log A + C'.$$
   Because $\varepsilon < 1/52$, we have $4 - 200\varepsilon > 4 - \frac{200}{52} = \frac{2}{13} > 0$,
   so for $Y$ large enough (`src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:133–153`), the right-hand side is $\le 4\log Y$.
3. For `box_of_S` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:28–60`), first `kappaC` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/kappaC.lean:10`) gives $\lVert \frac{L'}{L}(1,\chi) \rVert \le C\log Y$
   from `GoodC Q χ` and $\log Q \le Y^{\varepsilon/4}$. Next let $y \in [Y, Y^K]$ and
   $Z = (Y^K)^{400} \ge y$. Because $\chi(n) = \kappa(n)(\frac{n}{q})$ holds for **every**
   $n \in \mathbb N$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:46–50`, invoked for primitive $\psi_{r,q}$ of conductor $f_r q$
   where $\kappa_r(n) = \xi_r(n)$), the truncated character sum `Sz χ y Z` equals $S(Z, y, q, \kappa)$
   identically with zero bad-prime discrepancy, and `finite_splitting_of_group` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:45`)
   rewrites
   $$G_\chi(y) = -S(Z, y, q, \kappa) - y\,\mathrm{tailL}_\chi(Z).$$
   For $Y \ge 16$, $\varepsilon \le 1/4$, and $\tau > 0$, we have $Y^\varepsilon \le Y^{1/4}$ and
   $2 \le 16^{1/4} \le Y^{1/4}$, so $Y^\varepsilon \le \frac{1}{2} Y^{1/2} \le \frac{1}{2} y^{1/2 + \tau}$
   (`num_box`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:10`). By the triangle inequality and part 1 (`tailK`),
   $$\lVert G_\chi(y) \rVert \le \lVert S(Z, y, q, \kappa) \rVert + \lVert y\,\mathrm{tailL}_\chi(Z) \rVert
   \le \frac{1}{2} y^{1/2 + \tau} + Y^\varepsilon
   \le y^{1/2 + \tau}. \quad \square$$

### 4.4.4 Mean-square bounds over primes and the Sobolev–Markov uniformization (`meanSqK`, `twistK`, `bad_share`)

Next we bound $\sum_{q \in \mathrm{PPset}} \lVert S(Z, y, q, \kappa) \rVert^2$ at a single point $y$,
and then upgrade that pointwise $L^2$ bound to a **simultaneous uniform bound for all $y \in [Y, Y^K]$**!

**Proposition 4.5 ($L^2$ mean-square bound over primes with at most one Landau–Page modulus).**
*There exists an absolute constant $C_{\mathrm{m}} > 0$ such that for every $0 < \varepsilon \le 1$
and $K \ge 1$, there exists $Y_0$ such that for all $Y \ge Y_0$, whenever `admitted ε Y U m₀ a₀`
holds ($8 \mid m_0$, $\gcd(a_0, m_0) = 1$, $Y^{\varepsilon/6} \le \log U \le Y^{\varepsilon/5}(\log Y)^2$,
and $\frac{1}{4}(\log Y)^2 \log m_0 \le \log U$) and every prime $p \mid m_0$ satisfies either
$p \le Y^{\varepsilon/5}$ or $p > (Y^K)^{400}$, we have
`MeanSq C_{\mathrm{m}} ((Y^K)^400) (PPset m₀ a₀ U) (Set.Icc Y (Y^K))`: for every $y \in [Y, Y^K]$
and every $\kappa : \mathbb N \to \mathbb C$ with $\lVert \kappa(n) \rVert \le 1$,*
$$\sum_{q \in \mathrm{PPset}(m_0, a_0, U)} \bigl\lVert S\bigl((Y^K)^{400}, y, q, \kappa\bigr) \bigr\rVert^2
\le C_{\mathrm{m}}\,y\,\log y\,\bigl\lvert \mathrm{PPset}(m_0, a_0, U) \bigr\rvert.$$
*(Lean: `QH.twistK`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean:148`;
`QH.meanSqK`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean:51`; `QH.meanSq_abs`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean:8`; `meanSquareHypW_of_pnt`,
`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMain.lean:55`, using
`pnt_progressions_relative_weak_holds` [Lean] at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:22`, `excBound` [Lean] at
`src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:32`, and `page_across` [Lean, read]
at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPage.lean:37`, called at
`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwist.lean:26`; see Section 4.7.5.)* [Lean, read]

*Proof.* First (`meanSq_abs`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean:8–58`), setting $c_n(y) := \Lambda(n)\min(1, y/n) \ge 0$
and $Z := (Y^K)^{400}$, expanding the square and applying $\lvert \kappa(n_1)\overline{\kappa(n_2)} \rvert \le 1$ gives
$$\sum_{q \in \mathcal P} \bigl\lVert S(Z, y, q, \kappa) \bigr\rVert^2
= \sum_{1 \le n_1, n_2 \le \lfloor Z \rfloor} c_{n_1}(y) c_{n_2}(y)\,\kappa(n_1)\overline{\kappa(n_2)}
\sum_{q \in \mathcal P} \Bigl(\frac{n_1 n_2}{q}\Bigr)
\le \sum_{1 \le n_1, n_2 \le \lfloor Z \rfloor} c_{n_1}(y) c_{n_2}(y)
\Bigl\lvert \sum_{q \in \mathcal P} \Bigl(\frac{n_1 n_2}{q}\Bigr) \Bigr\rvert,$$
where $\mathcal P := \mathrm{PPset}(m_0, a_0, U)$. Notice why taking absolute values *outside* the
$q$-sum works cleanly: **the inner character sum $\sum_{q \in \mathcal P} (\frac{n_1 n_2}{q})$ no
longer depends on $\kappa$ at all!**

Now factor each product $n_1 n_2$ ($1 \le n_1, n_2 \le \lfloor Z \rfloor$) into its $m_0$-part and
its coprime squarefree core (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMain.lean:70–120`): write $n_1 n_2 = m' \cdot t^2 \cdot s$, where
every prime dividing $m'$ divides $m_0$ (remember $2 \mid m_0$, so $t^2 s$ is **odd**),
$\gcd(t s, m_0) = 1$, and $s \ge 1$ is odd, squarefree, and coprime to $m_0$, with
$$s \le n_1 n_2 \le Z^2 = Y^{800K}.$$
For every $q \in \mathcal P$, we have $q \equiv a_0 \pmod{m_0}$ (so $(\frac{m'}{q})$ is a fixed
sign $\pm 1$ determined by $a_0 \bmod m_0$, since $8 \mid m_0$ fixes $(\frac{2}{q})$ as well) and
$q > U^{1/2} \ge \exp(\frac{1}{2} Y^{\varepsilon/6}) \gg Y^{800K} \ge n_1 n_2$, so the
prime $q$ never divides $t$, making $(\frac{t^2}{q}) = 1$. Finally, since $s$ is odd and $8 \mid m_0$
fixes $q \bmod 4$, quadratic reciprocity turns $(\frac{s}{q})$ into $\pm (\frac{q}{s})$ with a sign
independent of $q \in \mathcal P$:
$$\Bigl\lvert \sum_{q \in \mathcal P} \Bigl(\frac{n_1 n_2}{q}\Bigr) \Bigr\rvert
= \Bigl\lvert \sum_{q \in \mathcal P} \Bigl(\frac{q}{s}\Bigr) \Bigr\rvert.$$

Now `twistK` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean:148–353`, invoked at exponent parameter $B = K + 1$ in `src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean:63`)
splits the odd squarefree moduli $s \le Z^2$ coprime to $m_0$ into three regimes:

1. **The off-diagonal non-exceptional moduli ($s > 1$, $s \neq n_*$).** As a function of $q$,
   $q \mapsto (\frac{q}{s})$ is a non-principal real primitive character of conductor $s$ or $4s$,
   still non-principal on the progression $q \equiv a_0 \pmod{m_0}$ because $\gcd(s, m_0) = 1$ and
   $8 \mid m_0$. By the classical Landau–Page theorem across moduli $\le 4 Z^2$ (`page_across`,
   `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPage.lean:37`, Lemma 4.16 [Lean, read]), among all real primitive characters of conductor $\le 4 Z^2$, **at
   most one** can violate the classical zero-free region. Hence there exists at most **one** odd
   squarefree integer $n_*$ such that for every $s \notin \{1, n_*\}$ ($s \le Z^2$, $\gcd(s, m_0) = 1$),
   the prime number theorem in progressions modulo $\operatorname{lcm}(m_0, 4s) \le 4 m_0 Z^2$ (note
   $\frac{1}{4}(\log Y)^2 \log m_0 \le \log U$ places $U$ inside the Siegel–Walfisz /
   Page-uniform range, with Siegel's bound `excBound` [Lean] guaranteeing $\lvert \mathcal P \rvert \ge U^{9/10}$)
   yields (`src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean:151`)
   $$\Bigl\lvert \sum_{q \in \mathcal P} \Bigl(\frac{q}{s}\Bigr) \Bigr\rvert
   \le Y^{-(K + 1)}\,\lvert \mathcal P \rvert.$$
   Since $\sum_{n \le Z} c_n(y) = \sum_{n \le y}\Lambda(n) + y\sum_{y < n \le Z}\frac{\Lambda(n)}{n} \ll y K\log Y$
   (`sum_cN_le`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean:58`), multiplying $(\sum_{n \le Z} c_n(y))^2 \ll y^2 K^2 (\log Y)^2$
   by $Y^{-(K + 1)}\lvert\mathcal P\rvert \le Y^{-1} y^{-1}\lvert\mathcal P\rvert$ contributes
   $\ll y\,(\log y)\,\lvert\mathcal P\rvert$.
2. **The diagonal ($s = 1$).** Recall $\Lambda(n)$ is supported on prime powers $p^a$. If
   $n_1 = p_1^{a_1}$ and $n_2 = p_2^{a_2}$ have coprime squarefree core $s = 1$, then either
   $p_1 = p_2$ (diagonal prime powers) or both $p_1, p_2$ divide $m_0$ (hence both are $\le Y^{\varepsilon/5}$
   since $n_1, n_2 \le Z = (Y^K)^{400}$). On true diagonal prime powers,
   $$\sum_{n \le Z} c_n(y)^2 = \sum_{n \le y} \Lambda(n)^2 + y^2\sum_{y < n \le Z} \frac{\Lambda(n)^2}{n^2}
   \sim y \log y + y^2 \cdot \frac{\log y}{y} = 2 y \log y,$$
   and primes dividing $m_0$ ($\le Y^{\varepsilon/5}$, handled in `src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean:45–48, 95–155`) also
   contribute $O(y \log y)\,\lvert\mathcal P\rvert$.
3. **The single Landau–Page modulus ($s = n_* > 1$).** If $n_1 = p_1^{a_1}$ and $n_2 = p_2^{a_2}$
   have squarefree odd core $s(n_1 n_2) = n_* > 1$, then since $n_*$ is squarefree and $> 1$ while
   $n_1, n_2$ are prime powers, $n_*$ can have **at most two prime factors**: either $n_* = p$ is
   prime or $n_* = p_1 p_2$ is a semiprime with $\{p_1, p_2\}$ fixed by $n_*$ (`abs_pair_sum_eq`,
   `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMain.lean:38`). Thus $n_*$ contributes at most $O(y \log y)\,\lvert\mathcal P\rvert$ as well.

Combining the five partial constants into $C_{\mathrm{m}} := C_3 + 25 C_1^2 + 4 C_2^2 + 20 C_1 C_2 + C_4^2$
(`src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean:59`) gives $\sum_{q \in \mathcal P} \lVert S(Z, y, q, \kappa) \rVert^2 \le C_{\mathrm{m}}\,y\log y\,\lvert\mathcal P\rvert$. $\square$

How do we pass from a bound **at each fixed $y$** to a bound **simultaneously for all uncountably
many $y \in [Y, X]$** without losing a factor of $Y$? Look at the archive's `bad_share`
(`src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean:1–318`), which we read in full (`R3`) — it is a textbook one-dimensional Sobolev
embedding ($W^{1,2} \hookrightarrow L^\infty$) on dyadic intervals!

**Lemma 4.6 (Dyadic Sobolev–Markov uniformization: `QH.bad_share`).** *Let $C \ge 0$, $\tau > 0$,
and $\eta > 0$. There exists $Y_0 \ge 2$ (chosen so that
$\frac{32 C}{\tau}\,Y^{-\tau}\,(1 - 2^{-\tau})^{-1} \le \eta$ for all $Y \ge Y_0$) such that for
every $Y \ge Y_0$, every $X, Z \in \mathbb R$, every finite prime set $P$, and every
$\kappa : \mathbb N \to \mathbb C$ with $\lVert \kappa(n) \rVert \le 1$, if `MeanSq C Z P (Set.Icc Y X)`
holds, then every subset $B \subseteq P$ satisfying*
$$\forall q \in B,\ \exists y \in [Y, X],\ \frac{1}{2}\,y^{1/2 + \tau} < \bigl\lVert S(Z, y, q, \kappa) \bigr\rVert$$
*has cardinality $\lvert B \rvert \le \eta\,\lvert P \rvert$.*
*(Lean: `QH.bad_share`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean:251`.)* [Lean, read]

*Proof.* Write $S_q(y) := S(Z, y, q, \kappa) = \sum_{1 \le m \le \lfloor Z \rfloor} c_m(y)\kappa(m)(\frac{m}{q})$,
where $c_m(y) = \Lambda(m)\min(1, y/m)$ equals $\Lambda(m)$ for $m \le y$ and $\Lambda(m)\frac{y}{m}$
for $m > y$. Differentiating $y \mapsto \min(1, y/m)$ from the right (`bs_hasDeriv_min`,
`src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean:48`):
- for $m \le y$, $\min(1, y/m) = 1$ is **constant** on $[y, \infty)$, so its right-derivative is $0$;
- for $y < m$, $\min(1, y/m) = \frac{y}{m}$ has derivative $+\frac{1}{m}$, so $c_m'(y) = +\frac{\Lambda(m)}{m} = \frac{1}{y}\,c_m(y)$!
Therefore $S_q(y)$ is continuous and piecewise linear with right-derivative $D_q(y) := \mathrm{bsD}(Z, y, q, \kappa)$
satisfying (`bs_S_sub_S` and `bs_mul_D_eq_S`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean:76, 83`)
$$S_q(b) - S_q(a) = \int_a^b D_q(v)\,dv
\qquad\text{and}\qquad
y\,D_q(y) = S\bigl(Z, y, q, \mathbf{1}_{y < m}\,\kappa\bigr)!$$
Pause to appreciate that identity (`bs_mul_D_eq_S`, `:83`): **$y\,D_q(y)$ is itself an instance of
$S(Z, y, q, \kappa_{>y})$** for the truncated weight $\kappa_{>y}(m) := \mathbf{1}_{y < m}\,\kappa(m)$,
which still satisfies $\lVert \kappa_{>y}(m) \rVert \le 1$! Hence `MeanSq` on $[Y, X]$ gives at
every $v \in [Y, X]$ (`bs_sum_D_le`, `:146`):
$$\sum_{q \in P} \lVert S_q(v) \rVert^2 \le C\,v\log v\,\lvert P \rvert,
\qquad
\sum_{q \in P} \lVert D_q(v) \rVert^2 = \frac{1}{v^2}\sum_{q \in P} \lVert v\,D_q(v) \rVert^2
\le C\,\frac{\log v}{v}\,\lvert P \rvert!$$

Now consider a single truncated dyadic block $[a, W] \subseteq [Y, X]$ with $2 \le a \le W \le 2a$.
For any $q \in P$ and any witness point $w(q) \in [a, W]$, Cauchy–Schwarz gives (`bs_normSq_S_le`,
`:118`):
$$\lVert S_q(w(q)) \rVert^2
\le 2\lVert S_q(a) \rVert^2 + 2\Bigl(\int_a^{w(q)} \lVert D_q(v) \rVert\,dv\Bigr)^2
\le 2\lVert S_q(a) \rVert^2 + 2a \int_a^W \lVert D_q(v) \rVert^2\,dv.$$
Summing over $q \in P$ and exchanging $\sum_{q \in P}$ with $\int_a^W$ (`bs_block`, `:163`) yields
$$\sum_{q \in P} \lVert S_q(w(q)) \rVert^2
\le 2 C\,a\log a\,\lvert P \rvert + 2a\int_a^W C\,\frac{\log(2a)}{a}\,\lvert P \rvert\,dv
\le 4 C\,a\log(2a)\,\lvert P \rvert!$$
Look at that: **choosing a worst-case point $w(q) \in [a, W]$ separately for every prime $q$ cost
only a factor of $4$!** If $B_a \subseteq P$ consists of primes $q$ with a bad witness
$w(q) \in [a, W]$ satisfying $\lVert S_q(w(q)) \rVert > \frac{1}{2} w(q)^{1/2 + \tau} \ge \frac{1}{2} a^{1/2 + \tau}$,
then using $\log(2a) \le \frac{2}{\tau} a^\tau$ for $a \ge 2$, Markov's inequality (`bs_markov`,
`:207`) gives
$$\lvert B_a \rvert \cdot \frac{1}{4}\,a^{1 + 2\tau}
\le 4 C\,a\log(2a)\,\lvert P \rvert
\le \frac{8 C}{\tau}\,a^{1 + \tau}\,\lvert P \rvert
\implies \lvert B_a \rvert \le \frac{32 C}{\tau}\,a^{-\tau}\,\lvert P \rvert.$$
Finally, partition $B$ according to the unique dyadic index $i \ge 0$ for which the bad point
$y \in [Y, X]$ satisfies $2^i Y \le y < 2^{i+1} Y$, and apply `bs_markov` on $[a_i, \min(2 a_i, X)]$
with $a_i = 2^i Y$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean:269–318`). Since $a_i^{-\tau} = Y^{-\tau}\,(2^{-\tau})^i$ and
$r := 2^{-\tau} \in (0, 1)$, summing the geometric series $\sum_i r^i \le (1 - r)^{-1}$ yields
$$\lvert B \rvert \le \frac{32 C}{\tau}\,Y^{-\tau}\,(1 - 2^{-\tau})^{-1}\,\lvert P \rvert \le \eta\,\lvert P \rvert. \quad \square$$

### 4.4.5 Assembling the two-stage sieve (`stage` and `pairEx`)

Combining Lemmas 4.3, 4.4, 4.5, and 4.6 immediately proves the single-stage sieve `QH.stage` and
then the two-stage prime-pair existence theorem `PairEx`.

**Theorem 4.7 (Single-stage and two-stage prime sieve: `QH.stage` and `PairEx`).**

1. **Single-stage sieve (`QH.stage`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:41`).**
   *There exists an absolute constant $C > 0$ such that for every $0 < \varepsilon \le 1/4$,
   $\tau > 0$, $K \ge 1$, $\eta > 0$, and $R \in \mathbb N$, there exists $Y_0$ such that for every
   $Y \ge Y_0$, whenever `admitted ε Y U m₀ a₀` holds, every prime $p \mid m_0$ is either
   $\le Y^{\varepsilon/5}$ or $> (Y^K)^{400}$, $1 \le F \le U^{1/2}$, and $\Xi$ is a set of at most
   $R$ primitive characters $\xi \bmod f_\xi$ with $f_\xi \le F$, the set $\mathcal P := \mathrm{PPset}(m_0, a_0, U)$
   is nonempty and every subset $B \subseteq \mathcal P$ of primes $q$ failing
   `BoxAll (F * U) C τ Y (Y^K) (ξ · J q) M` for some $\xi \in \Xi$ and $M \neq 0$ satisfies
   $\lvert B \rvert \le \eta\,\lvert \mathcal P \rvert$.* [Lean, read]
2. **Two-stage existence (`QH.pairEx` / `PairEx`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112`).**
   *`PairEx` holds: for every $M \ge 1$, every $0 < \varepsilon < 1/52$, and every $A \ge 1$, there
   exists $Y_1$ such that for all $Y \ge Y_1$, there exist primes $(q, d)$ satisfying
   `PairGood M eps Y (Y^A) q d`.* [Lean, read]

*Proof.*

1. Set $Q := F U$. Because $1 \le F \le U^{1/2}$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:44`), we have $U \le Q \le U^{3/2}$,
   so $Y^{\varepsilon/6} \le \log U \le \log Q \le \frac{3}{2}\log U \le \frac{3}{2} Y^{\varepsilon/5}(\log Y)^2 \le Y^{\varepsilon/4}$
   for large $Y$ (`stage_log`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:16`). Every bad $q \in B \subseteq \mathcal P$ either
   lies in the zero-box failure set $B_1$ (where the primitive twist $\psi_{\xi, q}$ of conductor
   $f_\xi q \le F U = Q$ fails `ZeroFreeBox (F * U)`) or satisfies `GoodC (F * U) ψ_{ξ,q}` for all
   $\xi \in \Xi$ while failing $\sup_{y \in [Y, Y^K]} y^{-1/2 - \tau}\lVert S((Y^K)^{400}, y, q, \xi) \rVert \le \frac{1}{2}$
   for some $\xi \in \Xi$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:100–160`, by Lemma 4.4(3), `box_of_S`).
   - For $B_1$: Lemma 4.3 (`count_bad`) gives $\lvert B_1 \rvert \le \lvert C_b \rvert\,(FU)^{1/4} \le \lvert C_b \rvert\,U^{3/8}$,
     while `count_a` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean:346`, fed by
     `pnt_progressions_relative_weak_holds` at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:22` and `excBound`; Statement 4.17 [Lean]) gives $\lvert \mathcal P \rvert \ge U^{9/10}$
     (which also proves $\mathcal P$ is nonempty!). Since $\frac{3}{8} + \frac{21}{40} = \frac{9}{10}$,
     $\lvert C_b \rvert U^{3/8} \le \frac{\eta}{2} U^{9/10} \le \frac{\eta}{2}\lvert \mathcal P \rvert$
     for large $U$ (`stage_pow`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:29`).
   - For $B \setminus B_1$: Proposition 4.5 (`meanSqK`) supplies `MeanSq C_{\mathrm{m}} ((Y^K)^400) P (Set.Icc Y (Y^K))`,
     so Lemma 4.6 (`bad_share` at share $\frac{\eta}{2(R + 1)}$) gives at most $\frac{\eta}{2(R+1)}\lvert\mathcal P\rvert$
     bad primes for each $\xi \in \Xi$. Summing over the $\le R$ characters $\xi \in \Xi$ gives
     $\lvert B \setminus B_1 \rvert \le \frac{\eta}{2}\lvert\mathcal P\rvert$.
   Hence $\lvert B \rvert \le (\frac{\eta}{2} + \frac{\eta}{2})\lvert\mathcal P\rvert = \eta\,\lvert\mathcal P\rvert$.
2. Now fix $M \ge 1$, $0 < \varepsilon < 1/52$, and $A \ge 1$, and set $z := Y^{\varepsilon/5}$ and
   $z' := Y^{\varepsilon/5}(\log Y)^2$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112–169`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean:9`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairShare.lean:26`).
   In `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean:15`, `pair_share` invokes `QH.stage` in both stages with bad-share threshold
   $\eta = 1/2$ (and $\tau = \varepsilon / 2$ in `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:120`):
   - **Stage 1 (`stage1`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/Stage1Succ.lean:36`):** Apply `QH.stage` ($\eta = 1/2$) to
     $\mathcal P_1 := \mathrm{PPset}(8, 3, \exp(z))$, twisting primitive characters dividing $8M$
     ($N_0 = 8M$, conductor $F = 8M \le \exp(z/2)$ for large $Y$). Note $\log m_0 = \log 8$,
     so $\frac{1}{4}(\log Y)^2 \log 8 \ll Y^{\varepsilon/5} = z$ holds trivially. Because
     $\lvert \mathcal P_1 \rvert > 0$ and at most $\frac{1}{2}\lvert\mathcal P_1\rvert$ primes are
     bad, at least $\frac{1}{2}\lvert\mathcal P_1\rvert > 0$ primes $q \in \mathcal P_1$ satisfy
     `GoodQ (8*M)` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean:29–34`). Pick one such prime $q \equiv 3 \pmod 8$ with
     $\frac{1}{2} z < \log q \le z$ and $8M < q$ (so $\gcd(M, q) = 1$).
   - **Stage 2 (`stage2`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/CharOf.lean:61`):** With $q$ fixed, let
     $\mathrm{oddM}(z, q) := q \cdot \prod_{2 < p \le z,\,p\text{ prime}} p$ (`src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:53`).
     By the Chebyshev primorial bound $\sum_{2 < p \le z} \log p \le 2z$ (`PrimorialBound`), the Stage 2
     progression modulus $m_0 := 16 \cdot \mathrm{oddM}(z, q)$ satisfies
     $$\log m_0 = \log 16 + \log q + \sum_{2 < p \le z} \log p \le \log 16 + z + 2z \le 4z = 4\,Y^{\varepsilon/5},$$
     and every prime dividing $m_0$ is either $\le z = Y^{\varepsilon/5}$ or equal to $q$ (with
     $q > \exp(z/2) > (Y^A)^{400}$ for large $Y$). By the Chinese remainder theorem, since $16$ and
     $\mathrm{oddM}(z, q)$ are coprime, there is a residue class $a_0 \bmod m_0$ with
     $\gcd(a_0, m_0) = 1$ defined by
     $$a_0 \equiv 7 \pmod{16} \qquad\text{and}\qquad a_0 \equiv -1 \pmod{\mathrm{oddM}(z, q)}$$
     (`src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:45`). Any prime $d \in \mathcal P_2 := \mathrm{PPset}(m_0, a_0, \exp(z'))$
     automatically satisfies $d \equiv 7 \pmod{16}$, $q \mid d + 1$, $p \mid d + 1$ for all odd
     primes $p \le z = Y^{\varepsilon/5}$, and $\frac{1}{2}z' < \log d \le z'$ — so **`WinPair eps Y q d`
     holds for every $d \in \mathcal P_2$**. Moreover, Stage 2 calls `QH.stage` at
     $\varepsilon' := \frac{6}{5}\varepsilon < \frac{6}{5}\cdot\frac{1}{52} < \frac{1}{4}$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/CharOf.lean:71`)
     on $\log U = z' = z(\log Y)^2 \ge \frac{1}{4}(\log Y)^2 \log m_0$. Twisting primitive characters
     of $\xi \cdot (\frac{\cdot}{q})^i$ ($i \in \{0, 1\}$, conductor $\le 8Mq \le 8M e^z \le e^{z'/2}$)
     by $(\frac{\cdot}{d})$ at $\eta = 1/2$ leaves at least $\frac{1}{2}\lvert \mathcal P_2 \rvert > 0$
     primes $d \in \mathcal P_2$ satisfying `GoodD (8*M)` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/PairShare.lean:26`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean:9`).
     Note finally that `GoodQ (8*M)` and `GoodD (8*M)` give `ZeroFreeBox Q` precisely up to
     $Q = 8M e^z = \mathrm{height}(M, \varepsilon, Y, 0)$ when $j = 0$ and
     $Q = 8M e^{z + z'} = \mathrm{height}(M, \varepsilon, Y, 1)$ when $j = 1$ (`pairEx_box`,
     `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:17`), while `kappa4` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:117, 162`) upgrades $\lVert L'/L(1,\chi) \rVert$
     to $4\log Y \le 4\log y$ on $[Y, Y^A]$, completing `PairEx`. $\square$

#### 4.4.5.1 Why coprime twists stay primitive

**Motivation.** In the proof of [the two-stage sieve](#445-assembling-the-two-stage-sieve-stage-and-pairex), the zero-density count ranges over primitive characters. A pointwise formula for a twist gives a character at the advertised level, but leaves open which primitive character the count should use. If the starting character is primitive of conductor $f$ and an odd prime $q$ is coprime to $f$, the sieve needs the exact new conductor $fq$. Stage 2 also needs to know the conductor of the character obtained in Stage 1 before it starts twisting by $d$. The [Siegel product](#41025-the-siegel-lower-bound-from-biquadratic-product-series) uses level change to construct a product and then studies its Dirichlet coefficients. Here the issue is whether two characters multiplied at a common level can lose conductor.

**Two hand calculations [Expository].** A useful way to rule out a divisor $e$ of a level $N$ is to find two units modulo $N$ that agree modulo $e$ but have different character values. We use this test before proving the general result.

*Moduli $3$ and $5$.* Let $\chi_3$ and $\chi_5$ be the Legendre characters. The nonzero squares are $1$ modulo $3$ and $1,4$ modulo $5$, as is seen by squaring the units of each prime field. The value lists starting at residue $0$ are $(0,1,-1)$ and $(0,1,-1,-1,1)$. The units $1,2$ differ in value for each character. Since the levels are prime, their only proper divisor is $1$, which identifies those units. The two conductors are therefore $3$ and $5$.

Multiply the lists by reducing each residue modulo $3$ and $5$. The table includes the two original values even at nonunits of the product level.

| Residue modulo $15$ | $0$ | $1$ | $2$ | $3$ | $4$ | $5$ | $6$ | $7$ | $8$ | $9$ | $10$ | $11$ | $12$ | $13$ | $14$ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $\chi_3$ | 0 | 1 | −1 | 0 | 1 | −1 | 0 | 1 | −1 | 0 | 1 | −1 | 0 | 1 | −1 |
| $\chi_5$ | 0 | 1 | −1 | −1 | 1 | 0 | 1 | −1 | −1 | 1 | 0 | 1 | −1 | −1 | 1 |
| Product | 0 | 1 | 1 | 0 | 1 | 0 | 0 | −1 | 1 | 0 | 0 | −1 | 0 | −1 | −1 |

The units $1,7$ exclude $3$, and $1,11$ exclude $5$. Either pair excludes $1$. The conductor divides $15$, so it is $15$.

*Moduli $8$ and $3$.* The units modulo $8$ are generated by $3$ and $5$. Both square to $1$, and $3\cdot5\equiv7\pmod 8$. Send both generators to $-1$. This gives the character $\chi_8$ with values $(0,1,0,-1,0,-1,0,1)$ in residue order. Its values at $1$ and $5$ rule out factoring through $4$ and hence also through $2$ or $1$. Its conductor is $8$. Multiply by $\chi_3$ using the same reductions.

| Residue modulo $24$ | $0$ | $1$ | $2$ | $3$ | $4$ | $5$ | $6$ | $7$ | $8$ | $9$ | $10$ | $11$ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $\chi_8$ | 0 | 1 | 0 | −1 | 0 | −1 | 0 | 1 | 0 | 1 | 0 | −1 |
| $\chi_3$ | 0 | 1 | −1 | 0 | 1 | −1 | 0 | 1 | −1 | 0 | 1 | −1 |
| Product | 0 | 1 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | 0 | 0 | 1 |

| Residue modulo $24$ | $12$ | $13$ | $14$ | $15$ | $16$ | $17$ | $18$ | $19$ | $20$ | $21$ | $22$ | $23$ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $\chi_8$ | 0 | −1 | 0 | 1 | 0 | 1 | 0 | −1 | 0 | −1 | 0 | 1 |
| $\chi_3$ | 0 | 1 | −1 | 0 | 1 | −1 | 0 | 1 | −1 | 0 | 1 | −1 |
| Product | 0 | −1 | 0 | 0 | 0 | −1 | 0 | −1 | 0 | 0 | 0 | −1 |

Every proper divisor of $24$ divides one of $8$ and $12$. The units $1,17$ exclude $8$, and $1,13$ exclude $12$. Both pairs have product values $1,-1$. This rules out every proper divisor and gives conductor $24$.

**Definitions.** Write $U_N=(\mathbb Z/N\mathbb Z)^\times$ for $N>0$. We use the [conductor convention of §2.3.1](02-functional-equations-and-primitive-characters.md#231-conductors-level-change-and-bundled-primitive-characters). A character is a homomorphism $U_N\to\mathbb C^\times$, extended by zero on nonunits. For $e\mid N$, $\operatorname{lift}_{e,N}$ is pullback on units along reduction followed by this zero extension. Thus equality of two lifts at $N$ can be tested on $U_N$. The conductor is the least inducing divisor, and the Chapter 2 divisibility criterion says that a character of conductor $c$ factors through a divisor $e$ of $N$ exactly when $c\mid e$. A primitive character has conductor equal to its level. At level $1$, the trivial unit group gives the character with value $1$ on every integer, including $0$.

**Three conductor rules [Lean, read].** For characters $A,B$ at the same positive level, and a lift between positive levels, we have

$$
\begin{aligned}
\operatorname{cond}(\operatorname{lift}_{e,N}\chi)&=\operatorname{cond}(\chi),\\
\operatorname{cond}(AB)&\mid\operatorname{lcm}(\operatorname{cond}(A),\operatorname{cond}(B)),\\
\operatorname{cond}(A^{-1})&=\operatorname{cond}(A).
\end{aligned}
$$

*Proof.* Let $c=\operatorname{cond}(\chi)$ and let $c'$ be the conductor of its lift from $e$ to $N$. Lifting the inducing character of level $c$ in two steps shows $c'\mid c$. In particular $c'\mid e$. Lift the inducing character of the upper level first to $e$. Its further lift to $N$ is the lift of $\chi$. Surjectivity of $U_N\to U_e$ makes pullback injective, so this character at $e$ equals $\chi$, proving $c\mid c'$. This is the two-divisibility proof of Mathlib's `conductor_changeLevel`.

For the product let $L$ be the least common multiple of the two conductors. Lift the inducing characters to $L$, multiply there, and lift to $N$. Pullback preserves multiplication, so this induces $AB$ and the divisibility criterion applies. Finally, lifting commutes with the group inverse, which takes reciprocals on units and extends by zero. Thus $\operatorname{cond}(A^{-1})\mid\operatorname{cond}(A)$. Applying the same argument to $A^{-1}$ gives the reverse divisibility. Mathlib proves this first for integral powers and uses exponent $-1$. $\square$

**Theorem (coprime primitive product) [Lean, read].** Let $m,n$ be coprime positive integers. If $\chi_1$ modulo $m$ and $\chi_2$ modulo $n$ are primitive, then

$$
\operatorname{cond}\bigl(\operatorname{lift}_{m,mn}\chi_1\cdot
             \operatorname{lift}_{n,mn}\chi_2\bigr)=mn.
$$

On every integer $a$, the product evaluates to $\chi_1(a)\chi_2(a)$ using the original zero-extended characters. On units modulo $mn$ this is pullback in each coordinate. Off the units, a prime dividing $mn$ divides $a$, so at least one of the original character values is already zero.

*Proof.* Put $A=\operatorname{lift}_{m,mn}\chi_1$, $B=\operatorname{lift}_{n,mn}\chi_2$, and $C=\operatorname{cond}(AB)$. The first rule gives $\operatorname{cond}(A)=m$ and $\operatorname{cond}(B)=n$. Recover $A=(AB)B^{-1}$ and $B=(AB)A^{-1}$ in the character group. The second and third rules give

$$
m\mid\operatorname{lcm}(C,n)\mid Cn,\qquad
n\mid\operatorname{lcm}(C,m)\mid Cm.
$$

Since $\gcd(m,n)=1$, the first chain implies $m\mid C$ and the second implies $n\mid C$. Coprimality then gives $mn\mid C$. Since $C$ divides the level $mn$, equality follows. The equalities with inverse characters take place in the character group, whose identity has value $0$ off the units. This proof is the argument of the private lemma `prim_mul`. $\square$

**Corollary (odd-prime twists and the dyadic base) [Lean, read].** Let $\xi$ be primitive modulo $f>0$ and $q$ an odd prime with $q\nmid f$. The function $\psi(a)=\xi(a)(\frac{a}{q})$ is a primitive nonprincipal character of conductor $fq$. If $\xi^2=1$ as a character, then $\psi^2=1$ as well. The character $\chi_8$ in the second example is the archive's dyadic base, with conductor $8$ and square equal to the principal character modulo $8$. In particular its twist by $q$ has conductor $8q$ and square equal to the principal character at $8q$.

*Proof.* On $U_q$ the squaring homomorphism has kernel $\{1,-1\}$, so its image has index two. The Legendre character is the sign on the two cosets and takes $-1$ on the nonsquares. At the prime level $q$ the only possible conductors are $1$ and $q$. A character of conductor $1$ is principal, so the Legendre character has conductor $q$. Its square equals the level-$q$ principal character by the values on units. The coprime product theorem now gives conductor $fq>1$, which proves nonprincipality even for $f=1$. Products and lifts preserve the asserted square identity. For $\chi_8$, the values at $1$ and $5$ supply the conductor obstruction used by the archive. Its square follows from its unit values. $\square$

**Remarks and the two-stage sieve.** At $q=2$, the multiplicative group of the prime field has just one element, so its quadratic character is principal and has conductor $1$. For odd $f$, twisting by that character merely raises the level to $2f$, leaving the conductor $f$ and forcing zeros at the even integers. If $q$ divides $f$, shared conductor factors may cancel. For a strict example, both factors $\chi_3,\chi_3$ are primitive of conductor $3$, but their product at the common level $3$ is $(0,1,1)$ in residue order. It equals the lift of the level-$1$ character, since its unit values are all $1$ and its value at the nonunit is $0$. Its conductor is exactly $1$. Lifting both factors to level $9$ before multiplying gives the principal character modulo $9$, again of conductor $1$.

In `QH.twist_prim`, $J(q,a)$ denotes the complex cast of the Jacobi symbol, which agrees with the Legendre symbol at the prime $q$. The wrapper obtains primitivity and nonprincipality from `TwPrimitive`. Its second direct supplier, `twist_evaluation_formula`, verifies the pointwise formula on units by reduction and handles nonunits by splitting according to whether $a$ is coprime to $f$. The separate dyadic branch and square assertion are part of `TwPrimitive`.

In [Stage 1 and Stage 2](#445-assembling-the-two-stage-sieve-stage-and-pairex), `QH.stage` has $f\le F\le U^{1/2}<q\le U$ and takes $U$ large enough to exclude $2$. The primitive twist has conductor $fq\le FU$. A box failure for this character can therefore enter the primitive-character count. When the box and the short-sum bound both hold, the stage uses the nonprincipal clause and the evaluation formula in its analytic transfer, and uses `ind_unique` to identify the primitive character named by the box interface. Stage 1 first replaces the characters at level $N_0=8M$ by their primitive inducing characters of conductor $f\mid N_0$.

Stage 2 starts with the same base level and the already chosen $q>N_0$. For exponent $i=0$, `char_of` keeps the primitive character of conductor $f$. For $i=1$, it produces the primitive twist of conductor $fq$. Agreement with the original level-$N_0$ character is used on integers coprime to $N_0$, where removing the extra zero extension is valid. These two families fit the Stage 2 budget $F=N_0e^z$ because $q\le e^z$. The same stage argument then twists them by $d>F$. An exponent $j=1$ thus yields conductor $fq^i d$. When $j=0$, the `ind_drop` call in `pairEx_box` identifies the $q$-twist from agreement at the auxiliary level and lets the proof reuse Stage 1. This explains where exact conductors and agreement on common units enter the sieve.

The classical inputs are unit-group pullback, conductor divisibility and quadratic characters of prime fields. Roberts gives the classical coprime product theorem by separating the two unit-group coordinates. [Roberts, *Theta Series*, Lemma 1.1.5](https://www.brooksroberts.org/theta_series.pdf#page=9)

For the classical induction convention see the [DLMF, §27.8](https://dlmf.nist.gov/27.8) and [Kedlaya, *Notes on analytic number theory*, Definition 3.3](https://kskedlaya.org/ant/chap-lfunc.html#chap-lfunc-3-4). For the precise local reading scope and the remaining named inputs, see the [declaration and consumer register](../sources/SOURCES.md#chapter-4-coprime-twist-conductors).

### 4.4.6 Window rescaling (`winPairs`) and assembling the host supply (`supplyChi`)

With `PairEx` proved unconditionally, two short, fully read (`R3`) glue theorems connect `PairEx`
and `VWin` (`VWinAt ψ 401`) to the exact `HostExW (3 / 2)` window-supply hypothesis used by
`zeroFreeAll_of_topG` in Chapter 3 (Theorem 3.7)!

**Proposition 4.8 (Rescaling quadratic `VWinAt ψ 401` windows to $Z^{3/2}$ windows: `winPairs`).**
*Let $\psi \in \mathrm{PChar}$, $0 < \varepsilon < 1/52$, and $c \ge 1$. Assume `VWinAt ψ 401` and
`PairEx`. Then there exists $J \ge 1$ such that for every real threshold $y$, there exists $Z \ge y$
such that for every $x \in [Z, Z^{3/2}]$, there exist $Y \in \mathbb R$ and $q, d, e \in \mathbb N$
satisfying `WinDatum ψ eps J c x Y q d e` (`src/Development/AutomorphicArithmetic/CharacterBoxes/TwistForm.lean:19`), namely:*

1. $x^{1/J} \le Y \le x$ *and* `PairGood ψ.N eps Y x q d`;
2. $x^{2 + 8\varepsilon} \le c \cdot 2^e \le 2\,x^{2 + 8\varepsilon}$; *and*
3. *for every number field $E$ satisfying `IsChiField ψ e q d E`, we have
   `VVle E ⌊x^400⌋₊ (sqrt (exp (x^eps)))` (note $\sqrt{\exp(x^\varepsilon)} = \exp(x^\varepsilon / 2)$).*
*(Lean: `UpperTheory.Top.winPairs`, `src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean:5`.)* [Lean, read]

*Proof.* First choose $e : \mathbb R \to \mathbb N$ satisfying `PageN eps e` by Lemma 4.1(1).
Applying `VWinAt ψ 401` to $(\varepsilon, e)$ gives $J \ge 1$ and $X_0$, and applying `PairEx` to
$(\psi.N, \varepsilon, J)$ gives $Y_1$ (`src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean:10–13`). Define the rescaling factor
$$k := c^{1/(2 + 8\varepsilon)} \ge 1, \qquad\text{so}\quad k^{2 + 8\varepsilon} = c.$$
Given any threshold $y \in \mathbb R$, set $M := \max(1, y, Y_1, k^3, k^{400})$ and
$X := \max(X_0, M^J)$, and define $Y := X^{1/J} \ge M \ge Y_1$ (`:23–34`). By `PairEx` at $Y$,
there exist $(q, d)$ satisfying `PairGood ψ.N eps Y (Y^J) q d`, where $Y^J = X$; in particular
`WinPair eps (X^{1/J}) q d` holds. Feeding $(X, q, d)$ into `VWinAt ψ 401` produces $W \in [Y, X]$
such that `VAt ψ 401 eps x' (e x') q d` holds for every $x' \in [W, W^2] \subseteq [Y, X]$ (`:35`).

Now set $Z := kW \ge W \ge M \ge y$. Let $x \in [Z, Z^{3/2}]$, and set $x' := x / k$, so $x = k x'$
and $x' \ge W \ge M \ge 1$. Check all three conclusions (`:40–81`):

- Since $k^3 \le M \le W$, we have $(kW)^3 = k^3 W^3 \le W \cdot W^3 = W^4$; taking square roots gives
  $$Z^{3/2} = (kW)^{3/2} \le W^2!$$
  Hence $W \le x' \le k x' = x \le Z^{3/2} \le W^2 \le X = Y^J$. Because $Y \le W \le x \le Y^J$,
  we get $x^{1/J} \le Y \le x$, and shrinking the upper endpoint of `PairGood` from $Y^J$ to $x$
  (`PairGood.mono`, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:41`) gives `PairGood ψ.N eps Y x q d`.
- Applying `PageN` at $x' \ge 1$ gives $(x')^{2+8\varepsilon} \le 2^{e(x')} \le 2(x')^{2+8\varepsilon}$;
  multiplying by $c = k^{2+8\varepsilon}$ gives $x^{2+8\varepsilon} \le c \cdot 2^{e(x')} \le 2\,x^{2+8\varepsilon}$.
- Because $x' \in [W, W^2]$, `VAt ψ 401` gives `VVle E ⌊(x')^401⌋₊ (exp((x')^eps / 2))` for every $E$
  satisfying `IsChiField ψ (e x') q d E`. Since $k^{400} \le M \le W \le x'$ and $1 \le k$,
  $$x^{400} = k^{400}(x')^{400} \le x' \cdot (x')^{400} = (x')^{401}
  \qquad\text{and}\qquad
  \exp\bigl((x')^\varepsilon / 2\bigr) \le \exp(x^\varepsilon / 2) = \sqrt{\exp(x^\varepsilon)}.$$
  Monotonicity of `VVle` in both arguments (`VVle.mono`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:51`) gives
  `VVle E ⌊x^400⌋₊ (sqrt (exp (x^eps)))`. $\square$

**Theorem 4.9 (Host supply on $Z^{3/2}$ windows: `supplyChi`).** *Assume `VWin` and `PairEx`. Then
for every primitive character $\psi \in \mathrm{PChar}$, there exists a window host supply at
exponent $\lambda = 3/2$:*
$$\mathrm{HostExW}\ \frac{3}{2}\ \Bigl(\text{producing }(s, R, H)\text{ with }\mathrm{EAtH}(\mathrm{Level.cyc}\,\psi, H.\mathrm{toHostRaw}, H.TT, s.x, s.\varepsilon, 4)\ \land\ \mathrm{VVle}\,H.E\,R.t\,\sqrt{s.b}\Bigr).$$
*(Lean: `UpperTheory.Top.supplyChi`, `src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean:8`,
via `fieldChi` (`src/Development/AutomorphicArithmetic/CharacterBoxes/FieldChi.lean:20`), `supplyOfAdmOf` (`src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:13`),
`eventually_rank_le_rpow_of_lt_one_div_fiftytwo` (`src/Development/AutomorphicArithmetic/CharacterBoxes/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5`),
and the imported short-norm coset theorem `hostOfField` [Lean] (`src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8`)
and admissible-rank existence `admissible_ranks_of_CMDatum` [Lean] (`src/Development/AutomorphicArithmetic/CoprimeRanks/AdmChi.lean:11`).)* [Lean, read]

*Proof.* Fix $\psi \in \mathrm{PChar}$ and $0 < \varepsilon < 1/52$. First, `fieldChi ψ`
(`src/Development/AutomorphicArithmetic/CharacterBoxes/FieldChi.lean:20`) fixes the constant factor $c \ge 1$ and threshold $e_0$ such that for any
$e \ge e_0$ and any $(q, d)$ obeying `HostHyp q d`, $q \neq 3$, $\gcd(\psi.N, qd) = 1$, and
$(\frac{-d}{p}) = 1$ for odd primes $p \le b$ ($b \ge 4\psi.N$), there exists a host field
`H0 : HostAx φ` with $\varphi.e = e$, $\varphi.\mathrm{ord} = c \cdot 2^e$, $\varphi.o = (\mathrm{Level.cyc}\,\psi).o$,
`KeptInXp`, `ExceptionalCharacterKept`, `KerChi ψ H0`, and `TwistForm ψ H0`.

Second, Proposition 4.8 (`winPairs`) supplies windows $[Z, Z^{3/2}]$ on which every $x \in [Z, Z^{3/2}]$
has `WinDatum ψ eps J c x Y q d e` (`src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:58–80`). At each $x \in [Z, Z^{3/2}]$:

- Lemma 4.1(2) converts `WinPair eps Y q d` into `HostHyp q d`, $q \neq 3$, and $(\frac{-d}{p}) = 1$
  for odd primes $p \le \lfloor Y^{\varepsilon/5} \rfloor$, so `fieldChi` constructs `H0 : HostAx φ`
  with $x^{2+8\varepsilon} \le \varphi.\mathrm{ord} = c \cdot 2^e \le 2 x^{2+8\varepsilon}$
  (`src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:88–103`).
- Lemma 4.2(1) (`isChiField`) deduces `IsChiField ψ e q d H0.E` from `KerChi ψ H0`, so Conclusion 3
  of `WinDatum` gives `VVle H0.E ⌊x^400⌋₊ (sqrt s.b)` (since $s.b = \exp(x^\varepsilon)$); by
  `eventually_rank_le_rpow_of_lt_one_div_fiftytwo` (`src/Development/AutomorphicArithmetic/CharacterBoxes/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5`,
  using $\varepsilon < 1/52$ to check $R.t \le 10708\,x^{399.67} \le \lfloor x^{400} \rfloor$),
  monotonicity lowers $\lfloor x^{400} \rfloor$ to $R.t$.
- Lemma 4.2(2) (`boundedTw`) combines `TwistForm ψ H0` and `PairGood ψ.N eps Y x q d` to verify
  both `BoundedCharsPointwise (Level.cyc ψ).KEPT x eps` (`EAtH.bdG`) and the $4\log x$ bound on
  $\lvert \frac{L'}{L}(1, \chi) \rvert$ (`EAtH.bdL`, with $C = 4$!).
- Finally, the imported short-norm theorem `hostOfField` (`src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8` [Lean]) equips `H0`
  with a finite set $TT \subset \varphi.A$ of Galois elements (Frobenius classes of split primes of
  norm $\le x^{\varepsilon}$) satisfying the weighted coset-equidistribution property
  `φ.Shares TT (x^{-1 + eps})` (`EAtH.shares`). Together with `KeptInXp`, `ExceptionalCharacterKept`,
  and $\varphi.o = (\mathrm{Level.cyc}\,\psi).o$, all six fields of `EAtH (Level.cyc ψ) H.toHostRaw H.TT x eps 4`
  hold (`src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:123–134`). $\square$

---

## 4.5 Remarks

### 4.5.1 Why there is zero circularity here

Let us double-check the logical hygiene of Chapter 4 [Expository]:

1. **Which $L$-functions receive zero-free boxes in `PairGood`?** Only the primitive characters of
   $\mathrm{tw}(\chi_0, q, d, i, j)$ with **$(i \neq 0 \lor j \neq 0)$** (`src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:23`)! When
   $(i, j) = (0, 0)$, the character $\chi_0 \bmod M$ sits inside $\mathrm{Level.cyc}(\psi)$, and
   **nothing in Chapter 4 ever asserts a zero-free box or a prime-sum bound for $(i, j) = (0, 0)$**.
   Instead, $(i, j) = (0, 0)$ is the *output* `Kept` family that Chapter 5 isolates on the left-hand
   side of $\Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}$, while $(i, j) \neq (0, 0)$
   is the `Bounded` parasitic family moved to the right-hand side!
2. **Why Siegel's theorem causes no ineffectiveness problem.** Classically, C. L. Siegel's lower
   bound $L(1, \chi_{\mathrm{real}}) \gg_\eta q^{-\eta}$ (*Acta Arith.* **1** (1935), 83–86) has an
   ineffective implied constant, which makes the threshold $Y_0(M, \varepsilon, A)$ in `PairEx`
   (`src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112`) existentially quantified rather than explicit. Look back at Chapter 3,
   Definition 3.4 (`HasWindows`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean:7`): the Landau-window criterion only asks that
   $\forall y_0,\ \exists Y \ge y_0$ with a good window $[Y, Y^{3/2}]$ — a purely existential
   statement! Whether $Y_0(\varepsilon)$ is computable or not makes no difference to proving
   $L(s, \psi) \neq 0$ on $\Re s > 1/2$ [Expository].
3. **Resolving a community vacuity flag (`pair_share`).** The LUMI vacuity report
   (`aapolipponen/rh-lean-check-lumi`, `docs/reports/vacuity-check.md`) flagged `pair_share` for
   closer human reading because `PairShare.lean` takes existence hypotheses on Stage 1 and Stage 2
   as parameters [Community]. Having read `PairShare.lean`, `PairExists.lean`, `Stage1Succ.lean`,
   `src/Development/AutomorphicArithmetic/MeanSquareBounds/CharOf.lean`, and `pairEx.lean` line by line (`R3`), we can report that `pair_exists`
   instantiates `pair_share` at $\eta = 1/2$ (`src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean:15`) and deduces $\lvert G \rvert > 0$
   from $\lvert \mathcal P \rvert > 0$ (supplied unconditionally by PNT in progressions `count_a`)
   and $\lvert B \rvert \le \frac{1}{2}\lvert \mathcal P \rvert$:
   there is no vacuity at the seam [Lean, read].

### 4.5.2 Summary of the numerical constants

For quick reference in Chapters 5 and 7–11, the table below summarizes where each numerical constant
of this chapter originates [Lean, read]:

| Constant | Lean location | Mathematical role |
|---|---|---|
| $1/400$ and $400$ | `src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:13`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:33`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:26` | Zero-free box width $\Re s > 1 - 1/400$ paired with explicit-formula truncation $Z = x^{400}$ so $x \cdot (x^{400})^{-1/400} = 1$. |
| $401$ | `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49`, `src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean:78` | Upstream Tate–Shafarevich twist cutoff $\lfloor (x')^{401} \rfloor$; absorbs $k^{400} \le x'$ under $x = k x'$ so $x^{400} \le (x')^{401}$. |
| $\lambda = 3/2$ | `src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean:7,40`, `src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean:9` | Window exponent $[Z, Z^{3/2}]$ after rescaling $Z = kW$ inside a quadratic `VWin` window $[W, W^2]$ ($k^3 \le W \implies (kW)^{3/2} \le W^2$). |
| $\varepsilon/5$ | `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:29–34`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:119` | Log-scale $\log q \asymp Y^{\varepsilon/5}$, $\log d \asymp Y^{\varepsilon/5}(\log Y)^2$: large enough that $q > Y^{800A}$, small enough that $1000\log\log d \approx 200\varepsilon \log Y$. |
| $\varepsilon < 1/52$ | `src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:126`, `src/Development/AutomorphicArithmetic/CharacterBoxes/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5` | Ensures $200\varepsilon < 50/13 < 4$ (giving $\lvert L'/L(1,\chi) \rvert \le 4\log Y$, hence $C = 4$ in `EAtH`) and $R.t \le \lfloor x^{400} \rfloor$. |

### 4.5.3 Classical analytic literature behind `P13`

Every ingredient of `P13` is a standard theorem of twentieth-century multiplicative number theory
[Expository]:

- **Exceptional real zeros and primes in progressions:** A. Page, "On the number of primes in an
  arithmetic progression", *Proc. London Math. Soc.* (2) **39** (1935), 116–141 (at most one real
  primitive modulus $\le Z$ with an exceptional zero), combined with C. L. Siegel, "Über die
  Classenzahl quadratischer Zahlkörper", *Acta Arithmetica* **1** (1935), no. 1, 83–86,
  doi:10.4064/AA-1-1-83-86 (giving the Siegel–Walfisz theorem; see Davenport, *Multiplicative Number
  Theory*, 3rd ed., Springer, 2000, Chapters 20–22).
- **Large-sieve zero-density estimates:** E. Bombieri, *Le grand crible dans la théorie analytique
  des nombres*, Astérisque **18**, Société Mathématique de France, 1974, and H. L. Montgomery,
  *Topics in Multiplicative Number Theory*, Lecture Notes in Mathematics **227**, Springer, 1971,
  doi:10.1007/BFb0060851, Chapter 12 (large-sieve Dirichlet-polynomial mean values and zero-density
  bounds of the form $\sum_{\chi \bmod q,\,q \le Q} N(\sigma, T, \chi) \ll (Q^2 T)^{c(1-\sigma)}(\log QT)^A$;
  at $\sigma = 1 - 1/400$ and $T = Q$, any $c < 100/3$ gives exponent $< 3 \cdot \frac{100}{3} \cdot \frac{1}{400} = 1/4$.
  That requirement is far weaker than the classical constants $c = 5/2$ of Montgomery [Montgomery1969]
  and $c = 12/5$ of Huxley [Huxley1972; Huxley1975]. The archive's own proof uses neither: Section 4.7
  shows that it needs only Bombieri's inequality [Bombieri1971] with trivial off-diagonal bounds).

### 4.5.4 Masullo's counterpart

Masullo's draft *The Music of the Primes* never introduces auxiliary prime pairs $(q, d)$, CM host
fields, character-family mean squares, zero-density estimates, or duality and large-sieve
inequalities: because his strategy works directly
with an arbitrary continuous Hecke character $\chi$ on the idele class group $C_F$ of the fixed
base field $F$, there are no parasitic twists to eliminate [Expository].

The nearest counterparts in Masullo's draft are three classical analytic preparation sections in
**Appendix B ("Preparations from Analytic Number Theory", p. 587)** that supply unconditional a
priori control on $L_f(s, \chi)$ before the trace formula is invoked [Paper; Masullo pp. 587–591,
636–643]:

- **Appendix B.1 ("Convexity bound on $L_f(s, \chi)$", pp. 588–591):** proves Phragmén–Lindelöf
  convexity for meromorphic functions with finitely many simple poles (Lemma B.1.1.1, pp. 589–590)
  and deduces Proposition B.1.1.3 (p. 591), $L_f(\sigma + it, \chi) \ll_{F,\chi,\varepsilon} \lvert t \rvert^{[F:\mathbb Q](1-\sigma)/2 + \varepsilon}$
  uniformly for $\sigma \in [0, 1]$ [Paper; Masullo pp. 589–591].
- **Appendix B.4 ("Explicit Formulas for Hecke L-functions", pp. 606–626):** Theorem B.4.2.2
  (statement p. 616, proof p. 617) is a Weil-type explicit formula for a continuous Hecke character $\chi$
  and a Schwartz test function $\phi$ with exponential decay. Writing $\Phi$ for the Mellin transform
  of $\phi$, the sum of $\Phi(\rho - 1/2)$ over the zeros, corrected by the terms $\Phi(\pm 1/2)$, equals
  $\phi(1)\log A_\chi$ minus a weighted prime-power sum, plus archimedean integrals. It is derived from
  the asymptotic residue theorem B.3.2.1. Theorem B.4.4.7 (p. 623) restates it idelically. Footnote 15
  on p. 616, placed on the sentence that introduces Theorem B.4.2.2, reads "Brian should double-check
  this" [Paper; Masullo pp. 606, 616–617, 623].
- **Appendix B.6 ("Classical zero-free regions for Hecke $L$-functions", pp. 636–643):** recalls the
  Hadamard–de la Vallée Poussin zero-free region
  $$\sigma \ge 1 - \frac{A}{[F : \mathbb Q]^4 \log\bigl(A_{F,\chi}(\lvert t \rvert + 3)\bigr)}$$
  with at most one simple real Siegel zero when $\chi$ is quadratic (Proposition B.6.1.1, p. 636,
  deduced from Iwaniec–Kowalski, Theorem 5.10), together with horizontal-segment lower bounds
  $\lvert L_{\Sigma_F - S}(\chi, \sigma + it) \rvert > \lvert t \rvert^{-A}$ for contour shifting
  (Theorem B.6.1.7, pp. 641–643, and Corollary B.6.1.8, p. 643; note also footnote 1 on p. 587,
  questioning whether the zero-free region discussion will ultimately be needed) [Paper; Masullo
  pp. 587, 636, 641–643].

Notice the sharp contrast: Masullo uses a **logarithmic-width** zero-free region
$1 - c / \log(\mathfrak q(\lvert t \rvert + 3))$ for the *fixed* $L$-function under study (to justify
contour integration), whereas the Lean archive uses a **fixed-width** box $\Re s > 1 - 1/400$ up to
subexponential height $Q = F U \le U^{3/2}$ ($\log Q \le \frac{3}{2} Y^{\varepsilon/5}(\log Y)^2$) — impossible to prove a priori
for an individual character, and obtained only by discarding $O(Q^{1/4})$ exceptions out of a random
prime family!

The explicit-formula side shows the same contrast. Masullo's Theorem B.4.2.2 is exact and sums over all
zeros. The archive's counterpart, `tail_contour` (Statement 4.18), is a Perron-type contour shift for
one Dirichlet character with kernel $y^w/(w(w-1))$, truncated at height $T = Q/2$ with error
$z^2/Q$. It is applied only inside a zero-free box, so no sum over zeros ever appears. Nothing in
Masullo's Appendix B plays the role of the counting argument of Section 4.7 [Expository].

---

## 4.6 Lean counterpart for this chapter

Every file in `CharacterBoxes/`, `MeanSquareBounds/`, `ShortNorms/supplyOfAdmOf.lean`,
`TotientGaloisClasses/`, and `FrobeniusOrbits/Statement.lean` cited below was read in full by us
(`R3` / `[Lean, read]`). So were the zero-density package (`zero_density_box` and its `CountZ*`
files) and `page_across` (Section 4.7). The remaining classical analytic sub-packages (the lemma files
behind `tail_contour`, `twist_bound`, `pnt_progressions_relative_weak_holds`,
`excBound`) and the short-norm/rank packages (`hostOfField`, `admissible_ranks_of_CMDatum`) were
read at statement level (`R2` / `[Lean]`). Section 4.7.6 lists the files.

### 4.6.1 Window pairs, host fields, and window rescaling (nodes P12 interface and P13 top)

| Declaration | File:line | Mathematical content / role in Section 4.4 | Tag |
|---|---|---|---|
| `UpperTheory.Top.VVle`, `IsChiField`, `WinPair`, `PageN`, `VAt`, `VWinAt`, `VWin`, `VVle.mono`, `exists_pageN` | `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12,19,27,39,41,44,49,51,67` | Definitions 4.1, 4.4 and Lemma 4.1(1): Tate–Shafarevich length bound, cyclotomic host characterization, prime-pair congruences/scales, `PageN`, and `VWin`. | [Lean, read] |
| `UpperTheory.Top.tw`, `ZeroBox`, `height`, `PairGood`, `PairEx`, `PairGood.mono` | `src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:9,12,15,18,28,41` | Definition 4.2: quadratic twists $\xi(\frac{\cdot}{q})^i(\frac{\cdot}{d})^j$, width-$1/400$ zero-free box, prime-sum and $4\log x$ bounds, and `PairEx`. | [Lean, read] |
| `UpperTheory.Top.KerChi`, `TwistForm`, `WinDatum` | `src/Development/AutomorphicArithmetic/CharacterBoxes/TwistForm.lean:9,14,19` | Artin-kernel characterization, twist decomposition on $A_0$-trivial characters, and rescaled window datum. | [Lean, read] |
| `jac_neg_of_dvd`, `jac_neg_recip`, `UpperTheory.Top.pairHyp` | `src/Development/AutomorphicArithmetic/CharacterBoxes/PairHyp.lean:5,15,24` | Lemma 4.1(2): $p \mid d + 1 \implies (\frac{-d}{p}) = 1$, quadratic reciprocity $(\frac{-q}{d}) = -(\frac{-d}{q})$, and `WinPair` $\implies$ `HostHyp`. | [Lean, read] |
| `UpperTheory.Top.isChiField` | `src/Development/AutomorphicArithmetic/CharacterBoxes/IsChiField.lean:5` | Lemma 4.2(1): `KerChi ψ H` implies `IsChiField ψ φ.e H.q H.d H.E`. | [Lean, read] |
| `UpperTheory.Top.boundedTw_key`, `UpperTheory.Top.boundedTw` | `src/Development/AutomorphicArithmetic/CharacterBoxes/BoundedTw.lean:5,45` | Lemma 4.2(2): every character in `H.Bounded` has $(i, j) \neq (0, 0)$ and inherits $x^{1/2+\varepsilon}$ and $4\log x$ bounds from `PairGood`. | [Lean, read] |
| `UpperTheory.Top.fieldChi` | `src/Development/AutomorphicArithmetic/CharacterBoxes/FieldChi.lean:20` | Constructs `(φ, H : HostAx φ)` of order $c \cdot 2^e$ for a primitive $\psi$ and prime pair $(q, d)$. | [Lean, read] |
| `UpperTheory.Top.winPairs` | `src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean:5` | Proposition 4.8: rescales $x = k x'$ ($k = c^{1/(2+8\varepsilon)}$) to pass from $[W, W^2]$ and $401$ to $[Z, Z^{3/2}]$ and $400$. | [Lean, read] |
| `UpperTheory.Top.eventually_rank_le_rpow_of_lt_one_div_fiftytwo` | `src/Development/AutomorphicArithmetic/CharacterBoxes/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5` | Uses $\varepsilon < 1/52$ to prove $R.t \le \lfloor x^{400} \rfloor$ for large $x$. | [Lean, read] |
| `UpperTheory.T3.supplyOfAdmOf` | `src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:13` | Theorem 4.9 core: combines `winPairs`, `fieldChi`, `isChiField`, `boundedTw`, and `hostOfField` to build `EAtH` ($C = 4$) and `VVle` on $[Z, Z^{3/2}]$. | [Lean, read] |
| `UpperTheory.Top.supplyChi` | `src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean:8` | Theorem 4.9 top entry: `VWin → PairEx → ∀ ψ, HostExW (3 / 2) ...`, feeding `zeroFreeAll_of_topG` in Chapter 3. | [Lean, read] |
| `UpperTheory.Top.hostOfField`, `UpperTheory.Top.supplyOfAdm` | `src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8,17` | Statement wrapper for short-norm Frobenius coset equidistribution `Shares H.TT (x^{-1+eps})` (`hostOfField` imported as R2; `supplyOfAdm` one-line wrapper). | [Lean] |
| `admissible_ranks_of_CMDatum` | `src/Development/AutomorphicArithmetic/CoprimeRanks/AdmChi.lean:11` | Supplies admissible unitary/theta rank tuples `RankVal s R` over `(φ, H0)`. | [Lean] |
| `Formalism.HC.Frame`, `A`, `A0`, `GG`, `sg`, `cc`, `iod`, `Psi` | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:15,29,63,89,100,102,104,112` | Definition 4.4(2): finite abelian Galois group model of order $4\,\varphi.\mathrm{ord}$. | [Lean, read] |
| `Formalism.HC.HostRaw`, `HostDer`, `HostAx`, `isCMField_hostE`, `finrank_cmField`, `finrank_hostF`, `conjE_mem_hostF_iff` | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:12,87,174,182,183,184,199` | Definition 4.4(3) and Lemma 4.2(1): CM host field $E$, totally real $F = E^+$, degrees $4\,\varphi.\mathrm{ord}$ and $2\,\varphi.\mathrm{ord}$. | [Lean, read] |
| `HostRaw.conj_sqd`, `HostRaw.hostSplitK` | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean:254,322` | $\mathrm{conj}(\sqrt{-d}) = -\sqrt{-d}$ and complete splitting in $K = \mathbb Q(\sqrt{-d})$ of $2$, $q$, and primes $\le b$. | [Lean, read] |
| `Formalism.FrobeniusOrbits.HostHyp`, `HostExample`, `HostRecip`, `HostReal` | `src/Formalism/FrobeniusOrbits/Statement.lean:13,91,110,147` | Toy example `HostHyp 11 7` (Section 4.2.1), reciprocity $(\frac{-q}{d}) = -1$, and real $2$-power layer. | [Lean, read] |

### 4.6.2 Two-stage analytic sieve and classical analytic inputs (node P13 engine)

| Declaration | File:line | Mathematical content / role in Section 4.4 | Tag |
|---|---|---|---|
| `QH.S`, `MeanSq`, `GoodC`, `Box`, `BoxAll`, `primePairSetFirst`, `primeSetTwoBounds`, `GoodQ`, `GoodD` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:13,26,32,35,38,41,45,48,51` | Definition 4.3(2): truncated Jacobi prime sum $S(Z, y, q, \kappa)$, $L^2$ mean-square predicate, and Stage 1/2 prime progressions. | [Lean, read] |
| `QH.count_bad_core`, `QH.count_bad` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBadCore.lean:18`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean:9` | Lemma 4.3: injectivity of $q \mapsto (f_{r(q)} q, \psi_{r(q),q})$ for $q > F$ reduces $\lvert B_1 \rvert$ to `zero_density_box`. | [Lean, read] |
| `QH.tailK_exp`, `tailK_num`, `tailK` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:8,23,92` | Lemma 4.4(1): $\lvert y\,\mathrm{tailL}_\chi((Y^K)^{400}) \rvert \le Y^\varepsilon$ via $x \cdot (x^{400})^{-1/400} = 1$. | [Lean, read] |
| `QH.kappa4_num`, `kappa4_loglog`, `kappa4` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:9,44,126` | Lemma 4.4(2): $\lvert \frac{L'}{L}(1,\chi) \rvert \le 1000\log\log Q + C \le 4\log Y$ for $\varepsilon < 1/52$. | [Lean, read] |
| `QH.box_of_S` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:28` | Lemma 4.4(3): splits $G_\chi(y)$ at $Z = (Y^K)^{400}$ into $-S(Z, y, q, \kappa)$ and $-y\,\mathrm{tailL}_\chi(Z)$. | [Lean, read] |
| `QH.meanSq_abs`, `QH.meanSqK`, `QH.twistK` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean:8`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean:51`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean:148` | Proposition 4.5: expands $L^2$ norm, strips $\kappa$, and bounds Jacobi character sums over primes outside at most one Landau–Page modulus $n_*$. | [Lean, read] |
| `QH.bs_S_sub_S`, `bs_mul_D_eq_S`, `bs_sq_integral_le`, `bs_sum_D_le`, `bs_block`, `bs_markov`, `bad_share` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean:76,83,98,146,163,207,251` | Lemma 4.6: fundamental theorem of calculus $y D_q(y) = S(Z, y, q, \mathbf{1}_{y < m}\kappa)$, dyadic Cauchy–Schwarz, and geometric-series Markov uniformization on $[Y, X]$. | [Lean, read] |
| `QH.stage_log`, `stage_pow`, `stage` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:16,29,41` | Theorem 4.7(1): single-stage prime sieve combining `count_bad`, `box_of_S`, `meanSqK`, and `bad_share`. | [Lean, read] |
| `QH.stage1`, `QH.stage2`, `QH.pair_share`, `QH.pair_exists`, `QH.pairEx` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/Stage1Succ.lean:36`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/CharOf.lean:61`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairShare.lean:26`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean:9`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112` | Theorem 4.7(2): Stage 1 ($q \equiv 3 \pmod 8$) + Stage 2 ($d \equiv 7 \pmod{16}$, $q \mid d+1$, small odd $p \mid d+1$) $\implies$ `PairEx`. | [Lean, read] |
| `ZeroDensityBox`, `zero_density_box` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean:7`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13` | Definition 4.3(1), Definition 4.5 and Theorem 4.15: at most $C Q^{1/4}$ primitive characters of modulus $\le Q$ have a zero in $\mathcal B(Q)$, proved by mollifier detection and Bombieri's inequality (Section 4.7). | [Lean, read] |
| `duality_inequality`, `pair_sum_bound`, `pair_twist_bound`, `mollifier_identity`, `coefficient_square_bound`, `zero_detection`, `blockCountOf_statement`, `numeric_constants`, `final_bound_of_assembly` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDual.lean:9`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZPair.lean:98`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZTwist.lean:32`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZMoll.lean:79,133`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDetect.lean:43`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZBlock.lean:23`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZNum.lean:10`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZFinal.lean:10` | Lemmas 4.10–4.13, Proposition 4.14 and Theorem 4.15. | [Lean, read] |
| `divisor_weight_bound`, `l_function_partial_sum`, `LFunction_eq_G`, `norm_character_sum_Icc_le` | `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean:56`; `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean:136`; `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean:228`; `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:39` | Direct dependencies of Lemmas 4.12–4.13: $d(n) \le C_e n^e$, partial-sum approximation of $L(s, \chi)$ on $\Re s > 0$, and character sums $\le q + 1$. | [Lean, read] |
| `page_across` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPage.lean:37` | Lemma 4.16: Landau–Page across moduli, conditional on `ZFRDirichlet` (proved by `zFRDirichlet` [Lean]). | [Lean, read] |
| `meanSquareHypW_of_pnt` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMain.lean:55` | Diagonal $s=1$ and single exceptional modulus $s=n_*$ prime-power counting for `MeanSq`. | [Lean, read] |
| `count_pos`, `count_a` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean:275,346` | §4.9 proves the conditional candidate count and traces its use in the sieve. | [Lean, read] |
| `tail_contour`, `box_tail_bound`, `twist_bound`, `pnt_progressions_relative_weak_holds`, `excBound` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContour.lean:14`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailFinal.lean:13`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwist.lean:18`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:22`; `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:32` | Statements 4.17–4.18. These are the Perron contour tail on $\mathcal B(Q)$, the Jacobi-sum bound outside $n_*$, PNT in progressions, and Siegel's lower bound. `tailK` and `kappa4` call `tail_contour` directly, and `box_tail_bound` is its real-character sibling. Top-level proofs are read; the internal files are `R2`. | [Lean] |

---

## 4.7 Zero density, mean squares and Siegel's lower bound: from the large sieve to `PairGood`

Sections 4.4.2–4.4.5 used four classical inputs as black boxes: the zero-density count
`zero_density_box`, the contour tail `tail_contour`, the prime count `count_a` behind
$\lvert \mathcal P \rvert \ge U^{9/10}$, and the exceptional-character input
(`page_across`, `excBound`). This section opens the first of them completely and the others as
far as we have read them. We follow the archive's proof line by line, and Section 4.7.6 lists
exactly what is still `R2`.

### 4.7.1 Motivation: why a crude zero-density bound is enough

The sieve of Theorem 4.7 needs only one numerical fact about zeros. At height $Q = FU \le U^{3/2}$
the number of characters of conductor $\le Q$ with a zero in
$$\mathcal B(Q) = \Bigl\{ s : \Re s > 1 - \tfrac{1}{400},\ \lvert \Im s \rvert \le Q \Bigr\}$$
must be smaller than the number of candidate primes, so $O(Q^{1/4}) = O(U^{3/8})$ against
$\lvert \mathcal P \rvert \ge U^{9/10}$ suffices (Theorem 4.7, proof of part 1). Classical zero-density theorems give
far more. Montgomery's hybrid estimate
$\sum_{q \le Q} \sum^{\ast}_{\chi \bmod q} N(\sigma, T, \chi) \ll (Q^2 T)^{5(1-\sigma)/2} (\log QT)^{c}$
[Montgomery1969] and Huxley's exponent $12/5$ in place of $5/2$ [Huxley1972; Huxley1975] give,
at $\sigma = 1 - 1/400$ and $T = Q$, the powers $Q^{3/160}$ and $Q^{9/500}$, both far below $Q^{1/4}$ [Expository].

The archive therefore proves a deliberately weak estimate by the shortest classical route. There
are three steps.

1. **Detection.** A zero of $L(s, \chi)$ makes a mollified Dirichlet polynomial large on some dyadic block.
2. **Duality.** A Bessel-type inequality of Bombieri [Bombieri1971] bounds the number of characters for which one fixed block is large.
3. **Bookkeeping.** Summing over blocks produces $Q^{1/4}$.

The proof of `zero_density_box` neither proves nor uses the arithmetic large sieve inequality
[Bombieri1965; Montgomery1968]. Off-diagonal terms are bounded trivially by complete character
sums. That is why its exponent is $1/4$ and not $0.02$.

### 4.7.2 Examples: the primes $11$ and $3$ (both $\equiv 3 \pmod 8$)

**Example 4.7.1 (a mollifier at toy length).** Take $\chi = (\frac{\cdot}{11})$, $Y = 2$, $N = 3$.
The mollified coefficients are
$$\mathrm{mco}(Y, N, n) = \sum_{\substack{ab = n \\ 1 \le a \le Y,\ 1 \le b \le N}} \mu(a)$$
(`mco`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean:18`) [Lean, read].
For $n = 1, \dots, 6$ they equal $1, 0, 1, -1, 0, -1$. For example $n = 2$ has the two
factorizations $1 \cdot 2$ and $2 \cdot 1$, which contribute $\mu(1) + \mu(2) = 0$. Hence
$$\bigl(1 + \chi(2)2^{-s} + \chi(3)3^{-s}\bigr)\bigl(1 - \chi(2)2^{-s}\bigr)
= 1 + \chi(3)3^{-s} - \chi(4)4^{-s} - \chi(6)6^{-s},$$
which one also checks by multiplying out and using $\chi(2)^2 = \chi(4)$. The term $n = 2 \le Y$
has cancelled. This is the mollifier identity of Lemma 4.12 below in its smallest case [Expository].

**Example 4.7.2 (two characters are almost orthogonal).** Take $\chi = (\frac{\cdot}{11})$ and
$\chi' = (\frac{\cdot}{3})$. Both are primitive and distinct, so $n \mapsto \chi(n)\overline{\chi'(n)}$
is the non-principal character $(\frac{\cdot}{33})$. Its sum over any $33$ consecutive integers is
$0$. Lemma 4.11 therefore gives $\lvert \sum_{0 \le n < M} \chi(n)\overline{\chi'(n)} \rvert \le 33$
for every $M$. In fact the largest partial sum for $M \le 132$ is $3$, attained at $M = 5$
(direct computation) [Expository]. The archive only uses the trivial bound $33 = 11 \cdot 3$.

**Example 4.7.3 (the actual parameters at $Q = 20$).** `zero_detection` works with
$X = \lceil Q \rceil$, mollifier length $Y = X^4$, $J = 8(\lfloor \log_2 X \rfloor + 1)$ blocks and partial-sum
length $N = 2^J$ (`q0`, `pY`, `pJ`, `pN`,
`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean:48–51`) [Lean, read].
At $Q = 20$ this gives
$X = 20$, $Y = 160{,}000$, $J = 8 \cdot 5 = 40$ and $N = 2^{40} \approx 1.1 \times 10^{12}$.
The detection inequality $\lVert P \rVert \cdot Y \le 3/X$ of Lemma 4.13 becomes $3/20 \le 1/2$.
The final exponent is $12 \cdot \frac{3}{200} + \frac{7}{100} = \frac{1}{4}$: the block length
reaches $Y 2^J \le 2^{20} Q^{12}$, each block costs a power $3/200$, and $J^3 \le Q^{7/100}$
absorbs the logarithms (Theorem 4.15) [Lean, read].

### 4.7.3 Definitions

**Definition 4.5 (`ZeroDensityBox`, exact form).** `ZeroDensityBox`
(`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean:7`) states: there is $C \in \mathbb R$ such that for every real $Q \ge 3$ and every finite set $S$ of
pairs $(N + 1, \chi)$ with $\chi$ a Dirichlet character modulo $N + 1$, the following holds. If every element of $S$ satisfies

- $\chi$ is primitive,
- $N + 1 \le Q$, and
- $L(s, \chi) = 0$ for some $s$ with $\Re s > 1 - \frac{1}{400}$ and $\lvert \Im s \rvert \le Q$,

then $\lvert S \rvert \le C\,Q^{1/4}$ [Lean, read].

Three features matter. The bound counts characters, not zeros. The constant carries no sign
condition. The modulus-$1$ character, whose $L$-function is $\zeta$, is admitted and contributes at most $1$.

**Definition 4.6 (blocks and parameters).** Put $s_0 := 1 - \frac{1}{400}$ (`s0`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean:16`). For
$Y, N, U \in \mathbb N$, a character $\chi$ and $s \in \mathbb C$, the dyadic block is
$$\mathrm{blk}(Y, N, U, \chi, s) := \sum_{U < n \le 2U} \mathrm{mco}(Y, N, n)\,\chi(n)\,n^{-s}$$
(`blk`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean:21`). The parameters $X$, $Y$, $J$ and $N$ are those of Example 4.7.3 [Lean, read].

**Definition 4.7 (the five interfaces).** `CountZDefs.lean` splits the proof into named
propositions. `zero_density_box` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`) is the composite term
`final_bound_of_assembly (coefficient_square_bound divisor_weight_bound) (zero_detection mollifier_identity) (blockCountOf_statement duality_inequality (pair_twist_bound pair_sum_bound)) numeric_constants`
(`:14–15`) [Lean, read]. The interfaces are:

| Name | Lean location | Content, with the quantifiers as in Lean |
|---|---|---|
| `DualIneq` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean:24` | For finite $S$ and $I$, vectors $v_i \in \mathbb C^I$, $b \in \mathbb C^I$ and $\Delta \ge 0$: if every row sum $\sum_{j \in S} \lvert \sum_{n \in I} v_i(n)\overline{v_j(n)} \rvert$ is $\le \Delta$, then $\sum_{i \in S} \lvert \sum_n b_n v_i(n) \rvert^2 \le (\sum_n \lvert b_n \rvert^2)\,\Delta$. |
| `PairSum`, `PairTwist` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean:29,33` | Distinct primitive $\chi \bmod q$ and $\chi' \bmod q'$ satisfy $\lvert \sum_{n < M} \chi(n)\overline{\chi'(n)} \rvert \le qq'$ for all $M$. For $\Re w > 0$ and $U \ge 1$, the twisted block satisfies $\lvert \sum_{U < n \le 2U} \chi(n)\overline{\chi'(n)} n^{-w} \rvert \le 2qq'(1 + \lvert w \rvert)$. |
| `MollId`, `CoeffSq` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean:38,44` | The identity of Lemma 4.12(2). There is $C \ge 0$ with $\sum_{U < n \le 2U} (\lvert \mathrm{mco}(Y, N, n) \rvert n^{-s_0})^2 \le C U^{-197/200}$ for all $Y$, $N$ and all $U \ge 1$. |
| `Detect` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean:53` | The conclusion of Lemma 4.13, for $Q \ge 20$ and moduli $2 \le q \le Q$. |
| `BlockCount`, `Num` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean:58,68` | The conclusions of Proposition 4.14 and of the two numerical inequalities in the proof of Theorem 4.15. |

### 4.7.4 Lemmas and proofs: the zero-density box

**Lemma 4.10 (Bombieri's inequality; `duality_inequality`).** *`DualIneq` holds.*
*(Lean: `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDual.lean:9`.)* [Lean, read]

*Proof.* Write $s_i := \sum_n b_n v_i(n)$, $X := \sum_{i \in S} \lvert s_i \rvert^2$,
$w_n := \sum_{i \in S} \overline{s_i}\, v_i(n)$ and $G_{ij} := \sum_n v_i(n)\overline{v_j(n)}$
(`:15–17`). Exchanging the two finite sums gives $X = \sum_n b_n w_n$ (`:29`). Hence
$X \le \sum_n \lvert b_n \rvert \lvert w_n \rvert$ (`:42`), and by Cauchy–Schwarz (`:47`)
$$X^2 \le \Bigl(\sum_n \lvert b_n \rvert^2\Bigr)\Bigl(\sum_n \lvert w_n \rvert^2\Bigr).$$
Expanding the square gives $\sum_n \lvert w_n \rvert^2 = \sum_{i, j} \overline{s_i} s_j G_{ij}$ (`:58`). With
$\lvert s_i \rvert \lvert s_j \rvert \le \frac12(\lvert s_i \rvert^2 + \lvert s_j \rvert^2)$ and the symmetry
$\lvert G_{ij} \rvert = \lvert G_{ji} \rvert$ (`:49`), this sum is
$$\le \sum_{i} \lvert s_i \rvert^2 \sum_{j} \lvert G_{ij} \rvert \le \Delta X$$
(`:73`, `:96`). So $X^2 \le B \Delta X$ with $B = \sum_n \lvert b_n \rvert^2$ (`:114`), and $X \le B\Delta$ whether
$X = 0$ or not (`:121–124`). $\square$

*Remark.* For $\xi, \varphi_1, \dots, \varphi_R$ in a Hilbert space this is
$\sum_r \lvert \langle \xi, \varphi_r \rangle \rvert^2 \le \lVert \xi \rVert^2 \max_r \sum_s \lvert \langle \varphi_r, \varphi_s \rangle \rvert$,
Bombieri's generalization of Bessel's inequality [Bombieri1971]. In zero-density work it is the
mean-value step of the Halász–Montgomery method [Montgomery1969; Montgomery1971]. See also
[Davenport2000, Ch. 27]. Lean pairs $b$ with $v_i$ bilinearly. Since
$\lvert \langle \overline{v_i}, \overline{v_j} \rangle \rvert = \lvert \langle v_i, v_j \rangle \rvert$, this is the same statement [Expository].

**Lemma 4.11 (distinct primitive characters; `pair_sum_bound`, `pair_twist_bound`).**
*Let $\chi \bmod q$ and $\chi' \bmod q'$ be primitive and distinct as pairs $(q, \chi) \ne (q', \chi')$.*

1. *For every $M \in \mathbb N$, $\lvert \sum_{0 \le n < M} \chi(n)\overline{\chi'(n)} \rvert \le qq'$.*
2. *For $\Re w > 0$ and $U \ge 1$, $\lvert \sum_{U < n \le 2U} \chi(n)\overline{\chi'(n)}\,n^{-w} \rvert \le 2qq'(1 + \lvert w \rvert)$.*

*(Lean: `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZPair.lean:98` and `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZTwist.lean:32`.)* [Lean, read]

*Proof.*

1. Lift both characters to modulus $qq'$ and put $\psi := \chi^{\uparrow}\,(\chi'^{\uparrow})^{-1}$
   (`mulLevel`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZPair.lean:11`). Suppose $\psi = 1$. Then the lifts coincide. Their conductors are $q$ and $q'$
   because both characters are primitive, so $q = q'$. Injectivity of the lift then gives $\chi = \chi'$,
   a contradiction (`:15–28`).
   On units, $\psi(n) = \chi(n)\overline{\chi'(n)}$ because $\lvert \chi'(n) \rvert = 1$; off units, both sides vanish (`:30–57`).
   A non-principal character sums to $0$ over each full period. What remains is fewer than
   $qq'$ terms of modulus $\le 1$ (`:72–96`).
2. Apply Abel summation to $f(n) = n^{-w}$ against these partial sums (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZTwist.lean:42`). Each of the two boundary terms is at most $qq'$, because
   $\lvert n^{-w} \rvert \le 1$ (`:43–52`). For $i \ge U$, the representation
   $i^{-w} - (i+1)^{-w} = w \int_i^{i+1} t^{-w-1}\,dt$ gives $\lvert (i+1)^{-w} - i^{-w} \rvert \le \lvert w \rvert/U$
   (`norm_cpow_sub_le'`, `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean:69`; `norm_cpow_step_le`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZTwist.lean:13`). At most $U$ such terms
   contribute $qq'\lvert w \rvert$ in total (`:53–67`). Hence the sum is at most $2qq' + qq'\lvert w \rvert \le 2qq'(1 + \lvert w \rvert)$. $\square$

**Lemma 4.12 (mollifier identity and coefficient size; `mollifier_identity`, `coefficient_square_bound`).**

1. *$\mathrm{mco}(Y, N, 1) = 1$. If $2 \le n \le Y \le N$, then $\mathrm{mco}(Y, N, n) = \sum_{d \mid n} \mu(d) = 0$. Always $\lvert \mathrm{mco}(Y, N, n) \rvert \le d(n)$, the number of divisors.*
   *(Lean: `mco_one`, `mco_eq_zero`, `mco_norm_le`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZMoll.lean:10,53,60`.)*
2. *For every Dirichlet character $\chi \bmod q$, every $s$, and $1 \le Y \le N$ with $YN \le K$,*
   $$\Bigl(\sum_{n \le N} \chi(n) n^{-s}\Bigr)\Bigl(\sum_{d \le Y} \mu(d)\chi(d) d^{-s}\Bigr)
   = 1 + \sum_{Y < n \le K} \mathrm{mco}(Y, N, n)\,\chi(n)\,n^{-s}.$$
   *(Lean: `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZMoll.lean:79`.)*
3. *There is $C \ge 1$ such that $d(n) \le C\,n^{1/400}$ for all $n \ge 1$. Consequently,
   $\sum_{U < n \le 2U} (\lvert \mathrm{mco}(Y, N, n) \rvert n^{-s_0})^2 \le C^2 U^{-99/100} \le C^2 U^{-197/200}$
   for all $Y$, $N$ and all $U \ge 1$.*
   *(Lean: `divisor_weight_bound`, `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean:56`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZMoll.lean:133`.)* [Lean, read]

*Proof.*

1. Only the factorization $1 \cdot 1$ contributes at $n = 1$. For $2 \le n \le Y \le N$, every
   factorization $n = ab$ satisfies the two box constraints, so the sum runs over all divisors and
   vanishes by Möbius inversion (`:23–58`). The bound $\lvert \mathrm{mco} \rvert \le d(n)$ follows
   from $\lvert \mu \rvert \le 1$ (`:60–77`).
2. Multiply out, regroup the double sum by the product $n = ab \le YN \le K$, and use part 1 for $n \le Y$
   (`:94–131`).
3. Write $d(n) = \prod_{p^a \parallel n} (a + 1)$. When $p^{e} \ge 2$, we have $a + 1 \le (p^{e})^a$.
   For every prime, $a + 1 \le \max(1, 1/(e\log 2))\,(p^e)^a$. Only the primes below $K = \lceil 2^{1/e} \rceil$ need the second bound, so
   $d(n) \le \max(1, 1/(e \log 2))^{K} n^e$ (`src/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean:56–92`). This is the textbook argument.
   With $e = 1/400$ (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZMoll.lean:141`), each term of the sum is at most
   $(C n^{1/400 - 399/400})^2 \le C^2 U^{-199/100}$. There are $U$ terms (`:149–191`). $\square$

**Lemma 4.13 (zero detection; `zero_detection`).** *Let $Q \ge 20$ and let $\chi \bmod q$ be primitive
with $2 \le q \le Q$. Let $\rho$ be a zero of $L(s, \chi)$ with $\Re \rho > s_0$ and $\lvert \Im \rho \rvert \le Q$.
With $Y$, $N$ and $J$ as in Example 4.7.3, some $j \in \{0, \dots, J - 1\}$ satisfies*
$$\bigl\lvert \mathrm{blk}(Y, N, Y 2^j, \chi, \rho) \bigr\rvert \ge \frac{1}{2J}.$$
*(Lean: `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDetect.lean:43`.)* [Lean, read]

*Proof.*

1. A primitive character of modulus $q \ge 2$ is non-principal (`:54–58`).
2. *Partial-sum approximation.* For non-principal $\chi$ we have
   $\lvert \sum_{1 \le n \le M} \chi(n) \rvert \le q + 1$
   (`norm_character_sum_Icc_le`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:39`).
   For $\Re s > 0$ and $N \ge 1$,
   $$\Bigl\lvert L(s, \chi) - \sum_{n \le N} \chi(n) n^{-s} \Bigr\rvert \le 2(q + 1)\Bigl(1 + \frac{\lvert s \rvert}{\Re s}\Bigr) N^{-\Re s}$$
   (`LPartialSum`, `src/Formalism/LFunctionBounds/PositivityBound.lean:62`; `l_function_partial_sum`, `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean:136`).
   The proof writes Mathlib's $L(s, \chi)$ as the Abel series
   $G(s) = \sum_n A(n)(n^{-s} - (n+1)^{-s})$, with $A(n) = \sum_{k \le n} \chi(k)$, for $\Re s > 0$.
   Both functions are holomorphic on the half-plane and agree for $\Re s > 1$; the identity theorem
   then gives equality (`LFunction_eq_G`, `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean:228`). The tail of the Abel series is
   at most $(q+1)\frac{\lvert s \rvert}{\Re s}(N+1)^{-\Re s}$ (`src/Formalism/LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean:12`).
3. *Numerics.* Put $P := \sum_{n \le N} \chi(n) n^{-\rho}$. Since $L(\rho, \chi) = 0$, part 2 bounds $\lVert P \rVert$. Moreover
   $q + 1 \le 2X$, $1 + \lvert \rho \rvert/\Re \rho \le 3X$ and $N \ge X^8$. Hence
   $N^{-\Re \rho} \le N^{-15/16} \le 1/(4X^7)$, using $\sqrt X \ge 4$. Therefore $\lVert P \rVert\,Y \le 3/X \le 1/2$
   (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDetect.lean:82–138`).
4. *Mollification.* Each term of $M := \sum_{d \le Y} \mu(d)\chi(d)d^{-\rho}$ has modulus $\le 1$, so
   $\lvert M \rvert \le Y$ (`:20`). Lemma 4.12(2) with $K = YN$ gives $1 + D = PM$, where
   $D = \sum_{Y < n \le YN} \mathrm{mco}(n)\chi(n)n^{-\rho}$. So $\lvert 1 + D \rvert \le 1/2$ and
   $\lvert D \rvert \ge 1/2$ (`:139–147`).
5. Since $YN = Y 2^J$, $D$ is the sum of the $J$ blocks $\mathrm{blk}(Y, N, Y2^j, \chi, \rho)$
   (`sum_blocks`, `:10`; `:149`). If every block had modulus $< 1/(2J)$, then $\lvert D \rvert < 1/2$ (`:152–162`). $\square$

**Proposition 4.14 (block count; `blockCountOf_statement`).** *Assume `CoeffSq` with constant $C \ge 0$.
Let $Q \ge 3$, let $Y, N, U, J \ge 1$, and suppose $8Q^3 C U^{-197/200} \le 1/(8J^2)$. Let $T$ be a finite set of
primitive characters of moduli $\le Q$. For each $\chi \in T$, let $\rho_\chi$ satisfy
$s_0 < \Re \rho_\chi < 1$, $\lvert \Im \rho_\chi \rvert \le Q$ and
$\lvert \mathrm{blk}(Y, N, U, \chi, \rho_\chi) \rvert \ge 1/(2J)$. Then $\lvert T \rvert \le 8J^2 C\,U^{3/200}$.*
*(Lean: `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZBlock.lean:23`.)* [Lean, read]

*Proof.* On $I = (U, 2U]$ put $b_n := \mathrm{mco}(n)n^{-s_0}$ and
$v_\chi(n) := \chi(n)\,n^{-(\rho_\chi - s_0)}$ (`:29–30`). Then $\sum_n b_n v_\chi(n)$ is the block of $\chi$
(`:115`), and $\sum_n \lvert b_n \rvert^2 \le C U^{-197/200}$ (`:123`).

In the Gram matrix, the diagonal entry is at most $U$, because $\lvert v_\chi(n) \rvert \le 1$ (`:40–60`).
For $\chi' \ne \chi$, the product $v_\chi(n)\overline{v_{\chi'}(n)}$ equals $\chi(n)\overline{\chi'(n)}n^{-w}$
with $w = (\rho_\chi - s_0) + \overline{(\rho_{\chi'} - s_0)}$ (`:67–75`). Here $0 < \Re w \le 1$ and
$\lvert \Im w \rvert \le 2Q$, so Lemma 4.11(2) bounds the entry by $2Q^2(2 + 2Q) \le 8Q^3$ (`:61–103`). The
row sums are therefore at most $\Delta := U + \lvert T \rvert\,8Q^3$ (`:31`, `:104–113`).

Lemma 4.10 gives (`:129–156`)
$$\frac{\lvert T \rvert}{4J^2} \le \sum_{\chi \in T} \lvert \mathrm{blk} \rvert^2
\le C U^{-197/200}\bigl(U + 8Q^3 \lvert T \rvert\bigr)
\le C U^{3/200} + \frac{\lvert T \rvert}{8J^2}.$$
Rearranging gives the claim (`:157–166`). $\square$

**Theorem 4.15 (the zero-density box; `zero_density_box`).** *`ZeroDensityBox` holds.*
*(Lean: `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`, via `final_bound_of_assembly`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZFinal.lean:10`, and `numeric_constants`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZNum.lean:10`.)* [Lean, read]

*Proof.* *Numerics* (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZNum.lean:10–134`). Take $Q_0 \ge 20$ beyond which two bounds hold:
$(\log Q)^3 \le Q^{7/100}/32768$ and $(\log Q)^2 \le Q^{47/50}/(65536(C + 1))$ (`:12–17`). Then
$J \le 32\log Q$ (`:58`), and for $Q \ge Q_0$ two inequalities follow.

- Since $Y 2^j \ge Q^4$, we get $Q^3 (Y2^j)^{-197/200} \le Q^{-47/50}$ and $64CJ^2 \le Q^{47/50}$. These give the
  hypothesis $8Q^3C(Y2^j)^{-197/200} \le 1/(8J^2)$ of Proposition 4.14 for every $j < J$ (`:64–96`).
- Since $2^J \le 256\,X^8$ and $X \le 2Q$, we get $Y 2^J \le 2^{20} Q^{12}$ (`:97–109`). With $J^3 \le Q^{7/100}$ (`:118`) this yields
  $$1 + J \cdot 8J^2 C (Y2^J)^{3/200} \le \bigl(1 + 8C\,(2^{20})^{3/200}\bigr) Q^{7/100 + 9/50} = C' Q^{1/4}$$
  (`:110–134`).

*Assembly* (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZFinal.lean:10–129`).

- If $3 \le Q < Q_0$, then $S$ lies in the finite set $F$ of all characters of modulus $\le \lceil Q_0 \rceil$
  (`:15`, `:19–33`).
- If $Q \ge Q_0$, at most one element of $S$ has modulus $1$ (`:47–56`). For every other element choose a zero
  $\rho_\chi$ in the box (`:58–64`). It has $\Re \rho_\chi < 1$ because $L(s,\chi) \ne 0$ on $\Re s \ge 1$
  (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZFinal.lean:84–89`, using Mathlib `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:398`). Lemma 4.13 assigns a block index
  $j(\chi) < J$ (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZFinal.lean:65–83`). Proposition 4.14 bounds each fibre $\{j(\chi) = j\}$ by
  $8J^2C(Y2^j)^{3/200} \le 8J^2 C (Y2^J)^{3/200}$ (`:94–116`). Summing over $J$ fibres and adding $1$
  gives $\lvert S \rvert \le C' Q^{1/4}$ (`:117–129`).

The constant is $\max(C', \lvert F \rvert + 1)$. $\square$

### 4.7.5 Mean squares and Siegel's lower bound: the other classical inputs

The mean-square half of the sieve (Proposition 4.5) rests on three more statements.

**Lemma 4.16 (Landau–Page across moduli; `page_across`).** *Assume `ZFRDirichlet`
(`src/Formalism/LandauZeroFreeBounds/Statement.lean:15`). This is the classical zero-free region
$\Re s \ge 1 - c/\log(q(\lvert \Im s \rvert + 2))$ for all $L(s, \chi)$ modulo $q$, except for at most
one zero. Such a zero is real and simple and belongs to a real non-principal character. Then there
is $c_0 > 0$ with the following property. Let $Z \ge 3$, let $M_1, M_2 \le Z$, and let $\chi_1 \bmod M_1$, $\chi_2 \bmod M_2$ be real and
non-principal. Suppose each $L(s, \chi_i)$ has a real zero $\beta_i \in (1 - c_0/\log Z, 1)$. Then
$\chi_1(n) = \chi_2(n)$ for every $n$ coprime to $M_1 M_2$.*
*(Lean: `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPage.lean:37`, called at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwist.lean:26` and `src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean:158`.)* [Lean, read]

*Proof.* Take $c_0 = c/3$ (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPage.lean:45`). Lift both characters to modulus $M_1 M_2 \le Z^2$. The lifted
$L$-functions still vanish at $\beta_i$ (`isLZero_changeLevel`, `:27`). Since
$\log(2M_1M_2) \le 3\log Z$, both zeros lie in the region of `ZFRDirichlet` for the modulus $M_1M_2$
(`inRegion_of_lt`, `:10`). The uniqueness clause of `ZFRDirichlet` forces the two lifts to be the
same character (`:58–59`). Evaluating at the unit $n \bmod M_1M_2$ gives the claim (`:60–65`). $\square$

This is the step that leaves at most one exceptional modulus $n_*$ in Proposition 4.5. The real
characters $(\frac{\cdot}{s})$ with exceptional zeros all come from one primitive character. The
input `ZFRDirichlet` itself is proved by `zFRDirichlet`
(`src/Formalism/LandauZeroFreeBounds/NoZeroComplex.lean:32`) [Lean]. The neighbouring
`twist_bound` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwist.lean:18`) is the archive's own version of the Jacobi-sum estimate
$\lvert \sum_{q \in \mathcal P} (\frac{q}{s}) \rvert \le x^{-3}\lvert \mathcal P \rvert$ for odd squarefree
$s \ne n_*$. We read its statement and its first lines, `:25–26` [Lean].

**Statement 4.17 (primes in progressions and the exceptional zero; `count_a`, `excBound`).**

1. `ExcBound` (`src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:50`) states:
   for every $\varepsilon > 0$ there is $c > 0$ such that every real zero $\beta$ of every real
   non-principal $L(s, \chi)$ modulo $q$ satisfies $\beta \le 1 - c\,q^{-\varepsilon}$. Its proof term
   `excBound := excBound_of_siegelLower siegelLower`
   (`src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:26,32`) derives it from Siegel's lower bound
   $\lvert L(1, \chi) \rvert \ge c\,q^{-\varepsilon}$ (`SiegelLower`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean:29`) [Siegel1935] and from a bound for
   $L'$ near $1$. The ordinary derivative and real-segment integral are worked out in [§4.10.24](#41024-separating-a-real-zero-from-1). We read the assembly; `siegelLower`
   (`src/Formalism/LandauZeroFreeBounds/FinalSiegel.lean:17`) is [Lean].
2. `PNTAPRelW` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MeanSquareHypWIff.lean:38`) is the prime number theorem in progressions modulo
   $M$ with $8 \mid M$, in relative form with an optional exceptional pair $(\chi_1, \beta_1)$:
   $$\lvert \pi(X; M, b) - \mathrm{main}(X) \rvert \le A_0\bigl(e^{-c_3\log X/\log M} + e^{-\sqrt{c_3 \log X}}\bigr)\mathrm{main}(X)$$
   once $C_0 \log M \log(\log M + 2) \le \log X$. Its proof term `pnt_progressions_relative_weak_holds`
   (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:22`) is a one-line assembly of the smoothed explicit formula, a log-density
   bound and a Deuring–Heilbronn step (`:23–24`) [Lean].
3. `count_a` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean:346`) derives
   $\lvert \mathrm{PPset}(m_0, a_0, X) \rvert \ge X^{9/10}$ under the hypotheses of Proposition 4.5. Its proof
   instantiates `ExcBound` only at $\varepsilon = 1$, i.e. $\beta \le 1 - c_0/m_0$ (`:352`, `:380–385`). The counting itself
   is delegated to `count_pos` (`:275`), proved in §4.9 [Lean, read]. The PNT package calls `excBound` again internally, for
   example at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DeuringHeilbronnFinishTuran.lean:19` with $\varepsilon = 1/2$. We have not read those files.

**Statement 4.18 (the contour tail; `tail_contour`, `box_tail_bound`).**
`tail_contour` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContour.lean:14`) states the following. For $0 < \delta \le 1/800$ there is $K \ge 0$ such that for
every non-principal $\chi \bmod N$ with $2 \le Q$, $N \le Q$ and no zero in $\mathcal B(Q)$, and every
$z \ge 1$, $0 < \eta \le 1$:
$$\Bigl\lVert S_\chi(z + z\eta) - S_\chi(z) - z\eta\,\Bigl(-\frac{L'}{L}(1, \chi)\Bigr) \Bigr\rVert
\le K\log Q\Bigl(\log Q \cdot \eta\,z^{1 - 1/400 + \delta} + \frac{z^2}{Q}\Bigr),$$
where $S_\chi(y) = \sum_{n \le y} \Lambda(n)\chi(n)(y/n - 1)$
(`Schi`, `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:11`) [Lean].

We read the top-level proof (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContour.lean:19–135`). It moves the Perron integral of
$-\frac{L'}{L}(w)\,y^w/(w(w-1))$ to $\Re w = 1 - 1/400 + \delta$ at height $T = Q/2$ (`:26`, `:44–45`). It then
bounds the two vertical tails (`:53–64`), the horizontal segments (`:66–85`) and the shifted
vertical line (`:87–105`). Section 4.8 reads the conditional estimate and identifies the deeper suppliers still at R2.

`box_tail_bound` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailFinal.lean:13`) packages the same estimate at $z = x^{400}$, $\eta = x^{-2}$ for
`GoodFor` characters (`src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:47`). That predicate includes $\chi^2 = 1$. Its proof (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailFinal.lean:14–101`) is
read [Lean, read], while its inputs `tail_contour`, `tail_mertens`, `tail_num` and `tail_diff_schi` remain [Lean].
Chapter 4's route does not pass through `box_tail_bound`. `tailK` and `kappa4` call `tail_contour` directly
(`src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:102`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean:46`), for all non-principal
primitive characters. `box_tail_bound` is consumed through `box_tail_bound_all`
(`src/Formalism/GL3MeanSquares/HookFormulaTorsion/BoxCountOfZeroDensity.lean:10`) in `src/Formalism/LocalToGlobal/GlobalTheory/AnalyticConclusionOfProp25.lean:261`.

### 4.7.6 Remarks

**Quantifiers and constants, Lean versus the classical statements.**

| Step | Lean (polarity and constants) | Classical counterpart | Tag |
|---|---|---|---|
| Zero density | $\exists C\ \forall Q \ge 3\ \forall S$ finite: $\lvert S \rvert \le CQ^{1/4}$; counts primitive characters with a zero, $\zeta$ included | $\sum_{q \le Q}\sum^{\ast}_\chi N(\sigma, T, \chi) \ll (Q^2T)^{5(1-\sigma)/2}(\log QT)^{c}$ counts zeros [Montgomery1969]; exponent $12/5$ in place of $5/2$ [Huxley1975] | [Lean, read] |
| Duality | row-sum bound $\Delta$ for every $i \in S$ | $\max_r \sum_s \lvert \langle \varphi_r, \varphi_s \rangle \rvert$ [Bombieri1971] | [Lean, read] |
| Off-diagonal | $2qq'(1 + \lvert w \rvert) \le 8Q^3$, trivial complete-sum bound | large sieve $\ll (N + Q^2)\sum \lvert a_n \rvert^2$ [Bombieri1965; Montgomery1968; Davenport2000, Ch. 27], not used | [Lean, read] |
| Coefficients | $d(n) \le C n^{1/400}$, block mass $\le C^2U^{-197/200}$ | $d(n) \ll_\varepsilon n^\varepsilon$ | [Lean, read] |
| Detection | $Y = \lceil Q \rceil^4$, $N = 2^J \ge \lceil Q \rceil^8$, threshold $1/(2J)$ | mollifier $M_X(s) = \sum_{d \le X}\mu(d)d^{-s}$ [Montgomery1971] | [Lean, read] |
| Landau–Page | $c_0 = c/3$, moduli $\le Z$, lifted to $M_1M_2 \le Z^2$ | at most one exceptional real character [Page1935] | [Lean, read] given `ZFRDirichlet` |
| Siegel | $\forall \varepsilon > 0\ \exists c > 0$, ineffective; `count_a` uses $\varepsilon = 1$ | $L(1, \chi) \gg_\varepsilon q^{-\varepsilon}$ [Siegel1935] | [Lean] |

**Why the exponent is $1/4$.** Because off-diagonal terms are bounded trivially by $8Q^3$, the
mollified polynomial must start beyond $Y = Q^4$. Only there does the diagonal term $U$ dominate the
off-diagonal total $8Q^3\lvert T \rvert$ weighted by the coefficient mass $U^{-197/200}$. The price is
$U^{3/200}$ with $U$ up to $Q^{12}$, plus three powers of $J \asymp \log Q$. This gives $Q^{0.18 + 0.07}$.
A large-sieve treatment of the same blocks would give an exponent proportional to $1 - \sigma$. The
archive needs neither: $Q^{1/4} \le U^{3/8}$ is already negligible against $U^{9/10}$ [Expository].

**Effectivity.** Every constant in Theorem 4.15 is effective. $Q_0$ comes from two
$\log$-versus-power comparisons, $C$ from the divisor bound, and the small-$Q$ case from a finite
count of characters. Lean extracts $Q_0$ from an `IsLittleO` statement, which is existential in
form, but no ineffective input is used. In the files we have read, ineffectivity enters only through
`excBound`, that is, Siegel's theorem. As Remark 4.5.1(2) explains, the existential form of
`HasWindows` makes this harmless [Expository].

**What is now `R3` and what is still `R2`.**

- **R3 (`[Lean, read]`)**, read down to Mathlib: `CountSt`; the nine `CountZ*` files `CountZDefs`,
  `CountZDual`, `CountZPair`, `CountZTwist`, `CountZMoll`, `CountZDetect`, `CountZBlock`,
  `CountZNum`, `CountZFinal`; `CountZAll`; and the direct dependencies `DivisorBound.lean`,
  `src/Formalism/LFunctionBounds/PositivityBound.lean:51,62`, `LPartialSum.lean`, `LFunctionEqGOfOneLt.lean` and
  `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:10–51`. Also `MSqPage.lean` (`page_across`, conditional on `ZFRDirichlet`) and the
  proof body of `box_tail_bound` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailFinal.lean:13–101`).
- **R2 (`[Lean]`)**: the full `tail_contour` closure (see §4.8.6 for the individual suppliers and the locally read proof bodies); `TailDiff`,
  `TailMertens` and `TailNum`; the PNT package behind `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:22` (`PNTRangeA`, `PNTGlue`,
  `PrimeCountOfPsi`, `PNTSharp`, `PNTBAsm`, `PNTZSum`, `PNTDens`, `PNTExplMain`, `PNTZSumL`,
  `PNTDHB` and their imports); `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwist.lean:27–229`
  with `MSqTwistB` and `MSqTwistC`; `FinalSiegel`, `ExcBoundOf` and `LDerivNearOne` behind `excBound`; and
  `NoZeroComplex` behind `zFRDirichlet`. Sections 4.10 and 4.10.5–4.10.8 later read parts of the PNT package (local R3).

## 4.8 From the zero-free box to the truncated Perron tail

### 4.8.1 Motivation

A smoothed prime sum can be recovered by integrating a logarithmic derivative against a kernel. The factor $1/(s(s-1))$ gives quadratic decay high on the original vertical line. Moving the finite part of that line to the left crosses the kernel pole at $1$ and lowers the exponent of $y$ in $y^s$. When two endpoints are close, subtract their integrands *before* estimating the new vertical integral. The numerator difference supplies the short-interval factor $\eta$, while cancelling one denominator factor in the bound. The resulting integral has logarithmic growth in the truncation height. The original tails and the horizontal segments still have both denominator factors.

### 4.8.2 A parameter example [Expository]

Take $N=3$, $Q=20$, $\delta=1/800$, $z=1$ and $\eta=1/2$. Use the non-principal character modulo $3$ and take its zero-free box as a hypothesis for this example. Then $y_0=1$, $y_1=3/2$, $T=10$ and $\sigma=799/800$. The contour is $1/800$ from the strict left edge of the box and $1/800$ from the kernel pole. At the top edge the local zero disc can reach height $10+11/60=611/60<20$. The horizontal span is $801/800$, and the pointwise majorant at $y_1$ on either horizontal side is $9M/400$, where $M=K_B\log 20$. At the real-axis crossing of the shifted line, $u=0$ gives $1/|\sigma-1|=800$. The bound for the paired left integrals in the proof below is $8M\log 8001$. The two terms inside the final parentheses become $(\log 20)/2$ and $1/20$. These substitutions describe the geometry and the bounds under the stated analytic hypotheses.

### 4.8.3 Definitions and analytic inputs

Write $L(s)=L(s,\chi)$, $D(s)=-L'(s)/L(s)$ and
$$
S_\chi(y)=\sum_{1\le n\le y}\Lambda(n)\chi(n)(y/n-1),\qquad
F_y(s)=\frac{D(s)y^s}{s(s-1)}.
$$
The sum weight is the smoothed Perron weight $(a-1)$ for $a=y/n\ge1$, and zero for $0<a<1$. The kernel explanation is that a vertical integral of $a^s/(s(s-1))$ to the right of $1$ closes to the left for $a>1$, giving residues $a$ and $-1$ at $1$ and $0$. For $a<1$ one closes to the right, with no poles. At $a=1$ the two residues cancel and the weight is zero; the kernel's quadratic decay makes the vertical integral continuous in $a$ on compact subintervals of $(0,\infty)$. The archive supplies the integrable character formula on $\Re s=2$, namely $2\pi S_\chi(y)=\int_{\mathbb R}F_y(2+it)\,dt$ for $y\ge1$. This formula and the rectangle shift are analytic inputs [Lean]. The definitions are at §4.8.6.

Let $\mathcal B(Q)$ mean $L(s)\ne0$ whenever $\Re s>1-1/400$ and $|\Im s|\le Q$. Set $\sigma=1-1/400+\delta$, $T=Q/2$ and $\ell=\log Q$. In the following proof $0<\delta\le1/800$, so $\sigma$ lies strictly inside the box and $g=1-\sigma=1/400-\delta\ge1/800$. For $Q\ge2$, $0<T\le Q-1$. These are two different margins: $\delta$ separates the shifted contour from nearby zeros, while $g$ separates it from the kernel pole.

### 4.8.4 Lemma (the box supplies a bound for the numerator)

**[Lean, read] conditional on the polynomial-growth, local Landau and right-half-plane inputs.** For fixed $\delta>0$ there is $K_B\ge0$ such that, if $1\le N\le Q$, $Q\ge2$, $\chi$ is non-principal and has $\mathcal B(Q)$, then $|D(s)|\le K_B\ell$ for $\Re s\ge1-1/400+\delta$ and $|\Im s|\le Q-1$.

**Proof.** Use the polynomial-growth bound $|L(w)|\le C N(1+|w|)$ for $\Re w\ge1/2$, the inverse bound $1/|L(w)|\le\Re w/(\Re w-1)$ for $\Re w>1$, and the right-side bound $|D(w)|\le1/(\Re w-1)+C_R$ there, with $C_R\ge0$. If $\Re s\ge11/10$, the last inequality gives $|D(s)|\le10+C_R\le (10+C_R)\ell/\log2$.

Otherwise $26/27\le\Re s<11/10$ and $L(s)\ne0$ by the box. Put $t=\Im s$, $c=21/20+it$, $r=11/20$ and $X=N(|t|+2)$. The disc of radius $r$ about $c$ lies in $\Re w\ge1/2$ and $1+|w|\le2(|t|+2)$ there by the triangle inequality. At $c$ the inverse bound gives $1/|L(c)|\le21$ (the center is nonzero in $\Re w>1$). Thus on the disc $|L(w)|\le H|L(c)|$ for $H=2\cdot21(|C|+1)X\ge1$. Non-principality supplies holomorphy. The local Landau input supplies the zeros $Z$ in the closed disc of radius $r/3$, with nonnegative integer weights $m_\rho$ whose sum is at most $\log H/\log2$. At nonzeros in the closed disc of radius $r/6$ it bounds the error after subtracting $\sum_{\rho\in Z}m_\rho/(s-\rho)$ from $L'(s)/L(s)$ by $72\log H/r$. The real-part range above ensures $|s-c|\le r/6$.

Each $\rho\in Z$ has $|\Im\rho|\le |t|+r/3<Q$. Since the box excludes zeros strictly to the right of $1-1/400$, every such $\rho$ satisfies $\Re\rho\le1-1/400$ and $|s-\rho|\ge\delta$. Triangle inequality and $\delta>0$ bound the zero sum by $\log H/(\delta\log2)$. For $X\ge2$, set $A_0=1+\log(2\cdot21(|C|+1))/\log2$ so that $\log H\le A_0\log X$. Also $X\le Q(Q+1)\le Q^3$ by $N\le Q$, $|t|\le Q-1$ and $Q\ge2$. Combining the two triangle bounds gives the claimed estimate with
$$
K_B=3A_0\left(\frac{1440}{11}+\frac{1}{\delta\log2}\right)
         +\frac{10+C_R}{\log2}.
$$
Both summands are nonnegative, so this constant serves in either real-part range. A zero on the allowed box edge would make $|s-\rho|=\delta$ when the heights coincide. At $\delta=0$ this separation argument loses its finite majorant.

### 4.8.5 Theorem (conditional truncated tail bound)

**[Lean, read] for the estimate given its analytic inputs.** Fix $0<\delta\le1/800$. Suppose $1\le N\le Q$, $Q\ge2$, and $\chi$ is non-principal with $\mathcal B(Q)$. Assume the analytic inputs of the box lemma. Section 4.8.7 supplies the Perron identity and the empty-zero rectangle shift used below, and §4.8.8 supplies the box lemma's local Landau, inverse and right-half-plane inputs. Then for $z\ge1$ and $0<\eta\le1$,
$$
|S_\chi(z+z\eta)-S_\chi(z)-z\eta D(1)|
 \le K\ell\left(\ell\eta z^\sigma+\frac{z^2}{Q}\right),\qquad
 K=160K_B+32(1+C_R).
$$
Here $K$ depends on $\delta$ and the uniform analytic constants, and works for every such $N,\chi,Q,z,\eta$.

**Proof.** Let $y_0=z$, $y_1=z(1+\eta)$, so $1\le y_j\le2z$. For either $y=y_j$, write $E_y$ for the integral of $F_y(2+it)$ over the complement of $(-T,T]$, $H_y^\pm=\int_\sigma^2 F_y(x\pm iT)\,dx$ and $V_y=\int_{-T}^T F_y(\sigma+iu)\,du$. The closed rectangle $[\sigma,2]+i[-T,T]$ lies in the box. The rectangle shift input applies for non-principal $\chi$, $y>0$, $0<\sigma<1<2$, $T>0$, and no zeros anywhere on or inside the rectangle. The pole of the kernel at $1$ contributes residue $yD(1)$ and $0$ lies outside. With counterclockwise orientation the bottom edge runs right, the right edge up, the top edge left and the left edge down. Splitting the original Perron integral gives
$$
2\pi(S_\chi(y)-yD(1))=E_y+i(H_y^- -H_y^+)+V_y .
$$
The absolute integrability in the original Perron identity permits the split; finite endpoints make no difference to these integrals.

**Left edge.** Put $M=K_B\ell$. For $|u|\le T$, $s=\sigma+iu$ has $|D(s)|\le M$. For real $w\in[z,y_1]$, differentiation along the positive axis gives $(w^s)'=s w^{s-1}$. Since $0<\sigma<1$ and $w\ge z>0$, the derivative has norm at most $|s|z^{\sigma-1}$. Integration over length $z\eta$ yields
$$
|y_1^s-y_0^s|\le |s|\eta z^\sigma,\qquad
|F_{y_1}(s)-F_{y_0}(s)|\le \frac{4M\eta z^\sigma}{|s-1|}.
$$
Here $s\ne0,1$, so $|s|$ cancels. The displayed majorant keeps the factor $4$ used by the formal proof, by nonnegativity. The integrands are continuous on this compact segment since $L$ has no zeros there and neither kernel denominator vanishes. The two coordinate lower bounds give $|s-1|\ge\max(g,|u|)\ge(g+|u|)/2$ with $g>0$. The integral of $2/(g+|u|)$ is $4\log(1+T/g)$ by evenness and the antiderivative of $1/(g+u)$ for $u\ge0$. Since $g\ge1/800$, this is at most $4\log(1+800T)$. Finally $1+800T=1+400Q\le512Q\le Q^{10}$ for $Q\ge2$. Taking the norm after subtracting gives $|V_{y_1}-V_{y_0}|\le160K_B\ell^2\eta z^\sigma$.

**Horizontal edges.** For $\sigma\le x\le2$ and $|v|=T>0$, the box bound gives $|D(x+iv)|\le M$. The modulus of the power is $y^x\le y^2$ since $y\ge1$. Both denominator factors have modulus at least $T$, their common absolute imaginary part. Hence $|F_y(x+iv)|\le My^2/T^2$. Integrating a continuous function over a span $2-\sigma\le2$ gives
$$
|H_y^\pm|\le \frac{8Mz^2}{T^2}=\frac{32Mz^2}{Q^2}\le\frac{16Mz^2}{Q}.
$$
The last step uses $Q\ge2$. The span is approximately one, whereas the box width enters through the left endpoint $\sigma$ and the exponent $z^\sigma$.

**Original right tails.** On $\Re s=2$ the right-half-plane bound gives $|D(s)|\le1+C_R$ for all heights. For $|t|\ge T>0$, both denominator moduli are at least $|t|$, so $|F_y(2+it)|\le B/t^2$ with $B=4(1+C_R)z^2$. The archive uses the positive majorant $2B/(T^2+t^2)$ on this set, valid because $t^2\ge T^2$. Its integral over the whole real line is $2\pi B/T$ by the arctangent integral and $T>0$. Thus $|E_y|\le 2\pi\cdot8(1+C_R)z^2/Q$. The height restriction of the box plays no role in the right-half-plane bound for $|t|>T$.

**Assembly.** Subtract the two shift identities, use $y_1-y_0=z\eta$ and take the triangle inequality with $|i|=1$. There are two right tails, four horizontal terms and one paired left difference. After dividing by $2\pi>0$ and using $2\pi\ge1$ on the nonnegative horizontal and left bounds, the result is at most
$$
16(1+C_R)\frac{z^2}{Q}
 +64K_B\ell\frac{z^2}{Q}+160K_B\ell^2\eta z^\sigma .
$$
Now $\ell\ge\log2\ge1/2$ (integrate $1/x\ge1/2$ over $[1,2]$), so $16(1+C_R)\le32(1+C_R)\ell$. The stated $K$ dominates both coefficients after factoring out $\ell$. This proves the bound on the stated domain.

### 4.8.6 Source map and reading boundary

All paths below are relative to the joined Alpöge archive with SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`
([SOURCES, §1](../sources/SOURCES.md#1-the-lean-archive-primary-source)).

| Step | Archive declaration and proof |
|---|---|
| Box, sum and kernel definitions | `src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:44–45`; `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:11–20,28–36`; `src/Formalism/LandauZeroFreeBounds/NoZeroComplexOf.lean:10–11` |
| Local disc and its input | `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LandauLemmaLfunctionZeros.lean:9–91`; `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:57–68` |
| Separation and uniform box bound | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailBox.lean:13–119` |
| Shift identity and its orientation | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourA.lean:11–35` |
| Derivative of the power difference and integrated left edge | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean:10–99,157–244` |
| Horizontal and original right pointwise bounds | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean:101–155` |
| Right-tail integral | `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormIntegralComplLe.lean:9–43` |
| Combining the seven contributions and absorbing the logarithm | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean:246–271`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContour.lean:19–135` |

**Which kernel is consumed?** `TailKernel.lean` is imported both directly and through `TailContourB`. Its `tail_kernel_cpow` and `tail_kernel_line` prove closely related bounds at
`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean:27–64,89–124`. The actual consumer at `TailContour.lean:87–89` calls `tc_left_int`, which calls `tc_left_pt` and integrates $2/(g+|u|)$ directly. `tc_left_pt` differentiates $w^s$ on a real interval. The separately imported `perron_horizontal_segment_bound` in `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean:71–121` belongs to a different estimate with a zero-free region and an optional exceptional zero. The horizontal consumer here is `tc_horiz_pt`.

**Remaining R2 [Lean].** The proof bodies of `TailContourA` and the consumed declarations of `TailContourB` are read locally. Section [4.8.7.6](#4876-source-map-and-reading-boundary) records the local R3 reading of `perron_formula_character` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean:283`), `rectangle_contour_shift_character` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RectShiftChi.lean:114`) and their direct suppliers. On the box side [§4.8.8](#488-local-zeros-and-the-logarithmic-derivative-in-tailbox) reads the local Landau expansion, the inverse bound `inverseBound` and the right-half-plane bound `l_log_deriv_right` through their direct production proofs, while [§4.10.9](#4109-uniform-polynomial-growth-in-the-half-plane-lfunction_polynomial_growth-and-exlf_growth) reads the polynomial-growth input `lfunction_polynomial_growth` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:53–71`) at local R3. The local zeta Laurent remainder and its right-half-plane transfer are read in [§4.10.10](#41010-the-pole-subtracted-zeta-logarithmic-derivative). Deeper analytic dependencies retain R2 [Lean]. The unused Perron horizontal provider and the standalone kernel lemmas receive no promotion from this reading. The complete imported proof of `tail_contour` remains R2. The conditional proof here reads one estimate with its analytic inputs exposed.

### 4.8.7 Mellin inversion and the finite rectangle

#### 4.8.7.1 Motivation

The tail estimate of §4.8 starts from a smoothed von Mangoldt sum at two nearby arguments. To move its integral across $1$, we need the precise kernel, pointwise inversion, and the residue on the way across. Smoothing makes the weight continuous at each integer and gives two powers of decay on the original line. At $1$ the kernel can contribute a residue for a non-principal character. For the principal character the pole of $L$ increases the order of the singularity.

#### 4.8.7.2 Two character calculations [Expository]

**Principal character modulo $2$.** At $y=5$ the only contribution is from $3$. The character kills $2$ and $4$, $\Lambda(1)=0$, and $5$ has weight zero. Thus $S_{\chi_0}(5)=2\log 3/3$. Here $L(s,\chi_0)=\zeta(s)(1-2^{-s})$. For $w=s-1$ the factors expand as $w^{-1}+\gamma+O(w)$ and $1/2+w\log 2/2+O(w^2)$, where $\gamma$ is Euler's constant. Thus $wL(1+w,\chi_0)=\tfrac12(1+(\gamma+\log 2)w+O(w^2))$. Its logarithmic derivative gives $D(1+w)=w^{-1}-\gamma-\log 2+O(w)$, where $D=-L'/L$. Multiplying by $5^{1+w}/((1+w)w)$ gives
$$
F_5(1+w)=\frac5{w^2}+\frac{5(\log(5/2)-1-\gamma)}w+O(1).
$$
On a rectangle satisfying the theorem below, the boundary integral divided by $2\pi i$ is $5(\log(5/2)-1-\gamma)$. The shifted line, horizontal edges, and truncation supply the difference between this number and $2\log 3/3$.

**Non-principal character modulo $3$.** Take $\chi(1)=1$, $\chi(2)=-1$, and $\chi(0)=0$ on residue classes. At $y=5$ the terms at $2,4,5$ give $-\tfrac32\log 2+\tfrac14\log 2+0$, hence $S_\chi(5)=-\tfrac54\log 2$. Grouping the series into pairs gives
$$
L(1,\chi)=\sum_{k\ge0}\left(\frac1{3k+1}-\frac1{3k+2}\right)
=\int_0^1\frac{dx}{1+x+x^2}
=\left[\frac2{\sqrt3}\arctan\frac{2x+1}{\sqrt3}\right]_0^1
=\frac{\pi}{3\sqrt3}.
$$
In the integral the summed terms are $x^{3k}(1-x)\ge0$. The paired Dirichlet series is locally uniformly convergent on $\Re s>0$, since each pair equals $s\int_{3k+1}^{3k+2}u^{-s-1}\,du$. Differentiating at $1$ gives
$$
L'(1,\chi)=\sum_{k\ge0}\left(
 \frac{\log(3k+2)}{3k+2}-\frac{\log(3k+1)}{3k+1}\right).
$$
This derivative series converges absolutely by integrating the derivative of $(\log u)/u$ over the same unit intervals. Since $5^{1+w}/(1+w)=5+O(w)$, multiplication by $D(1+w)/w$ gives the residue
$$
R_\chi(5)=\frac{15\sqrt3}{\pi}\sum_{k\ge0}
 \left(\frac{\log(3k+1)}{3k+1}-\frac{\log(3k+2)}{3k+2}\right).
$$
The calculation establishes nonvanishing at $1$. The boundary identity below also assumes nonvanishing throughout the rectangle.

#### 4.8.7.3 Definitions and the Mellin production lemma

For a character $\chi$ modulo $N\ge1$, use $a_n=\Lambda(n)\chi(n)$ for $n\ge1$, $D(s)=-L'(s,\chi)/L(s,\chi)$, and
$$
k(u)=\max(u-1,0),\qquad S_\chi(y)=\sum_{n\ge1}a_n k(y/n),\qquad
F_y(s)=\frac{D(s)y^s}{s(s-1)}.
$$
For $y>0$ use $y^s=\exp(s\log y)$. The sum is locally finite, continuous and zero for $0<y\le1$. At an integer $m$ the entering term has weight zero, so the cutoffs $n<m$ and $n\le m$ agree and inversion uses the ordinary value at $m$.

**Lemma 4.8.7.3 (smoothed inversion) [Lean, read] for the convergence and the inversion identity; the tail majorant is [Expository].** Assume the identity $D(s)=\sum_{n\ge1}a_n n^{-s}$ for $\Re s>1$. For $y\ge1$, $c>1$ and $T>0$,
$$
S_\chi(y)=\frac1{2\pi}\left(\int_{-T}^T F_y(c+it)\,dt+E_y\right),\qquad
E_y=\int_{\mathbb R\setminus(-T,T]}F_y(c+it)\,dt.
$$
The full-line integral is absolutely convergent and $|E_y|\le 2A(c)y^c/T$, where $A(c)=\sum_{n\ge1}\Lambda(n)n^{-c}$. The archive's `perron_formula_character` proves the convergence and the identity. The tail majorant is our derivation from the quadratic decay; the archive's consumers bound the tail with their own constant, $1+C_R$ in §4.8.5.

**Proof.** The Mellin exponent here is $-s$. For $n\ge1$ and $\Re s>1$, integrate the two powers on the support:
$$
\int_0^\infty k(x/n)x^{-s-1}\,dx
=\int_n^\infty(n^{-1}x^{-s}-x^{-s-1})\,dx
=n^{-s}\left(\frac1{s-1}-\frac1s\right)=\frac{n^{-s}}{s(s-1)}.
$$
The same computation for $c=\Re s$ gives an integrated absolute majorant
$$
\sum_{n\ge1}\int_0^\infty |a_n|k(x/n)x^{-c-1}\,dx
=\sum_{n\ge1}\frac{|a_n|n^{-c}}{c(c-1)}
\le\frac{A(c)}{c(c-1)}<\infty .
$$
Here $|\chi(n)|\le1$ and $\Lambda(n)\le\log n$. Absolute summability of the integrals permits the exchange with the sum and yields
$$
\mathcal M S_\chi(-s)=\int_0^\infty S_\chi(x)x^{-s-1}\,dx
=\frac{D(s)}{s(s-1)}.
$$
The formal producer uses the real majorant and the complex power integral for a general real coefficient sequence dominated by a multiple of $\Lambda$. The character proof applies it to $\Lambda(n)\Re\chi(n)$ and $\Lambda(n)\Im\chi(n)$ and recombines the two. The auxiliary index $0$ has coefficient zero.

On $\Re s=c$, $|D(s)|\le A(c)$. Each squared denominator modulus is at least $d_c(1+t^2)$ for $d_c=\min(1,(c-1)^2)$, so $|s(s-1)|\ge d_c(1+t^2)$. This gives integrability of the Mellin transform along the vertical line and of $F_y(c+it)$. With $u=\log x$, the function $g(u)=e^{-cu}S_\chi(e^u)$ is integrable by the first majorant. Its Fourier transform with kernel $e^{-itu}$ is $\mathcal M S_\chi(-c-it)$ and is also integrable. Fourier inversion at the continuous point $\log y$ gives
$$
S_\chi(y)=\frac1{2\pi}\int_{\mathbb R} y^{c+it}\mathcal M S_\chi(-c-it)\,dt.
$$
The archive starts on the line $-c+it$ and reflects $t$ to $-t$. Contour notation on the right line has $ds=i\,dt$, giving the same factor $1/(2\pi)$ from $1/(2\pi i)$. Split at $(-T,T]$, whose endpoints have measure zero. For $|t|\ge T$ both denominator moduli are at least $|t|$. Integrating $A(c)y^c/t^2$ on the two tails gives $2A(c)y^c/T$.

#### 4.8.7.4 The conditional shift theorem

**Theorem 4.8.7.4 (Perron inversion across an empty zero rectangle).** Under the Dirichlet-series assumption of Lemma 4.8.7.3, take $0<\sigma<1<c$, $T>0$, and $y\ge1$. Write $\mathcal R=[\sigma,c]+i[-T,T]$. Assume one of the following:

- For a non-principal character, $L(s,\chi)$ is holomorphic on a neighborhood of $\mathcal R$ and nonzero everywhere on $\mathcal R$. Put $R_\chi(y)=yD(1)$.
- For the principal character $\chi_0$ modulo $N$, take $L(s,\chi_0)=\zeta(s)\prod_{p\mid N}(1-p^{-s})$. Assume $\zeta$ is meromorphic on a neighborhood of $\mathcal R$, with its only pole on $\mathcal R$ at $1$, where $\zeta(1+w)=w^{-1}+\gamma+O(w)$, and is nonzero on $\mathcal R\setminus\{1\}$. Put
  $$
  R_{\chi_0}(y)=y\left(\log y-1-\gamma-\sum_{p\mid N}\frac{\log p}{p-1}\right).
  $$

Write $H_y^\pm=\int_\sigma^c F_y(x\pm iT)\,dx$, $V_y=\int_{-T}^T F_y(\sigma+it)\,dt$, and $M_\pm=\max_{\sigma\le x\le c}|D(x\pm iT)|$. Then
$$
2\pi(S_\chi(y)-R_\chi(y))=V_y+i(H_y^--H_y^+)+E_y
$$
and
$$
\left|S_\chi(y)-R_\chi(y)-\frac{V_y}{2\pi}\right|
\le\frac{y^c}{2\pi}
\left(\frac{(c-\sigma)(M_-+M_+)}{T^2}+\frac{2A(c)}{T}\right).
$$
The non-principal identity is [Lean, read] for the empty zero set. The principal calculation for general $N$ is [Expository].

**Proof.** The point $0$ lies outside $\mathcal R$ and $1$ lies strictly inside. For a non-principal character, nonvanishing and continuity give a holomorphic quotient $D$ on a neighborhood of the closed rectangle. Set $h(s)=D(s)y^s/s$. Subtracting $h(1)/(s-1)$ from $F_y$ leaves the difference quotient of $h$, holomorphically extended by $h'(1)$ at $1$. Thus the residue is $h(1)=yD(1)$, with a removable singularity if $D(1)=0$.

For the principal character put $G(s)=(s-1)L(s,\chi_0)$. Each Euler factor is nonzero for $\Re s>0$ because $|p^{-s}|<1$. Then $G(1)=\prod_{p\mid N}(1-p^{-1})\ne0$, including the empty product for $N=1$. Logarithmic differentiation of the product and the Laurent expansion give
$$
\frac{G'(1)}{G(1)}
=\gamma+\sum_{p\mid N}\frac{(\log p)p^{-1}}{1-p^{-1}}.
$$
Near $1$ we have $D(1+w)=w^{-1}-G'(1)/G(1)+O(w)$ and $y^{1+w}/(1+w)=y+y(\log y-1)w+O(w^2)$. Multiplying and dividing by $w$ gives
$$
F_y(1+w)=\frac{y}{w^2}+
      \frac{y(\log y-1-G'(1)/G(1))}{w}+O(1).
$$
Subtracting both principal-part terms leaves a holomorphic extension across $1$. The integral of $(s-1)^{-2}$ on the closed boundary vanishes by the primitive $-(s-1)^{-1}$.

In either case Cauchy's theorem removes the holomorphic remainder. For the positively oriented rectangle, the integral of $1/(s-1)$ is $2\pi i$. To see the archive's computation, use the principal logarithm of $s-1$ along the bottom, right and top and the principal logarithm of $-(s-1)$ on the left. The first three increments telescope to the top-left log minus the bottom-left log. Including the downward left edge leaves the difference of the log-minus-log-of-negative values at the two left corners. These values are $i\pi$ at the upper corner and $-i\pi$ at the lower one. Thus
$$
H_y^- - H_y^+ + i\int_{-T}^T F_y(c+it)\,dt-iV_y
=2\pi iR_\chi(y).
$$
Divide by $i$ and use the inversion split to obtain the identity. For either horizontal edge, the span is $c-\sigma$, the power has modulus at most $y^c$, and the two denominator factors have modulus at least $T$ each. This gives $|H_y^\pm|\le(c-\sigma)M_\pm y^c/T^2$. Combining these with the tail bound proves the error inequality. The edge constants depend on the actual horizontal bounds on $D$. At fixed $c$, $A(c)$ is uniform in the character and modulus. It can grow as $c$ approaches $1$, and the full-line integrability majorant additionally costs $d_c^{-1}$. The statement is at a finite height with controlled edges.

#### 4.8.7.5 Return to the tail consumer

At the actual calls the right line is $c=2$ and the finite set of real zeros supplied to the rectangle theorem is empty. The formal shift adjoins $1$ to that set to construct the candidate poles, leaving $\{1\}$ in this call. Its open neighborhood here is the right-half-plane nonvanishing locus, and its regularized integrand is obtained by subtracting the one principal part and filling in the punctured limit at $1$. The empty-set simplification removes the zero sum.

For the parameters of §4.8, $\sigma=1-1/400+\delta$ and $T=Q/2$, the positive real-part margin places even the boundary inside the given zero-free box. Apply the non-principal identity at $y_0=z$ and $y_1=z+z\eta$. The difference of residues is exactly $z\eta D(1)$ and the contribution to $2\pi$ times the residue-subtracted sum is
$$
(E_{y_1}-E_{y_0})+
 i\big((H_{y_1}^--H_{y_0}^-)-(H_{y_1}^+-H_{y_0}^+)\big)
 +(V_{y_1}-V_{y_0}).
$$
This is the input to §4.8.5. The box supplies the four horizontal bounds, the original line supplies two truncation bounds, and the shifted vertical integrals are estimated as a pair. For a principal character the same subtraction would produce the residue difference
$$
z\eta\left(\log z-1-\gamma-\sum_{p\mid N}\frac{\log p}{p-1}\right)
+z(1+\eta)\log(1+\eta).
$$
The archived tail estimate uses the linear, non-principal residue.

#### 4.8.7.6 Source map and reading boundary

Archive paths are relative to A2, joined SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
The Mellin conventions also appear in DLMF §2.5(i), equations (2.5.1)–(2.5.2). [A2 source record](../sources/SOURCES.md#1-the-lean-archive-primary-source) · [DLMF §2.5(i)](https://dlmf.nist.gov/2.5#i)

| Step | Source and reading scope |
|---|---|
| Definitions and interfaces | `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:11–36`; `src/Formalism/LandauZeroFreeBounds/NoZeroComplexOf.lean:10–11`; `src/Formalism/DefsOC.lean:10`. |
| Real and complex kernel production and sum–integral interchange | Local R3 for `src/Formalism/ZetaNonvanishing/MellinSAux.lean:9–154` and `src/Formalism/ZetaNonvanishing/MellinSgen.lean:13–172`. |
| Character series, domination, continuity, transform and inversion | Local R3 for `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean:15–305`, including `perron_formula_character` at line 283. Direct continuity and denominator lemmas in `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean:44–46,119–143`. |
| Inversion by logarithmic change of variables | Mathlib's `Mathlib/Analysis/MellinInversion.lean:49–124`, read at the A2 manifest pin. Fourier inversion is an input. |
| Holomorphic extension and residue assembly | Local R3 for `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RectShiftChi.lean:10–239`, including `rectangle_contour_shift_character` from line 114. The textbook argument uses the empty-zero branch. Its direct residue supplier `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean:9–186` is read locally; its statement `RectResidue` and the contour integral `FX.rectInt` are defined at `src/Formalism/LFunctionBounds/ExpSumLowerBound.lean:34–43`. |
| Orientation and consumer instantiation | `src/Formalism/ZeroFreeRegion/SmallHeightLogDeriv.lean:9–11`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourA.lean:20–35`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContour.lean:24–48,87–89`. |
| Zeta specialization of the principal calculation | `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LaurentAtOne.lean:8–89` and `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectShiftOf.lean:32–88`. The latter uses the separate `rectangle_double_pole` supplier in `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean:103`, read in §4.10.8. |

**Retained inputs.** At depth, Mathlib supplies `DirichletCharacter.LSeries_twist_vonMangoldt_eq`, `DirichletCharacter.LFunction_eq_LSeries`, `DirichletCharacter.LSeries_ne_zero_of_one_lt_re`, `ArithmeticFunction.LSeriesSummable_vonMangoldt`, `integral_Ioi_cpow_of_lt`, `integral_Ioi_rpow_of_lt`, `integral_tsum_of_summable_integral_norm`, `Integrable.fourierInv_fourier_eq`, `DirichletCharacter.differentiable_LFunction`, `DirichletCharacter.LFunction_apply_one_ne_zero`, `Complex.differentiableOn_dslope` and `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. The principal analogue also uses the zeta Laurent input `log_deriv_riemannZeta_eq_neg_inv_sub_add`, the zeta residue at $1$, and the principal Euler-factor identity. The transitive proofs remain outside the local R3 reading. For the real-zero correction see the statement of `RectShiftChi` and the conditional `smoothed_character_sum_of` assembly (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SmoothChiOf.lean:9`). The zero-free-region and exceptional-zero deduction remain R2 [Lean], including `logDerivRegionChi`, `zFRDirichlet`, `siegelLower` and `excBound` through `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:17–34`. For the deeper box-bound inputs see §4.8.6.

### 4.8.8 Local zeros and the logarithmic derivative in TailBox

#### 4.8.8.1 Motivation

The numerator in the contour integral of §4.8 is $D(s)=-L'(s,\chi)/L(s,\chi)$. A bound for $L$ on a disc gives no lower bound for its values near a zero. Instead, the local Landau argument removes the poles of the logarithmic derivative and bounds the contribution of the remaining factor. An inverse bound normalizes the function at the disc center. The zero-free box then bounds the finite sum of pole terms by separating the contour from the selected zeros.

#### 4.8.8.2 A simple zero and a double zero [Expository]

Use the closed unit disc centered at $0$ and set $a=1/8$. In both examples the only zero lies inside the evaluation disc of radius $1/6$. Write $x=a+\epsilon$ for $0<\epsilon\le1/24$.

**Simple zero.** Let $f(z)=(z-a)e^z$. Then $f(0)=-1/8$, and on the unit disc $|f(z)|\le(9/8)e=9e|f(0)|$. Differentiation gives $f'(z)=e^z(1+z-a)$, so $f'(a)=e^a$ and $f'(x)/f(x)=(1+\epsilon)/\epsilon=1/\epsilon+1$. At $x=1/6$ the ratio is $25$, with $24$ from the pole and $1$ from the remainder. The total multiplicity satisfies $1\le\log(9e)/\log 2$. Omitting the pole leaves $1/\epsilon+1$, which exceeds any fixed remainder bound as $\epsilon$ tends to zero.

**Double zero.** Let $f(z)=(z-a)^2e^z$. Then $f(0)=1/64$, and $|f(z)|\le(9/8)^2e=81e|f(0)|$ on the unit disc. Here $f'(z)=e^z(2(z-a)+(z-a)^2)$ and $f''(z)=e^z(2+4(z-a)+(z-a)^2)$. Thus $f'(a)=0$ and $f''(a)=2e^a$. The ratio at $x$ is $(2\epsilon+\epsilon^2)/\epsilon^2=2/\epsilon+1$. At $x=1/6$ the ratio is $49$, with $48$ from the pole and $1$ from the remainder. The total multiplicity satisfies $2\le\log(81e)/\log 2$. Using weight one for the single location leaves the unbounded remainder $1/\epsilon+1$. Using weight two leaves $1$. In both examples a separation $|x-a|\ge d>0$ bounds the pole's contribution by $m/d$, where $m$ is the order of the zero.

#### 4.8.8.3 Definitions and the local disc lemma

Write $B(c,R)=\{w:|w-c|<R\}$ and $\overline{B}(c,R)=\{w:|w-c|\le R\}$. At a zero $\rho$, the order $m_\rho$ is the exponent of the first nonzero Taylor term. In the archive the wrapper `LandauLocal3` exposes only $m_\rho\ge1$ and the derivative test for order one; the exact order follows from $h(\rho)\ne0$ in `zeroFactorization`. The empty product is $1$ and the empty sum is $0$.

**Lemma 4.8.8.3 (local Landau expansion).** Let $r>0$, $H\ge1$, and let $f$ be holomorphic on $B(c,r)$ and continuous on $\overline{B}(c,r)$. Assume $f(c)\ne0$ and $|f(w)|\le H|f(c)|$ throughout the closed disc. The set $Z$ of zeros in $\overline{B}(c,r/3)$ is finite. Its total order $n=\sum_{\rho\in Z}m_\rho$ satisfies $n\le\log H/\log 2$. At every $s$ with $|s-c|\le r/6$ and $f(s)\ne0$,
$f'(s)/f(s)=\sum_{\rho\in Z}m_\rho/(s-\rho)+E(s)$, where $|E(s)|\le72\log H/r$. The remainder extends holomorphically to $B(c,r/3)$. If $|s-\rho|\ge d>0$ for every $\rho\in Z$, then $|f'(s)/f(s)|\le (72/r+1/(d\log 2))\log H$. This formulation uses interior holomorphy and boundary continuity for the textbook proof. The archive assumes complex differentiability on the closed disc.

**Proof.** By the identity theorem the zeros are isolated and have finite order because $f(c)\ne0$. An infinite sequence of distinct zeros in the smaller closed disc would have an accumulation point inside $B(c,r)$. Thus $Z$ is finite.

Keep the original finite set of locations and divide out one linear factor at a time. If the current function $F$ has positive order at $\rho$, set $G(w)=F(w)/(w-\rho)$ for $w\ne\rho$ and $G(\rho)=F'(\rho)$. The Taylor series shows that $G$ is holomorphic at $\rho$ and that its order there drops by one. At every other location the divisor is a holomorphic unit, so the order stays the same. The boundary values stay continuous because the divisor is nonzero there. Repeating until the sum of orders is zero gives $f=Ph$, where $P(w)=\prod_{\rho\in Z}(w-\rho)^{m_\rho}$ and $h$ is nonzero on the smaller closed disc. At a selected zero, $f(w)=(w-\rho)^{m_\rho}k(w)$ with $k(\rho)\ne0$. Differentiation gives $f'(\rho)=k(\rho)$ for order one and $f'(\rho)=0$ for order at least two.

On $|w-c|=r$, every selected zero has $|w-\rho|\ge2r/3$, whereas $|c-\rho|\le r/3$. Hence $|P(w)|\ge(2r/3)^n$ and $|P(c)|\le(r/3)^n$. The growth hypothesis gives $|h(w)|\le H|P(c)||h(c)|/|P(w)|\le H2^{-n}|h(c)|$. The maximum modulus principle extends this bound to the outer closed disc. Taking $w=c$ and canceling $|h(c)|>0$ yields $2^n\le H$.

Put $R=r/3$. The holomorphic function $h'/h$ has a primitive $g$ on $B(c,R)$ with $g(c)=0$. The derivative of $he^{-g}$ vanishes, so $h=h(c)e^g$. The normalization and exponential identity follow from the [disk logarithm proposition](03-landau-window-criterion.md#a-normalized-holomorphic-logarithm-on-a-zero-free-disk). The bound on $h$ gives $\Re g\le\log H$. For $A>\log H$ put $u=g/(2A-g)$. The denominator is nonzero and $|u|\le1$ because $|2A-g|^2-|g|^2=4A(A-\Re g)>0$. Since $u(c)=0$, Schwarz's lemma gives $|u(w)|\le |w-c|/R$. The identity $g=2Au/(1+u)$ now gives the Borel–Carathéodory bound $|g(w)|\le 2A|w-c|/(R-|w-c|)$, at most $6A$ on $\overline{B}(c,3R/4)$. When $|s-c|\le R/2$, the circle of radius $R/4$ around $s$ stays in that closed disc. Cauchy's derivative formula gives $|g'(s)|\le6A/(R/4)=24A/R$. Letting $A$ decrease to $\log H$ gives $|h'(s)/h(s)|\le72\log H/r$, including when $H=1$.

Where $f(s)\ne0$, the product rule gives $f'/f=P'/P+h'/h$. Differentiating the finite product and dividing by $P(s)$ gives $P'(s)/P(s)=\sum_{\rho\in Z}m_\rho/(s-\rho)$. The holomorphic remainder is $h'/h$ on $B(c,R)$. The finite sum has absolute value at most $n/d$ under the stated separation, giving the last bound. $\square$

#### 4.8.8.4 The character specialization and right-half-plane bounds

**Theorem 4.8.8.4 (conditional input to the box estimate).** Assume the reciprocal Möbius and von Mangoldt logarithmic derivative identities for Dirichlet $L$-functions on $\Re s>1$, together with the untwisted zeta identity there. Assume that $\zeta$ has a simple pole at $1$ with residue $1$, that the non-principal $L$-functions are holomorphic, and that $|L(w,\chi)|\le CN(1+|w|)$ for all non-principal characters of modulus $N\ge1$ and $\Re w\ge1/2$, with common constant $C$.

For all characters and $\sigma=\Re s>1$, one has $|L(s,\chi)|^{-1}\le\sigma/(\sigma-1)$ and $|D(s)|\le1/(\sigma-1)+C_R$ with $C_R\ge0$ independent of $N,\chi,s$. For non-principal $\chi$, let $26/27\le\Re s<11/10$ and $L(s,\chi)\ne0$. Put $t=\Im s$, $c=21/20+it$, $r=11/20$, $X=N(|t|+2)$ and $B_C=1+\log(42(|C|+1))/\log 2$. Then
$L'(s,\chi)/L(s,\chi)=\sum_{\rho\in Z}m_\rho/(s-\rho)+E(s)$, where $Z$ contains exactly the zeros in $\overline{B}(c,11/60)$,
$\sum_{\rho\in Z}m_\rho\le B_C\log X/\log 2$, and $|E(s)|\le(1440/11)B_C\log X$.

**Proof.** The reciprocal series $\sum_{n\ge1}\mu(n)\chi(n)n^{-s}$ converges absolutely in $\sigma>1$, since $|\mu(n)\chi(n)|\le1$. The reciprocal identity gives nonvanishing there. For each $n\ge2$, the integral of the decreasing function $x^{-\sigma}$ over $[n-1,n]$ bounds $n^{-\sigma}$. Thus $|L(s,\chi)|^{-1}\le1+\int_1^\infty x^{-\sigma}\,dx=\sigma/(\sigma-1)$.

For the logarithmic derivative, $D(s)=\sum_{n\ge1}\Lambda(n)\chi(n)n^{-s}$, so $|D(s)|\le A(\sigma)=\sum_{n\ge1}\Lambda(n)n^{-\sigma}$. The series converges by $\Lambda(n)\le\log n$, and its nonnegative terms decrease with $\sigma$. The untwisted identity gives $A(\sigma)=-\zeta'(\sigma)/\zeta(\sigma)$. Write $\zeta(w)=v(w)/(w-1)$ near $1$ with $v(1)=1$. On a sufficiently small closed disc of radius $\epsilon>0$, the function $v$ is nonzero and $|v'/v|\le B$ for some $B\ge0$. For $1<\sigma<1+\epsilon/2$, logarithmic differentiation gives $A(\sigma)\le1/(\sigma-1)+B$. For $\sigma\ge1+\epsilon/2$, monotonicity gives $A(\sigma)\le A(1+\epsilon/2)$. The maximum of $B$ and $A(1+\epsilon/2)$ serves as $C_R$.

At the disc center the inverse bound gives $|L(c,\chi)|^{-1}\le21$. On $\overline{B}(c,r)$, $\Re w\ge1/2$ and $1+|w|\le 1+21/20+|t|+11/20\le2(|t|+2)$. This gives $|L(w,\chi)|\le H|L(c,\chi)|$ with $H=42(|C|+1)X$. The point $s$ has the same imaginary part as $c$. Both $21/20-26/27=47/540$ and $11/10-21/20=1/20$ are at most $r/6=11/120$. Apply Lemma 4.8.8.3 and use $X\ge2$ to obtain $\log H\le B_C\log X$. Substituting $72/r=1440/11$ gives the remainder bound. Both the pole sum and the remainder change sign for $D=-L'/L$. $\square$

#### 4.8.8.5 Return to the tail budget

Suppose $1\le N\le Q$, $Q\ge2$, and $\chi\ne1$ has the zero-free box $\mathcal B(Q)$ of §4.8. Let $\Re s\ge1-1/400+\delta$ and $|\Im s|\le Q-1$ with $\delta>0$. For $\Re s<11/10$ the box ensures $L(s,\chi)\ne0$, and the real-part lower bound implies $\Re s\ge26/27$. Every selected zero satisfies $|\Im\rho|\le Q-1+11/60<Q$. The box therefore forces $\Re\rho\le1-1/400$, and $|s-\rho|\ge\Re(s-\rho)\ge\delta$. Since $X\le Q(Q+1)\le Q^3$, Theorem 4.8.8.4 gives $|D(s)|\le3B_C(1440/11+1/(\delta\log 2))\log Q$. For $\Re s\ge11/10$ the right-half-plane estimate gives $10+C_R$. The archive adds the two budgets and uses $\log Q\ge\log 2$, giving the admissible constant
$K_B=3B_C(1440/11+1/(\delta\log 2))+(10+C_R)/\log 2$.

In §4.8.5 the left edge lies at $1-1/400+\delta$ and the horizontal edges have heights $\pm Q/2$, within $Q-1$. The numerator bound on all three edges is $M=K_B\log Q$. The $1/\delta$ cost comes from the finite zero sum. The paired left-edge integral also uses the distance $g=1/400-\delta$ from the kernel pole at $1$, giving $\log(1+(Q/2)/g)$ in its budget. The two evaluations at $z$ and $z+z\eta$ use these same constants. The original-line tail uses the right-half-plane estimate at $\Re s=2$ with bound $1+C_R$. See §4.8.7 for inversion and the empty-zero shift, §4.7 for the density count, §4.10.8 for the separate disc at $101/100+it$ used by the smoothed explicit formula, and §17.4.11 for the separate per-character endpoint formula.

#### 4.8.8.6 Source map and reading boundary

The following paths are relative to `src/Formalism/`. Each reference uses archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

| Step | Declaration and file | Reading status |
| --- | --- | --- |
| Remove one factor per unit of order | `exists_factorization_of_sum_order` and `zeroFactorization`, `ZeroFreeRegion/ZetaLogDerivativeBounds/ZeroFactor.lean:18–118,120–168`. | [Lean, read] locally |
| Take a normalized logarithm and bound its derivative | `zflb_exists_log`, `logDerivBoundOnBall`, `ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivBound.lean:12–40,42–120`. The archive applies Mathlib's normalized Borel–Carathéodory theorem. The Schwarz argument above derives the same estimate. | [Lean, read] locally for the A2 bodies |
| Count by maximum modulus and form the finite sum | `landauLocal_logDeriv_prod`, `ZeroFreeRegion/ZetaLogDerivativeBounds/LandauLocalOf.lean:9–50`; `exists_localZeroExpansion_of_bound` with its derivative test, `LandauZeroFreeBounds/ExceptionalZeroBounds/ExistsLocalZeroExpansionOfBound.lean:12–47,49–180`. | [Lean, read] locally |
| Specialize to the character disc | `LandauLocal3`, `LandauZeroFreeBounds/LogDerivRegionChiOf.lean:57–68`; `landau_local3`, `LandauZeroFreeBounds/ExceptionalZeroBounds/LandauLocal3.lean:8–9`; `landau_lemma_lfunction_zeros`, `LandauZeroFreeBounds/ExceptionalZeroBounds/LandauLemmaLfunctionZeros.lean:9–91`. The real-part, norm, and logarithmic comparisons use the helpers in the cited file’s import LogTwoLeLogAnalyticConductor.lean:9–16,32–68. The wrapper exposes the simple-zero clause. Exact orders come from `zeroFactorization`. | [Lean, read] locally |
| Control the inverse and right-half-plane derivative | `inverseBound`, `negLD_eq_LSeries_mul_vonMangoldt`, `norm_LSeries_twist_vonMangoldt_le`, `l_log_deriv_right`, `LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean:12–86,88–126`; `lamF`, `norm_logDeriv_le_lamF`, `term_vonMangoldt_real`, `lamF_eq_norm`, `lamF_anti`, `ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean:10–50`; `logDerivBoundRightHalfPlane`, `ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivRight.lean:11–42`. | [Lean, read] locally |
| Consume the two bounds | `tail_box_log`, `tail_box_sum`, `tail_box_negLD`, `GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailBox.lean:13–119`. The contour call sites are in §4.8.6. | [Lean, read] as in §4.8 |

The local R3 reading covers the bodies listed above, and [§4.10.9](#4109-uniform-polynomial-growth-in-the-half-plane-lfunction_polynomial_growth-and-exlf_growth) reads `lfunction_polynomial_growth` (`LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:53–71`) with witness $C=9$ (giving $B_C=1+\log420/\log2\approx9.7142$). The continuation and deeper Dirichlet-series proofs retain R2 [Lean]. The direct von Mangoldt series and Laurent remainder producers are read in [§4.10.10](#41010-the-pole-subtracted-zeta-logarithmic-derivative). The interfaces for the inverse, growth, and right-side estimates are NoZeroComplexOf.lean:25–35. The full `tail_contour` closure retains R2, with the exceptional-zero, zero-free-region and endpoint predecessors retaining their existing labels. The examples, holomorphic extension of the remainder, and the general distance corollary are [Expository]. See the [source ledger](../sources/SOURCES.md#p13-local-zero-expansion-in-tailbox).

## 4.9 Counting enough candidates before the sieve

### 4.9.1 Motivation

A mean-square bound proportional to the number of candidates holds vacuously on an empty set. Even when the set is nonempty, the zero-density loss in §4.4.5 is an absolute count, so we need a lower bound against which to compare it. The archive first counts primes in the entire progression, retains the primes above the square-root cut, and only then bounds the share that fails the twist tests. An exceptional zero enters the progression main term as a signed correction. The bad twist tests delete elements of a finite set.

### 4.9.2 A small progression and two character tests [Expository]

Take $M=8$, $b=3$, and $U=100$. The primes in the progression up to $U$ are $3,11,19,43,59,67,83$. Exactly one, $3$, is at most $\sqrt U=10$, leaving $P=\{11,19,43,59,67,83\}$. To model two character tests, take the primitive quadratic characters of conductors $3$ and $5$, and stipulate the failure sets for their window-sum tests to be $\{19,43\}$ and $\{43,67\}$. Stipulate also a box failure set $\{19\}$. The union is exactly $\{19,43,67\}$, leaving $\{11,59,83\}$. The sum of the three failure counts is $5$, while their union has size $3$. The stipulated flags illustrate the finite-set deduction in §4.9.5. The prime list and the square-root cut are exact, and the analytic large-scale hypotheses are outside this example.

For the sign of the exceptional correction, the primitive quadratic character of conductor $8$ given by $(2/\cdot)$ takes the value $-1$ on $3$ and $+1$ on $1$. If that character supplied the optional pair in the formula below, the progression $3\bmod 8$ would gain $\operatorname{li}_2(U^\beta)/4$ and the progression $1\bmod 8$ would lose exactly the same amount. This is a conditional substitution in the formula for the main term.

### 4.9.3 Definitions and named analytic inputs

Let $M$ be a positive multiple of $8$, let $b$ be a reduced residue class, and, for $U>0$, write
$$
P(M,b,U)=\{q\text{ prime}: q\equiv b\bmod M,\ \sqrt U<q\le U\}.
$$
This is the positive-scale interpretation of `PPset`. The count $\pi(U;M,b)$ includes all primes up to $U$ in the class. Put $\operatorname{li}_2(U)=\int_2^U dt/\log t$. An exceptional pair consists of a character $\chi\bmod M$ with $\chi^2=1$, $\chi\ne1$, and a real zero $\beta$ of its $L$-function with $1-1/(8\log M)<\beta<1$. For an optional pair $e$, define the main term $H_e(b,U)$ by
$$
H_{\mathrm{none}}(b,U)=\frac{\operatorname{li}_2(U)}{\varphi(M)},\qquad
H_{(\chi,\beta)}(b,U)=\frac{\operatorname{li}_2(U)-\Re\chi(b)\operatorname{li}_2(U^\beta)}{\varphi(M)}.
$$

- **Relative PNT in progressions (`PNTAPRelW`) [Lean].** There exist real $c_3>0,A_0,C_0$ such that for each positive $M$ divisible by $8$ there is an option $e$ fixed for that modulus, valid if present, with no exceptional pair if absent. For every $U\ge2$ and every $b$ coprime to $M$ with $C_0\log M\log(\log M+2)\le\log U$, one has
  $$
  |\pi(U;M,b)-H_e(b,U)|\le A_0 E\,H_e(b,U),
  \qquad E=\exp(-c_3\log U/\log M)+\exp(-\sqrt{c_3\log U}).
  $$
  The proof below uses validity of the pair when present and the relative estimate in either case.
- **Real-zero separation (`ExcBound`) [Lean].** For every $\delta>0$ there is $c_0(\delta)>0$ such that for all positive moduli and all nonprincipal characters with $\chi^2=1$, each real zero $\beta$ satisfies $\beta\le1-c_0(\delta)M^{-\delta}$. The deduction uses $\delta=1$. The full analytic statement is the one in the archive, with classical background in [Siegel1935] and [Davenport2000].

### 4.9.4 Conditional counting proposition [Lean, read]

Assume `PNTAPRelW` and `ExcBound`. For every $\varepsilon>0$ there is $x_0$ such that for every real $x\ge x_0$ and $U>0$, every positive $M$ divisible by $8$, and every $b$ coprime to $M$, the conditions
$$
\frac14(\log x)^2\log M\le \log U,\qquad
x^{\varepsilon/6}\le\log U\le x^{\varepsilon/5}(\log x)^2
$$
imply $|P(M,b,U)|\ge U^{9/10}>0$. The threshold comes before the choice of $M,b,U$.

**Proof.** Write $L=\log x$, $v=\log U$, $\Lambda=\log M$, and set $c=\min(c_0(1),1)$ and $k_0=\log(4(|A_0|+1))$. The witnesses in `count_a` give the threshold
$$
x_0=\exp\!\left(320+4|C_0|(5+\varepsilon/5)
       +|4k_0/c_3|+|4k_0^2/c_3|
       +|\log(320/c)|\right).
$$
Each summand is nonnegative, hence $L$ is at least each of the displayed summands. Fix $M,b,U$ in the claimed range and select the option for $M$. The real-zero bound with $c_0(1)$ also holds with the smaller constant $c$. The proof now passes these data to `count_pos`, which uses the lower bound $L^2\Lambda/4\le v$ and the upper bound $v\le x^{\varepsilon/5}L^2$.

1. **Enter the PNT range (`range_ok`).** Since $M\ge8$, $\Lambda\ge1$. The two bounds just cited give $\Lambda\le4x^{\varepsilon/5}$ and $v\ge L^2/4$. In particular $v\ge4$, $v\ge80\Lambda$, and $U\ge2$. Also $\Lambda+2\le6x^{\varepsilon/5}$, so $\log(\Lambda+2)\le5+(\varepsilon/5)L\le(5+\varepsilon/5)L$. Multiply by $|C_0|$ and use the threshold to bound the product by $L^2/4$. This proves $C_0\Lambda\log(\Lambda+2)\le v$, including for negative $C_0$.

2. **Keep a positive main term (`mainAP_lower`).** For $2\le a\le U$, continuity of $1/\log t$ on $[2,U]$ gives the integral difference, and its minimum on $[a,U]$ gives
   $$
   \operatorname{li}_2(U)-\operatorname{li}_2(a)\ge (U-a)/v.
   $$
   Thus $\operatorname{li}_2(a)\ge0$. Without an exceptional pair, use $a=2$ and $U-2\ge cU/(2M)$ (here $U\ge5$, $M\ge8$, $c\le1$). With a pair, $\beta\ge7/8$ and $v\ge4$ give $2\le U^\beta\le U$. The separation $\beta\le1-c/M$ and $v\ge1$ give $U^\beta\le U\exp(-c/M)$. For $0\le w\le1$, convexity on the segment from $0$ to $-1$ gives $\exp(-w)\le1-w/2$, since $\exp(-1)\le1/2$. Apply it to $w=c/M$ to obtain $U-U^\beta\ge cU/(2M)$. Because $\Re\chi(b)\le1$ and $\operatorname{li}_2(U^\beta)\ge0$, the integral difference at $a=U^\beta$ bounds the numerator from below even for the most adverse sign. Dividing the positive lower bound by $0<\varphi(M)\le M$ yields, in both cases,
   $$
   H_e(b,U)\ge \frac{cU}{2vM^2}.
   $$

3. **Make the relative loss at most one half (`err_le_half`).** The threshold and $L^2\ge L$ give $k_0,k_0^2\le c_3L^2/4$. Since $v/\Lambda\ge L^2/4$ and $v\ge L^2/4$, we have $c_3 v/\Lambda\ge k_0$ and $\sqrt{c_3v}\ge k_0$ (with $k_0\ge0$). Each exponential in $E$ is at most $e^{-k_0}=1/(4(|A_0|+1))$. Hence $|A_0|E\le1/2$. Positivity from step 2 lets us bound $A_0 EH_e$ by $H_e/2$. The absolute-error inequality in the PNT then gives $\pi(U;M,b)\ge H_e(b,U)/2$.

4. **Budget for the short segment (`size_ineq`, `piAP_le_card_PPset_add`).** From $v\ge L^2/4$ and $L\ge320$ we get $v/20\ge L\ge\log(320/c)$. Also $v\le40e^{v/40}$ and $M^2=e^{2\Lambda}\le e^{v/40}$, the latter by $v\ge80\Lambda$. Splitting $e^v$ into factors with exponents $9v/10$, $v/20$, $v/40$, $v/40$ gives
   $$
   \frac{cU}{2vM^2}
   \ \ge\ U^{9/10}\frac{c e^{v/20}}{80}
   \ \ge\ 4U^{9/10}.
   $$
   Every prime counted by $\pi$ belongs to $P$ or to the integer interval $[1,\lfloor\sqrt U\rfloor]$. Thus $\pi\le |P|+\sqrt U$. Since $\sqrt U\le U^{9/10}$ for $U\ge1$, we conclude $|P|\ge 2U^{9/10}-\sqrt U\ge U^{9/10}$. $\square$

The archive states `count_a` for real $U$ without an explicit positivity premise. In the $U=0$ branch the real power is zero. For $U<0$, Lean's real-power convention gives $\exp((9/10)\log U)\cos(9\pi/10)\le0$, so the same weak inequality follows from nonnegative cardinality. The positive-scale branch is the one used to prove nonemptiness.

### 4.9.5 From candidate count to a window

At either application of `stage`, write $P=P(M,b,U)$ and fix the list $\Xi$ of at most $R$ primitive characters of conductor $\le F\le\sqrt U$. For any subset $B$ of failing candidates, each of its members lies in the box-failure set $B_1$ or in a window-sum failure set $B_{2,\xi}$ for some $\xi\in\Xi$. The first set has size at most $|C_b|(FU)^{1/4}\le |C_b|U^{3/8}$. The count just proved is used twice in `stage`: first to turn $U>0$ into $P$ nonempty, and then to turn the absolute box loss into at most $\eta|P|/2$. For the latter use
$$
U^{21/40}\ge 2|C_b|/\eta,\qquad 9/10-3/8=21/40.
$$
The mean-square and uniformization inputs give $|B_{2,\xi}|\le\eta|P|/(2(R+1))$ per character at the stage threshold. The union bound gives $|B|\le\eta |P|$. Taking $B$ to be the entire failure set gives at least $(1-\eta)|P|$ survivors by the exact identity $|P|=|B|+|P\setminus B|$. For $0<\eta<1$, both factors in $(1-\eta)|P|$ are positive. The PNT option has already been accounted for inside $H_e$. The separate Jacobi-sum exception $n_*$ of §4.7.5 is an excluded index in a twist estimate and is handled within the mean-square supplier, with no additional deletion of an auxiliary prime here.

**A scale with an existence threshold [Expository].** Fix $\varepsilon,\tau>0$, $K\ge1$, and a target modulus $N_0>0$ in the ranges of Theorem 4.7. Set $\eta=1/2$, $z=Y^{\varepsilon/5}$, $U_1=e^z$, $U_2=e^{z(\log Y)^2}$, and $T=\max(4,(4|C_b|)^{40/21})$. Take $Y$ beyond both stage thresholds, both counting thresholds (at $\varepsilon$ and $6\varepsilon/5$), and the progression-range thresholds from §4.4.5. Also require $Y\ge e^2$ and $z\ge\log T$, for example by adjoining $(\log T)^{5/\varepsilon}$ to the maximum. Then $U_2\ge U_1\ge T$, and the displayed box-loss inequality holds in both stages. At stage 1, $M=8,b=3$, so the range follows from $(\log Y)^2\log 8/4\le z$, $Y^{\varepsilon/6}\le z$ and $\log Y\ge1$. At stage 2, $M=16\,\mathrm{oddM}(z,q)$ varies with the first-stage prime $q$, but $\log M\le4z$ uniformly, so $(\log Y)^2\log M/4\le\log U_2$, and the CRT supplies the reduced class. With $\varepsilon'=6\varepsilon/5$, the lower logarithmic cutoff is $Y^{\varepsilon'/6}=z$, and the upper cutoff is $Y^{\varepsilon'/5}(\log Y)^2\ge\log U_2$. Each stage therefore retains at least $U_i^{9/10}/2>0$ candidates on these scales. The threshold is chosen before selecting $q$ and works for the second progression attached to any eligible first-stage $q$.

In the archive, `stage1` and `stage2` pass the progression data to `stage`. The latter chooses $Y_0$ after fixing the analytic and sieve parameters, then uses $\log U\ge Y^{\varepsilon/6}$ and $U\ge1+\log U$ to enforce the cutoff in $U$. `pair_share` applies the complement count in both stages, and `pair_exists` sets $\eta=1/2$ and picks $q$ first and $d$ second. The wrapper `pairEx` takes $N_0=8M$ for the target modulus $M$ and includes the extra threshold for the logarithmic-derivative bound. Finally `winPairs` fixes the target character $\psi$ and the exponent $J$ supplied by `VWinAt ψ 401`. It asks `PairEx` for its threshold $Y_1$ at $(M,A)=(\psi.N,J)$, then chooses $X$ large enough that $X^{1/J}\ge Y_1$ before taking the pair at $Y=X^{1/J}$. This same pair is used for the whole rescaled window of §4.4.6. The consumer receives a threshold and pair witnesses. The inequality $|P|\ge U^{9/10}$ has already done its work in producing those witnesses.

### 4.9.6 Source map and reading boundary

The references identify the joined Alpöge–Claude archive, Lean `v4.33.1`, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` ([SOURCES, §1](../sources/SOURCES.md#1-the-lean-archive-primary-source)).

| Step | Archive source |
|---|---|
| Finite progression count, exceptional pair, main term and relative PNT | `src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:50–51`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MeanSquareHypWIff.lean:24–46` |
| Short-segment loss | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean:13–30` |
| Integral and convexity steps, including the full `mainAP_lower` supplier | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean:32–173` |
| Size, relative loss and PNT range | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean:175–203,205–237,239–273` |
| `count_pos` and threshold in `count_a` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean:275–344,346–397` |
| `stage` calls the count, proves positivity and absorbs losses | `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:29–39,53–94,100–139,140–170` |
| Two progression choices and exact complements | `src/Development/AutomorphicArithmetic/MeanSquareBounds/Stage1Succ.lean:41–83`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/CharOf.lean:61–79,120–149`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairShare.lean:16–24,32–52` |
| Witness selection and window consumer | `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean:13–43`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112–130`, `src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean:5–35,52–68` |

**Reading status.** The complete proof bodies in `MSqCount`, including its direct counting suppliers, are [Lean, read] (local R3). The assembly of `pnt_progressions_relative_weak_holds` in `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:16–24` is [Lean, read] in §§4.10.2–4 and [§4.10.27](#p13-siegel-relative-pnt), which supplies the Abel and prime-power steps. The `ExcBound` interface and its direct wrappers are [Lean, read] at `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:50–52` and `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:26–32`. The gap proof is in [§4.10.24](#41024-separating-a-real-zero-from-1). The complete `siegelLower` input and the deeper analytic bodies identified in the source register remain [Lean], with their unread proofs [Open] in the book’s record.

**Related community reading [Community].** The LUMI vacuity report traced the use of the positive counts in the pair and window wrappers and marked the two sieve stages for closer reading. [LUMI vacuity report](https://github.com/aapolipponen/rh-lean-check-lumi/blob/main/docs/reports/vacuity-check.md)

---

## 4.10. Joining the two ranges of the relative progression estimate

The candidate count in §4.9 needs a prime-counting error measured against the
main term in the chosen residue class. If a real zero at $\beta$ is close to
$1$, the main term can involve the difference of two large logarithmic
integrals. An error measured against the ordinary logarithmic integral can then
overwhelm the difference. The two estimates assembled in `PNTFinal` first
control a sum of character errors on a common scale, $y\eta(M)$. Only after
joining those estimates does the proof pass to prime counts.

### 4.10.1. Two model calculations [Expository]

Take $M=8$ and write $l=\log 8$. For a small parameter illustration, use
near threshold $a=1/20$, an alternative far threshold $a_-=1/40$, and
$\log y=4096$. Then $1.6<l<3.2$, so both the near estimate at $a$ and the far estimate at
$a_-$ apply provided the far range constant satisfies
$C_0 l\log(l+2)\le4096$. For example, the model value $C_0=16$ satisfies
this check. For $X=y$ the resulting prime-count range condition is
$32l\log(l+2)\le4096$, which holds as well. At this overlap point, trial rates $c_N=1/10$ and $c_F=1/2000$
give the normalized factors $e^{-6.4}\approx0.001662$ and
$e^{-2.048/l}\approx0.3735$, respectively, before multiplication by their
individual constants. These trial constants illustrate the inequalities in
the range statements.

**No exceptional pair.** Set $e(8)=\mathrm{none}$. The character main term is
$y$ for the principal character and zero for the other three. Here
$\eta(8)=1$. For each reduced class, the prime-counting main term is
$\operatorname{li}_2(X)/4$, where $\operatorname{li}_2(X)=\int_2^X dt/\log t$.

**An exceptional pair in the model.** Use the quadratic character modulo $8$
with values $(1,-1,-1,1)$ on $(1,3,5,7)$, and prescribe
$\beta=999/1000$. This simulated separation satisfies
$0<1-\beta<1/(8l)$ and gives $\eta(8)=l/1000\approx0.00207944$.
For example, the trial region constant $c_Z=1/20$ puts this value of $\beta$
inside the narrow region, since $1-\beta<c_Z/\log16$. The exceptional
character's main term is $-y^\beta/\beta$. At the overlap point its magnitude
relative to $y$ is $e^{-4.096}/0.999\approx0.01666$. The prime-counting main
terms in classes $1$ and $3$ are respectively
$(\operatorname{li}_2(X)-\operatorname{li}_2(X^\beta))/4$ and
$(\operatorname{li}_2(X)+\operatorname{li}_2(X^\beta))/4$.
The same two decay factors as above multiply $y\eta(8)$ on both sides of
the splice. The exceptional data are counterfactual inputs to the formulas.
The calculations supply no assertion of an exceptional zero for modulus $8$.

### 4.10.2. The common normalization

Let $M$ be a positive multiple of $8$, $l=\log M$, and
$H(M)=l\log(l+2)$. Write $\psi_\chi(y)=\sum_{n\le y}\Lambda(n)\chi(n)$.
The narrow region has boundary
$\operatorname{Re}s=1-c_Z/\log(M(|\operatorname{Im}s|+2))$, with the
boundary included. The archive takes $c_Z$ to be the smaller of a
zero-free-region witness and $1/20$.

An exceptional pair is a nonprincipal quadratic character $\chi_1$ modulo
$M$ and a real zero $\beta$ of its $L$-function with
$1-1/(8l)<\beta<1$. The selector $e(M)$ chooses such a pair inside the
narrow region if one exists, otherwise chooses an exceptional pair in the
wider interval if one exists, and returns none in the remaining case.
Set $\eta(M)=1$ for none and $\eta(M)=\min(1,(1-\beta)l)$ for a selected
pair. For $y\ge2$, use the character main term
$F_\chi(y)=\mathbf{1}_{\chi=1}y-\mathbf{1}_{\chi=\chi_1}y^\beta/\beta$,
where the second term is omitted for none. Define
$S_M(y)=\sum_{\chi\bmod M}|\psi_\chi(y)-F_\chi(y)|$.

For a reduced residue class $b$, put $\theta=\chi_1(b)\in\{-1,1\}$ if a
pair is selected, and put $\theta=0$, $\beta=1$ otherwise. Write
$P_b(X)=(\operatorname{li}_2(X)-\theta\operatorname{li}_2(X^\beta))/\varphi(M)$.
Both range estimates use the same $e(M)$ and thus the same $F_\chi$, $\eta$,
and eventual $P_b$. The narrow region used to choose or account for a zero
is a region in the complex $s$-plane. The near and far estimates below are
ranges of the real parameters $(M,y)$.

### 4.10.3. Conditional splice and proof

**Proposition 4.10.1 [Lean, read].** Use `abel_core`, the progression orthogonality identity and the prime-power removal bound cited in the source map as named inputs, and the numerical estimate `num_main` proved in §4.10.5. Assume the Dirichlet zero-free-region
input `ZFRDirichlet`, the per-character bound `PsiChiBound`, and the
real-zero separation input `ExcBound` at exponent $1$. Assume also the
far-range inputs `ExplicitS` and `ZeroSum` of §4.10.4, and use the differencing input `SharpenS` proved in §4.10.6.
Then there are $a,c_N>0$ and $A_N\ge0$ for which
$S_M(y)\le A_N y\eta(M)e^{-c_N\sqrt{\log y}}$ whenever
$l\le a\sqrt{\log y}$. For each fixed $v>0$ there are $c_F>0$,
$A_F\ge0$ and $C_F\ge0$ for which
$S_M(y)\le A_F y\eta(M)e^{-c_F\log y/l}$ whenever
$v\sqrt{\log y}<l$ and $\log y\ge C_F H(M)$. Both estimates assume $y\ge2$
and $M$ as above. Choose the far constants at $v=a$, and set
$c=\min(c_N,c_F)$, $A=A_N+A_F$, $C_0=C_F$. Then, throughout
$y\ge2$, $\log y\ge C_0 H(M)$,

$$
S_M(y)\le A y\eta(M)\bigl(e^{-c\log y/l}+e^{-c\sqrt{\log y}}\bigr).
$$

Let $c_1>0$ be the uniform constant in $\eta(M)\ge c_1/M$ derived below.
With $d=\min(c/2,c^2/2)$, $D=\max(2C_0,16)$ and
$B=10 A+5632e^{2d}/c_1$, every real $X\ge2$ with
$\log X\ge D H(M)$ and every natural $b$ coprime to $M$ satisfy

$$
|\pi(X;M,b)-P_b(X)|
\le B\bigl(e^{-d\log X/l}+e^{-\sqrt{d\log X}}\bigr) P_b(X).
$$

**Proof, near range.** The zero-free-region input says that a zero in the
narrow region is simple, real, attached to a nonprincipal quadratic
character, and unique over all characters at this modulus. Such a zero is
in the wider exceptional interval since
$c_Z/\log(2M)<1/(8l)$, and the nonvanishing on $\operatorname{Re}s\ge1$
gives the strict upper endpoint. Selection therefore picks its character
and value. For each character the finite list of narrow-region zeros
required by `PsiChiBound` is empty unless the selected pair lies in the
narrow region and belongs to that character. In that case the list is the
singleton containing the selected zero. Simplicity supplies the required
nonzero derivative, and uniqueness gives exhaustiveness.

Fix the constants $k>0$ and $C$ of `PsiChiBound` at $c_Z$. That input
bounds the character error with the narrow-list main term by
$Cy e^{-k\sqrt{\log y}}$ if $M\le e^{k\sqrt{\log y}}$. Set
$a=\min(k/4,c_Z)$ and $s=\sqrt{\log y}$. The hypothesis $l\le as$
implies the modulus bound of the input. If there is no selected pair or
the character differs from the selected character, its empty-list main
term already agrees with $F_\chi$. The singleton case agrees as well.

There remains the selected character with a zero in the wider interval
outside the narrow region. The empty-list estimate holds, and moving to
$F_\chi$ adds at most $y^\beta/\beta$. The wider interval and $M\ge8$
give $\beta\ge1/2$. Exclusion from the narrow region gives
$(1-\beta)\log(2M)>c_Z$. Using $\log(2M)\le2l\le2c_Zs$ and
$\log y=s^2$ yields $(1-\beta)\log y\ge s/2$. Consequently

$$
y^\beta/\beta\le 2y e^{-(1-\beta)\log y}\le2y e^{-s/2}.
$$

The triangle inequality now gives $|C|y e^{-ks}+2y e^{-s/2}$ as a bound
in every case. There are $\varphi(M)\le M$ characters.

For the relative normalization, let $h>0$ be the separation witness
$1-\beta\ge h/M$ in `ExcBound`. Take $c_1=\min(1,h\log3)$.
For $M\ge3$, $c_1/M\le1$, and, in the selected case,
$c_1/M\le (1-\beta)l$. Thus $M\eta(M)\ge c_1$ in either case.
Converting the sum of absolute bounds to a bound with $\eta$ costs a
second factor of $M$. In fact $2a\le k/2$ and $2a\le1/10$, so with
$c_N=\min(k/2,2/5)$ both $M^2e^{-ks}$ and $M^2e^{-s/2}$ are at most
$e^{-c_Ns}$. This gives $A_N=(|C|+2)/c_1$. This is the chain from
`rangeA_far_term` and the empty and singleton lists through
`rangeA_one_char` to `psi_relative_near_range`.

**Proof, far range.** Fix $v>0$. Use the strip width $\kappa$ supplied by
`ZeroSum`, the uniform explicit-formula witness $C$ at $\kappa$, and
the zero-sum witnesses $(c_z,A_z,C_z)$ at height exponent $12$. Use the numerical estimate `num_main` (Lemma 4.10.3). The
proof takes $T=M^{12}$, $\delta=M^{-5}$ and $t=y^{-\kappa/2}$. For each
character, `ExplicitS` gives a finite zero list $Z_\chi$ with weights
$m_\chi(\rho)$, and an error bounded at both differencing points
$y,(1+\delta)y$ by

$$
E=C\bigl((MT)^C t+\log(2y)\log^2(MT)/T\bigr).
$$

Let $W_\chi=\sum_{\rho\in Z_\chi}(m_\chi(\rho)-w_\chi(\rho))
y^{\operatorname{Re}\rho-1}$, where $w_\chi(\rho)=1$ exactly when $(\chi,\rho)=(\chi_1,\beta)$ is the
selected pair, and $w_\chi(\rho)=0$ elsewhere. This is nonnegative.
The matching estimate `one_char` accounts for a selected zero missing
from the list by at most $2yt$ in its own character. Indeed, completeness
above $1-\kappa/2$ at height $T$ forces a missing real zero below that
line. If the selected zero is present, one copy cancels with the term in
$F_\chi$. The remaining explicit-formula sum is bounded by $2y W_\chi$
since every listed real part is at least $1/2$, so $|\rho|\ge1/2$, and $|y^\rho|=y^{\operatorname{Re}\rho}$. To see the matching identity directly, write the error with the selected main term as the formula residual minus the sum weighted by $m_\chi-w_\chi$, plus the difference between the selected term and the sum weighted by $w_\chi$. The triangle inequality gives the sum of the three bounds.
The weighted sum in the differencing error is at most $W_\chi+1$ for the
selected character and $W_\chi$ for all others. With $\delta\le1/2$,
`SharpenS` (Theorem 4.10.7) therefore bounds the sum of character errors by

$$
M\bigl(4yE/\delta+4(\delta y+1)\log(2y)\bigr)
+22y\sum_\chi W_\chi+20\delta y+2yt.
$$

Here the first summand uses the bound $M$ for the number of characters,
and the last two terms are charged at most once. The numerical estimate
`num_main` bounds the terms outside the zero sum by $B_*/M^2$ times $y$,
for a uniform $B_*\ge0$ and $\log y\ge C_* H(M)$ in the strict far
range. The zero-sum input bounds $\sum_\chi W_\chi$ by
$|A_z|\eta e^{-c_z\log y/l}$ for $\log y\ge C_zH(M)$.
Choose $c_F=\min(c_z,v^2)$ and $C_F=\max(C_z,C_*)$.
Since $v\sqrt{\log y}<l$, one has $M^{-1}\le e^{-c_F\log y/l}$.
Use $M^{-1}\le\eta/c_1$ on the other inverse modulus. This yields
$A_F=22|A_z|+B_*/c_1$. Here $C_*>0$ by the choice in `num_main`.

**Proof, splice.** The two actual branches of `glue_ranges` are
$l\le a\sqrt{\log y}$ and $a\sqrt{\log y}<l$. Equality calls the near
estimate. In the first branch, lowering its exponent to $c$ increases
the exponential because $\sqrt{\log y}\ge0$. In the second branch the
same holds because $\log y/l\ge0$. In each branch enlarge its coefficient
to $A$ and add the other nonnegative exponential. These operations
preserve the inequality since $y\eta\ge0$. The Lean proof permits
amplitudes of either sign and uses $\max(A_N,0)+\max(A_F,0)$, which
agrees with $A$ here. The far constants are chosen once after $a$ is fixed.

**Proof, transfer to prime counts.** For $\sqrt X\le y\le X$,
$\log y\ge(\log X)/2\ge C_0H(M)$. Also $\log X\ge16l$ because
$l\ge\log8>2$ and $\log(l+2)>1$. This ensures $y\ge2$. Character
orthogonality gives the progression Chebyshev main term
$(y-\theta y^\beta/\beta)/\varphi(M)$, with error bounded by
$S_M(y)/\varphi(M)$: the coefficient $\chi(b^{-1})$ has modulus one
and its value for the exceptional term is $\theta$. Put $L=\log X$ and
$R=e^{-dL/l}+e^{-\sqrt{dL}}$. The inequalities
$c\log y\ge dL$ and $c\sqrt{\log y}\ge\sqrt{dL}$ bound the Chebyshev
error by $D_1 y$ throughout that interval, where
$D_1=A\eta R/\varphi(M)$.

The supplies to `pi_core` give a partial-summation error at most
$5D_1X/L+40\sqrt X$ for the weighted prime-power count with weights
$1/j$ on $p^j$. Removing powers $j\ge2$ adds at most $4\sqrt X L$.
The resulting main term is $P_b(X)$, with the same lower limit $2$ for
both logarithmic integrals. To turn this into a relative estimate,
write $P_*=X\eta/(2L\varphi(M))$. If $\theta\le0$, integrate on
$[X/2,X]$ to see $P_b(X)\ge P_*$. If $\theta=1$, the difference of
integrals is at least $(X-X^\beta)/L$. Since
$(1-\beta)L\ge\eta$ and $0<\eta\le1$, convexity gives
$e^{-(1-\beta)L}\le e^{-\eta}\le1-\eta/2$, so again $P_b(X)\ge P_*$.

The first error is $10 A R P_*$. The other errors total at most
$44\sqrt X L$ since $L\ge1$. Use $L^2\le64 e^{L/4}$,
$\sqrt{dL}\le2d+L/8$, $2l\le L/8$, and
$\eta/\varphi(M)\ge c_1 e^{-2l}$. In succession these give

$$
44\sqrt X L\le 2816 e^{3L/4}/L
\le 2816 e^{2d-\sqrt{dL}+L-2l}/L
\le (5632e^{2d}/c_1)R P_*.
$$

Combining the errors and enlarging $P_*$ to $P_b(X)$ proves the claim.
This is the transfer in `prime_count_of_psi` and `pi_core`, conditional
on the stated numerical and partial-summation supplies.

### 4.10.4. Scope and source map

The proved assembly has a seam at $\log y=(l/a)^2$. With the exactly
matching thresholds in the source, there is no point where both branch
hypotheses hold. The quantifier over the far threshold supplies an
optional overlap: fix any $0<a_-<a$ and use the far theorem at $a_-$.
Then both estimates hold when
$(l/a)^2\le\log y<(l/a_-)^2$, subject to
$\log y\ge C_F(a_-)H(M)$ and $y\ge2$. This band is nonempty for
sufficiently large $M$ because $H(M)/l^2\to0$. On it either estimate
bounds the very same absolute error and one may take their minimum.
The far exponent there is
$c_F(\sqrt{\log y}/l)\sqrt{\log y}$, with
$1/a\le\sqrt{\log y}/l<1/a_-$, so both estimates decay on the
square-root logarithmic scale. One choice of constants works for all
allowed $M,y,X,b$ once the analytic witnesses and thresholds have been fixed.
The source gives no uniform witnesses as $a_-$ varies down to zero and
claims no effective numerical value for the Siegel-dependent constant.
In the prime-counting range $L\ge D l\log(l+2)$ the two decay terms tend
to zero as $X\to\infty$, uniformly over the permitted moduli: split at a
fixed large $l$ and then let $L\to\infty$ for the bounded $l$ part.
The proposition is for positive multiples of $8$ and for reduced classes
at the prime-counting stage. It allows every real $X$ above its
modulus-dependent lower threshold.

`PNTFinal` supplies `ExplicitS` by the smoothed explicit formula and
`SharpenS` by the differenced formula, proved in §4.10.6. `ZeroSum` is the relative bound
on the weighted zeros after subtracting one copy of the selected pair.
Its supplier uses the spaced zero-density bound `LogDensityM` and the
lossy Deuring–Heilbronn input `DeuringHeilbronnMB`. [§4.10.28](#p13-spaced-zero-density) proves the
spacing estimates and assembles `LogDensityM` from the two named block counts.
The estimates cited below supply the partial-summation step.
The numerical estimate is proved in §4.10.5. In particular, the separation witness used twice in
the normalization comes from `excBound`, which in the archive uses
Siegel's lower bound. Classical background is available in Davenport,
*Multiplicative Number Theory*, third edition, and Siegel's class-number
paper, pp. 83–86. The precise ranges and relative normalization here are
those of the archive. [Davenport2000](https://link.springer.com/book/9780387950976) · [Siegel1935](https://doi.org/10.4064/AA-1-1-83-86)

In P13 the resulting `PNTAPRelW` supplies the progression estimate in
§4.9. Invoke its existing `count_pos` and `count_a` interfaces, with
their own range and `ExcBound` hypotheses, for $|\mathcal P|\ge U^{9/10}$.
The supply proved here is the prime-distribution input to those interfaces.

The following paths are relative to the root of the joined Lean archive
with SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
R3 applies to the listed proof bodies. The analytic dependency closure
remains R2.

| Role | Archive path and lines | Status |
|---|---|---|
| Definitions of the selector, weight, main terms and conditional interfaces | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DeuringHeilbronnM.lean:13–111`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MeanSquareHypWIff.lean:24–46` | Definitions |
| Selector, narrow-region uniqueness deduction and the relative weight bound | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean:11–195` | [Lean, read] |
| Character matching, outer exceptional term and relative near estimate | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTRangeA.lean:11–239` | [Lean, read] |
| Conditional far assembly from explicit formula, differencing and zero sum | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsm.lean:15–166` | [Lean, read] |
| Common bound and final wiring | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTGlue.lean:11–56`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:16–24` | [Lean, read] |
| Transfer to the relative prime count | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PrimeCountOfPsi.lean:12–91`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiC.lean:11–212` | [Lean, read] |
| Far-range numerical bound | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean:7–63,88–158` | [Lean, read], §4.10.5 |
| Modulus factor and exceptional term matching | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean:65–86`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmB.lean:11–153` | [Lean, read] |
| Differenced explicit formula `SharpenS` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharp.lean:13–156`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpA.lean:9–81`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpB.lean:12–123` | [Lean, read], §4.10.6 |
| Smoothed formula, zero sum, density and repulsion | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMain.lean:15`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSumL.lean:30`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDens.lean:19`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHB.lean:13`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHBSt.lean:11` | [Lean] |
| Character orthogonality, weighted prime-power removal and Abel summation | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean:44`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean:102`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean:135`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean:145`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean:212` | [Lean] |
| Zero-free region and per-character bound, exceptional separation and Siegel input | `src/Formalism/LandauZeroFreeBounds/Statement.lean:9`, `src/Formalism/LandauZeroFreeBounds/NoZeroComplex.lean:32`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean:10–31`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:23`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:26`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:32`, `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:50–52` | [Lean] |

The inner proofs in the [Lean] rows remain [Open] for the book’s reading record.

### 4.10.5 The far-range numerical absorption lemma `num_main`

The far-range proof in §4.10.3 cites one purely numerical estimate, `num_main`. This subsection proves it, follows its actual arguments in `psi_relative_far_range`, and shows where its output is spent. No analytic input enters the lemma itself. The analytic witnesses enter only as the three positive numbers to which it is applied.

#### 4.10.5.1 Motivation

Let $M$ be a positive multiple of $8$, put $l=\log M$, and let $y\ge2$. The far-range proof applies the explicit formula with truncation height $T=M^{12}$, differences with step $\delta=M^{-5}$, and writes $t=y^{-\kappa/2}$. Here $\kappa\in(0,1/20]$ is the strip width of `ZeroSum` and $C>0$ is the `ExplicitS` constant at $\kappa$. Both differencing points $y$ and $(1+\delta)y$ lie in $[y,2y]$, so the explicit-formula error is at most $E=C\bigl((MT)^Ct+\log(2y)\log^2(MT)/T\bigr)$ at both. Once the weighted zero sum $\sum_\chi W_\chi$ has been separated, the sum of the character errors is bounded by $22y\sum_\chi W_\chi$ plus

$$
N(M,y)=M\Bigl(\frac{4yE}{\delta}+4(\delta y+1)\log(2y)\Bigr)+20\delta y+2yt .
$$

The zero sum is controlled on the scale $y\eta(M)e^{-c\log y/l}$. To bring $N$ to the same scale, the proof first shows $N\le B_*yM^{-2}$. It then spends the two inverse moduli, one on the normalization $\eta(M)\ge c_1/M$ and one on the decay $e^{-c\log y/l}$.

The bound $N\le B_*yM^{-2}$ mixes two kinds of tails. Some summands carry negative powers of $M$, from $\delta$ and $T$. Others carry the negative power $t=y^{-\kappa/2}$ of $y$, against the polynomial loss $(MT)^C=M^{13C}$. Write $y=M^u$, that is, $u=\log y/l$. Then $t=M^{-\kappa u/2}$, so the saving $y^{-\kappa/2}$ becomes the saving of a fixed power of $M$ once $u$ is bounded below. The later conversion $M^{-1}\le e^{-cu}$ needs the upper bound $u\le l/c$. The far range is the window of $u$ in which both conversions hold.

#### 4.10.5.2 Three calculations at one modulus [Expository]

The lemma below holds for every positive triple $(v,\kappa,C)$. Here $v$ is the far-range parameter, the archive's `cA`. For the calculations take the placeholder triple $v=\kappa=1/20$ and $C=1$. The values of $v$ and $\kappa$ are the largest that the archive permits. The far parameter actually used is the near-range constant $a=\min(k/4,c_Z)\le1/20$, and `ZeroSum` has $\kappa\le1/20$. The value of $C$ is arbitrary. The arithmetic is a genuine instance of the lemma, but it identifies none of the archive's analytic witnesses. With these values

$$
D_v=1+v^{-2}=401,\qquad C_*=5+\frac{26C+20}{\kappa}=925,\qquad B_*=4C+676CD_v+8D_v+22=274310 .
$$

Take $M=2^{10}=1024$. Then $l=10\log2\approx6.93147$, $H(M)=l\log(l+2)\approx15.1770$, $C_*H(M)\approx14038.7$ and $(l/v)^2=400l^2\approx19218.1$. Split $N$ into the five summands $N_1,\dots,N_5$ of §4.10.5.3. Divided by $yM^{-2}$ they are

$$
\frac{N_1}{yM^{-2}}=4M^{21-u/40},\qquad
\frac{N_2}{yM^{-2}}=\frac{4\log(2y)(13l)^2}{M^4},\qquad
\frac{N_3}{yM^{-2}}=4\log(2y)\Bigl(\frac{1}{M^2}+\frac{M^3}{y}\Bigr),
$$

$$
\frac{N_4}{yM^{-2}}=\frac{20}{M^3},\qquad
\frac{N_5}{yM^{-2}}=2M^{2-u/40}.
$$

The proof of the lemma gives them the budgets $4C=4$, $676CD_v=271076$, $8D_v=3208$, $20$ and $2$, whose sum is $B_*$.

**Below the lower threshold: $\log y=5000$.** Here $u\approx721.35$. The far condition holds, since $v\sqrt{\log y}\approx3.54<l$. The range condition fails, since $5000<14038.7$. The absorption itself fails as well: $\kappa u\approx36.07<26C+16=42$, so $t=M^{-18.03}$ does not beat $M^{13C+8}=M^{21}$. Indeed

$$
\frac{N_1}{yM^{-2}}=4M^{2.966}=4e^{20.561}\approx3.40\cdot10^{9}>B_* .
$$

The other four quotients are about $1.5\cdot10^{-4}$, $1.9\cdot10^{-2}$, $1.9\cdot10^{-8}$ and $10^{-48}$. Hence $N(M,y)>B_*yM^{-2}$, so at this point the conclusion of the lemma is false, not merely unproved. Neither range estimate of Proposition 4.10.1 claims the point. The near condition $l\le a\sqrt{\log y}$ fails, and the common threshold $C_0=C_F\ge C_*$ excludes it.

**Inside the window: $\log y=15000$.** Here $u\approx2164.04$, $14038.7\le15000<19218.1$ and $v\sqrt{\log y}\approx6.124<l$. The three absorption conditions $u\ge5$, $\kappa u\ge26C+16$ and $\kappa u\ge4$ hold, since $\kappa u\approx108.2$. The five quotients and their budgets are

| Summand | Quotient by $yM^{-2}$ | Budget |
|---|---|---|
| $N_1$ | $4e^{145.56-375}\approx9.1\cdot10^{-100}$ | $4$ |
| $N_2$ | $4\cdot15000.69\cdot8119.6/2^{40}\approx4.43\cdot10^{-4}$ | $271076$ |
| $N_3$ | $4\cdot15000.69/2^{20}\approx5.72\cdot10^{-2}$ | $3208$ |
| $N_4$ | $20/2^{30}\approx1.86\cdot10^{-8}$ | $20$ |
| $N_5$ | $2e^{13.86-375}\approx2.9\cdot10^{-157}$ | $2$ |

So $N(M,y)\approx0.0577\,yM^{-2}\le B_*yM^{-2}$. The differencing summand $N_3$ dominates, and every budget is lossy by many orders of magnitude.

**Beyond the seam: $\log y=20000$.** Now $v\sqrt{\log y}\approx7.071>l$, so the far hypothesis fails, and the splice gives this point to the near estimate. The numerical inequality still holds, since the five quotients add up to about $0.077$. The conversion is what breaks. Take $c_F=v^2$, the largest value its definition permits. Then $c_Fu\approx7.213>l$ and $e^{-c_Fu}\approx7.37\cdot10^{-4}<M^{-1}\approx9.77\cdot10^{-4}$. Far beyond the seam the inequality fails too. The quotient for $N_2$ exceeds $B_*$ once $\log(2y)>B_*M^4/(4C(13l)^2)\approx9.3\cdot10^{12}$, because a truncation height fixed at $M^{12}$ cannot control $\log y$ for astronomically large $y$.

#### 4.10.5.3 Definitions

Let $v,\kappa,C>0$, let $M\ge8$ and $y\ge2$ be real, and put $l=\log M$. Write

$$
T=M^{12},\qquad \delta=M^{-5},\qquad t=y^{-\kappa/2},\qquad u=\frac{\log y}{l},\qquad H(M)=l\log(l+2).
$$

For $M>0$ the archive's real power $M^{(12:\mathbb R)}$ equals the natural power $M^{12}$. Thus $MT=M^{13}$, $(MT)^C=e^{13Cl}$ and $\log(MT)=13l$. The **far-range budget** is $N(M,y)=N_1+\dots+N_5$, where

$$
N_1=4CyM^6(MT)^Ct,\qquad N_2=\frac{4Cy\log(2y)\log^2(MT)}{M^6},\qquad N_3=4M(\delta y+1)\log(2y),
$$

$$
N_4=20\delta y,\qquad N_5=2yt .
$$

Thus $N_1+N_2=M\cdot4yE/\delta$ with $E$ as in §4.10.5.1. This is literally the left side of `num_main`, with $T$, $\delta$ and $t$ substituted as in `psi_relative_far_range`.

The five summands have the following roles [Expository; their sources are the named inputs of §4.10.3]:

- $N_1$ is the first part of the explicit-formula error, the decay $y^{-\kappa/2}$ against the height and conductor loss $(MT)^C$.
- $N_2$ comes from truncating the zero sum at height $T$.
- $N_3$ is the differencing term of `SharpenS`. Heuristically, $\Lambda(n)\le\log(2y)$ on the at most $\delta y+1$ integers of an interval of length $\delta y$.
- $N_4$ is the share of the selected zero in the differencing zero sum, charged once because $\sum_\chi\mathbf 1_{\chi=\chi_1}\le1$.
- $N_5$ pays for a selected zero absent from the explicit-formula list. Such a zero lies below $1-\kappa/2$.

The factor $M$ in $N_1$, $N_2$ and $N_3$ counts characters, since $\varphi(M)\le M$.

Define the constants

$$
D_v=1+v^{-2},\qquad C_*=5+\frac{26C+20}{\kappa},\qquad B_*=4C+676CD_v+8D_v+22 .
$$

The **window** at $M$ is the set of $y\ge2$ with $C_*H(M)\le\log y<(l/v)^2$. Equivalently,

$$
C_*\log(l+2)\le u<\frac{l}{v^2}.
$$

The right end is the strict far condition $v\sqrt{\log y}<l$. The left end implies $u\ge C_*$, because $l\ge1$ gives $\log(l+2)\ge\log3\ge1$.

#### 4.10.5.4 The lemma

**Lemma 4.10.2 (algebraic core, `num_alg`) [Lean, read].** Let $M,y,C,K,P,t,g,m$ be real numbers with

$$
1\le M,\quad M^5\le y,\quad C\ge0,\quad K\ge0,\quad P\le M^{-8},\quad t\le M^{-2},\quad g\le KM^2,\quad 0\le m\le13M .
$$

Then

$$
M\Bigl(4yC\Bigl(P+\frac{gm^2}{M^{12}}\Bigr)M^5+4(M^{-5}y+1)g\Bigr)+20M^{-5}y+2yt\le(4C+676CK+8K+22)\,yM^{-2}.
$$

No sign condition is imposed on $P$, $t$ or $g$.

**Lemma 4.10.3 (far-range numerical absorption, `num_main`) [Lean, read].** Let $v,\kappa,C>0$, and let $D_v$, $C_*$ and $B_*$ be as in §4.10.5.3. Then $C_*\ge0$ and $B_*\ge0$. For all real $M\ge8$ and $y\ge2$ with

$$
C_*\,l\log(l+2)\le\log y\qquad\text{and}\qquad v\sqrt{\log y}<l,
$$

one has $N(M,y)\le B_*\,y\,M^{-1}M^{-1}$. The proof gives the individual bounds $N_1\le4CyM^{-2}$, $N_2\le676CD_v\,yM^{-2}$, $N_3\le8D_v\,yM^{-2}$, $N_4\le20yM^{-2}$ and $N_5\le2yM^{-2}$.

*Quantifiers and endpoints.* The archive states $\forall v,\kappa,C>0\ \exists C_*,B_*\ge0\ \forall M,y$, and its witnesses are the displayed closed forms. Thus $C_*$ depends only on $(\kappa,C)$, and $B_*$ only on $(v,C)$. Neither depends on $M$, $y$, a character or a residue class. The hypotheses $M\ge8$, $y\ge2$ and the range inequality are non-strict. The far inequality is strict, matching `glue_ranges`, which sends equality to the near estimate. Of $M\ge8$ and $y\ge2$ the proof uses only $M\ge3$ (so that $l\ge1$), $y>0$ and $\log y\ge0$. Of the far condition it uses only the consequence $v^2\log y<l^2$.

#### 4.10.5.5 Proof

*Proof of Lemma 4.10.2.* From $M\ge1$ and $M^5\le y$ we get $M>0$ and $y\ge0$. Clearing denominators,

$$
M\cdot4yC\Bigl(P+\frac{gm^2}{M^{12}}\Bigr)M^5=4Cy\Bigl(M^6P+\frac{gm^2}{M^6}\Bigr).
$$

Since $M^6\ge0$, $M^6P\le M^6M^{-8}=M^{-2}$. From $0\le m\le13M$ we get $m^2\le169M^2$. Because $m^2\ge0$ and $KM^2\ge0$, $gm^2\le KM^2m^2\le169KM^4$, and dividing by $M^6>0$ gives $gm^2/M^6\le169KM^{-2}$. As $4Cy\ge0$, the first part is at most $4Cy(1+169K)M^{-2}=(4C+676CK)yM^{-2}$. Next, $4M(M^{-5}y+1)\ge0$, so

$$
4M(M^{-5}y+1)g\le4M(M^{-5}y+1)KM^2=4K\bigl(yM^{-2}+M^3\bigr)\le8KyM^{-2},
$$

where $M^3\le yM^{-2}$ is the hypothesis $M^5\le y$. Finally, $M^{-5}\le M^{-2}$ gives $20M^{-5}y\le20yM^{-2}$, and $2yt\le2yM^{-2}$ because $2y\ge0$. Adding the four bounds gives $(4C+676CK+8K+20+2)yM^{-2}$. $\square$

*Proof of Lemma 4.10.3.* Nonnegativity of $C_*$ and $B_*$ follows from $\kappa,C>0$ and $D_v>0$. Fix $M$ and $y$ as in the statement. We verify the hypotheses of Lemma 4.10.2 for

$$
P=(MT)^Ct,\qquad t=y^{-\kappa/2},\qquad g=\log(2y),\qquad m=\log(MT),
$$

with the same $C$ and with $K=D_v=1+v^{-2}$.

1. *Logarithms.* Since $M\ge8>e$, $l\ge1$, hence $l+2\ge3>e$ and $\log(l+2)\ge1$. Also $l\le M-1\le M$.
2. *The lower end of the window.* Multiply $\log(l+2)\ge1$ by $C_*l\ge0$ and use the range hypothesis: $C_*l\le\log y$, that is, $u\ge C_*$.
3. *One inequality for both $y$-tails.* Multiply by $\kappa>0$. Since $\kappa C_*=5\kappa+26C+20$ and $5\kappa l\ge0$,

   $$
   (26C+20)\,l\le\kappa\log y .
   $$

4. *$M^5\le y$.* Since $C_*\ge5$, $5l\le C_*l\le\log y$, and the logarithm is increasing.
5. *The power tail.* With $(MT)^C=e^{13Cl}$ and $t=e^{-(\kappa/2)\log y}$, the claim $P\le M^{-8}$ reads $13Cl-\tfrac{\kappa}{2}\log y\le-8l$, i.e. $(26C+16)l\le\kappa\log y$. This follows from step 3 because $4l\ge0$.
6. *The second $y$-tail.* Likewise $t\le M^{-2}$ reads $4l\le\kappa\log y$, which follows from step 3 because $(26C+16)l\ge0$.
7. *The logarithm of $2y$.* Squaring the far condition, whose two sides are nonnegative, gives $v^2\log y<l^2$ (`logy_lt`). Hence $\log y\le l^2v^{-2}\le M^2v^{-2}$ by step 1. With $\log2\le1\le M^2$,

   $$
   \log(2y)=\log2+\log y\le M^2+v^{-2}M^2=D_vM^2 .
   $$

8. *The logarithm of $MT$.* $\log(MT)=13l\in[0,13M]$ by step 1.

Lemma 4.10.2 now gives the claim, and $M^{-2}=M^{-1}M^{-1}$. The individual bounds are the four estimates of its proof, with the first split into $4C$ for $N_1$ and $676CD_v$ for $N_2$. $\square$

Steps 3, 5 and 6 convert the tails $y^{-\kappa/2}$ into powers of $M$, all from the single inequality of step 3. Step 4 is needed only for the summand $4M\log(2y)$ of $N_3$, which carries no factor $y$. Step 7 is the only use of the far condition. Beyond $\log(l+2)\ge1$ the factor $\log(l+2)$ plays no role here. It gives the threshold the same shape as the range of `ZeroSum`, so the two thresholds merge as $C_F=\max(C_z,C_*)$.

#### 4.10.5.6 Remarks

**Where the output is spent [Lean, read, §4.10.3].** In `psi_relative_far_range` the lemma is called once, as `num_main cA κ C`, with $v$ equal to the far parameter `cA`. Through `glue_ranges` this parameter is the near-range constant $a=\min(k/4,c_Z)$. The other two arguments are $\kappa$, from `ZeroSum`, and $C$, from `ExplicitS` at that $\kappa$. The same $C$ is the zero-counting constant passed to `ZeroSum`, together with the height exponent $12$ that matches $T=M^{12}$. The choices are therefore made in the order $a$, $\kappa$, $C$, $(c_z,A_z,C_z)$, $(C_*,B_*)$, $c_1$. In the window, the two inverse moduli are spent as follows:

$$
B_*yM^{-1}M^{-1}\le B_*y\cdot\frac{\eta(M)}{c_1}\cdot e^{-c_F\log y/l},\qquad c_F=\min(c_z,v^2).
$$

The first factor uses $c_1M^{-1}\le\eta(M)$, with $c_1=\min(1,h\log3)$ and $h$ the `ExcBound` witness at exponent $1$. If $e(M)$ is none, $\eta=1\ge c_1/M$. If a pair $(\chi_1,\beta_1)$ is selected, then $1-\beta_1\ge h/M$ and $l\ge\log3$ give $(1-\beta_1)l\ge c_1/M$. The second factor is `inv_le_exp`, through $c_F\log y\le v^2\log y<l^2$. Under its own threshold $C_zH(M)\le\log y$, the zero sum is at most $|A_z|\,\eta\,e^{-c_z\log y/l}\le|A_z|\,\eta\,e^{-c_F\log y/l}$. The power tail of this lemma and the exponential tail of `ZeroSum` thus reach the same normal form, under the same threshold $C_FH(M)\le\log y$ and the same window condition:

$$
\sum_\chi|\psi_\chi(y)-F_\chi(y)|\le\Bigl(22|A_z|+\frac{B_*}{c_1}\Bigr)\,y\,\eta(M)\,e^{-c_F\log y/l}.
$$

At the prime-counting stage of §4.10.3, $y$ runs over $[\sqrt X,X]$, so $u$ runs over $[\tfrac12\log X/l,\ \log X/l]$. This interval may straddle the seam. For that reason the two range estimates are spliced before the transfer, and the constant $D=\max(2C_0,16)$ of Proposition 4.10.1 places the whole interval above the common threshold.

**A legal parameter set with margin [Expository].** Keep $v=\kappa=1/20$ and $C=1$. For the analytic witnesses take the placeholders $h=1/10$, $c_z=1/100$, $A_z=1$ and any $C_z\le C_*$. Then $c_1=(\log3)/10\approx0.10986$, $c_F=v^2=1/400$, $C_F=C_*=925$ and $A_F=22+B_*/c_1\approx2.4969\cdot10^6$. In the second calculation above, with $M=2^{10}$, the converted factor is $A_Fe^{-c_Fu}\approx1.1\cdot10^4$: the bound is true but useless there. Margin requires $c_Fu>\log A_F\approx14.73$, that is $u>5892$. Since $c_Fu\le v^2u<l$ in the window, it also forces $l>14.73$. Take $M=2^{30}$, so $l\approx20.7944$, and $u=7000$, i.e. $\log y=7000l\approx145560.9$. Then:

- the range holds: $C_*H(M)\approx60138.0\le145560.9$;
- the far condition holds: $v\sqrt{\log y}\approx19.08<20.79$;
- the left side is $N(M,y)\approx5.1\cdot10^{-13}\,yM^{-2}$, with $N_3$ again dominant;
- the conversion holds: $c_Fu=17.5\le l$ and $M^{-1}\approx9.3\cdot10^{-10}\le e^{-17.5}\approx2.51\cdot10^{-8}$;
- for $\eta$ only the inequality $c_1/M\approx1.02\cdot10^{-10}\le\eta(M)$ is used.

The far-range bound becomes

$$
\sum_\chi|\psi_\chi(y)-F_\chi(y)|\le A_Fe^{-17.5}\,y\eta(M)\approx0.063\,y\eta(M).
$$

This is a proper fraction of the scale $y\eta(M)$ on which §4.10.3 measures the main term and proves the prime-counting lower bound $P_b(X)\ge P_*$. With these placeholders the estimate has margin only for $M>A_F$, in particular only above $B_*/c_1$. The archive obtains $c_1$ through Siegel's lower bound and gives no numerical value for it, so the source supplies no numerical modulus threshold. The placeholders certify nothing about `ZeroSum`, `ExplicitS` or `ExcBound`.

**The shape of the window.** The window is nonempty exactly when $l/v^2>C_*\log(l+2)$. For the placeholders this means $l>4.2307$, or $M>68.8$, and $72$ is the first multiple of $8$ beyond it. At $M=8$ the lower end $\log y=2704.3$ exceeds the upper end $1729.6$. At $M=64$ the lower end $6993.4$ exceeds the upper end $6918.5$. For such moduli every $y$ above the range threshold satisfies $l\le v\sqrt{\log y}$, so the near estimate covers the whole range and the far branch is never used. As $v$ decreases the window widens, but $B_*=(676C+8)v^{-2}+680C+30$ grows and $c_F\le v^2$ shrinks. For the numerical part, this quantifies the remark of §4.10.4 that the source gives no witnesses uniform as the far parameter tends to zero.

**Why $12$, $5$ and $2$.** The final $M^{-2}$ pays for exactly the two inverse moduli of the conversion. Each of $N_1$, $N_2$ and $N_3$ carries the character count $M$, and $N_1$ and $N_2$ also carry $1/\delta=M^5$, for $M^6$ in all. The truncation summand therefore has $M^6\log(2y)(13l)^2/T$. The far condition and $l\le M$ make $\log(2y)(13l)^2$ at most $169D_vM^4$, so $T=M^{6+2+4}=M^{12}$ is the height at which $N_2$ fits the budget. Given only $\log(2y)\le D_vM^2$, the step $\delta=M^{-5}$ is the largest for which $4M\delta y\log(2y)\le4D_v\,yM^{-2}$. Its reciprocal $M^5$ is what $N_1$ and $N_2$ pay. Once $u\ge5$, also $\delta y\ge1$, which absorbs the $+1$ in $N_3$. The exponents are convenient, not optimized.

**Classical comparison [Community].** Tao's lecture notes on Linnik's theorem prove a special case of Gallagher's prime number theorem in progressions [Gallagher1970], with relative error $\exp(-c\log x/\log q)$ for $x\ge q^C$, following Chapter 18 of Iwaniec–Kowalski. They too truncate the explicit formula at a fixed power of the modulus: Exercise 5 takes $T=q^2$, with error $O(xq^{-2}\log^2q)$ for $x\ge q^C$. The hint points out that a naive truncation gives $\log^2x$ instead of $\log^2q$ when $x$ is extremely large compared with $q$, and that removing the last factor $\log x$ needs more than the bound $\Lambda(n)\le\log n$. The notes' Theorem 2 keeps the power saving $O(\log^2q/q)$ as a separate error term next to $\exp(-c\log x/\log q)$. The archive meets both points differently. It keeps the factor $\log(2y)$ in $N_2$ and bounds it by $D_vM^2$ through the far condition, which confines the lemma to the far range. It then converts the power saving into the far-range normal form instead of carrying it separately. [Tao2015](https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/) · [Gallagher1970](https://doi.org/10.1007/BF01403187)

#### 4.10.5.7 Source map and reading boundary

Paths are relative to the root of the joined Lean archive with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The archive files read for this subsection (`PNTBAsmA`, `PNTBAsm`, `PNTBAsmB`, `DeuringHeilbronnM`, `PNTEOf`, `PNTGlue`, `PNTRangeA` and `PNTFinal`) were compared byte for byte with the members of that tarball.

| Role | Archive path and lines | Status |
|---|---|---|
| `num_alg`, statement and proof | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean:7–55` | [Lean, read] |
| $1\le\log x$ for $x\ge3$, and $(M^n)^{-1}=e^{-n\log M}$ | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean:57–63` | [Lean, read] |
| `num_main`, statement, witnesses and proof | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean:88–158` | [Lean, read] |
| Squared far condition and $M^{-1}\le e^{-c\log y/l}$ | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean:65–86` | [Lean, read], §4.10.3 |
| The call, $T$, $\delta$, $t$ and $E$, and the conversion of the output | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsm.lean:15–22,38,46–57,128–166` | [Lean, read], §4.10.3 |
| Origin of $N_4$, $N_5$ and the character count | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmB.lean:30–153` | [Lean, read], §4.10.3 |
| `PsiRelB`, `ExplicitS`, `SharpenS`, `ZeroSum`, `PsiRelBOf` and the weight $\eta$ | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DeuringHeilbronnM.lean:19–22,47–75,92–111` | Definitions |
| $c_1M^{-1}\le\eta(M)$ (`etaOf_lower`) | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean:141–167` | [Lean, read], §4.10.3 |
| The value of $v$ and the splice | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTRangeA.lean:161–167`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTGlue.lean:22–25`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:22–24` | [Lean, read], §4.10.3 |
| The differencing (`SharpenS`) | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharp.lean:69–156` | [Lean, read], §4.10.6 |
| Suppliers of $\kappa$, $C$, $E$ and the zero sum | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMain.lean:15`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSumL.lean:30`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDens.lean:19`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHB.lean:13` | [Lean] |
| Supplier of $h$, through Siegel's lower bound | `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:50–52`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:26–32` | [Lean] |

The proof bodies of Lemmas 4.10.2 and 4.10.3 are read in full (local R3). Their remaining dependencies are order and field lemmas and facts about $\log$, $\exp$ and real powers in Mathlib at the pinned commit `0df444a`, used at statement level [Lean]. Examples are `Real.log_le_sub_one_of_pos` (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:307`), `Real.rpow_def_of_pos` and `Real.rpow_natCast` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:51,62`) and `Real.exp_one_lt_d9` (`Mathlib/Analysis/Complex/ExponentialBounds.lean:38`). The numerical lemma is unconditional. Reading it raises the status of no analytic supplier. The differencing (`PNTSharp`) is read in §4.10.6. The smoothed explicit formula (`PNTExplMain`), the zero sum (`PNTZSumL`) with its zero-density (`PNTDens`) and Deuring–Heilbronn (`DeuringHeilbronnMB`, `PNTDHB`) inputs, and the Siegel input keep R2. Their proofs remain [Open] for the book's reading record.

### 4.10.6 The differenced explicit formula `differenced_explicit_formula`

The far-range proof in §4.10.3 cites three analytic inputs: `ExplicitS`, `SharpenS` and `ZeroSum`. `PNTFinal` supplies `SharpenS` by `differenced_explicit_formula`, and the far-range assembly feeds the output of `ExplicitS`, supplied by `smoothed_explicit_formula`, into it. This subsection proves `SharpenS` from the ten local lemmas of `PNTSharp`, `PNTSharpA` and `PNTSharpB`, and follows that one call. The smoothed formula itself, the zero sum, zero density, Deuring–Heilbronn repulsion and Siegel's bound remain named inputs.

#### 4.10.6.1 Motivation

For a Dirichlet character $\chi$ modulo $M$ write $\psi_\chi(v)=\sum_{n\le v}\Lambda(n)\chi(n)$, as in §4.10.2, and

$$
S_\chi(v)=\sum_{n\le v}\Lambda(n)\chi(n)\Bigl(\frac vn-1\Bigr),\qquad \frac{S_\chi(v)}{v}=\sum_{n\le v}\Lambda(n)\chi(n)\Bigl(\frac1n-\frac1v\Bigr)=\int_1^v\frac{\psi_\chi(t)}{t^2}\,dt .
$$

This is the archive's `Schi`, the Riesz-weighted prime sum of [Definition 3.1](03-landau-window-criterion.md#331-riesz-weighted-prime-sums-and-normalized-remainders). Its Mellin kernel is $v^w/(w(w-1))$: the archive's interface `PerronChi` writes $S_\chi(v)$ as $(2\pi i)^{-1}\int_{(\sigma_0)}\bigl(-L'/L\bigr)(w,\chi)\,v^w\,dw/(w(w-1))$ for $\sigma_0>1$. The kernel decays like $\lvert w\rvert^{-2}$. A contour shift therefore produces a zero sum that converges absolutely, and `ExplicitS` states the result in the form

$$
\frac{S_\chi(v)}{v}=K+\mathbf 1_{\chi=1}(\log v-1)-\sum_{\rho\in Z}m(\rho)\frac{v^{\rho-1}}{\rho(\rho-1)}+(\text{error at most }E).
$$

Heuristically [Expository], the term $\log v-1$ is the residue of the double pole at $w=1$ for the principal character, $K$ is the constant term there, and each zero $\rho$ contributes $-m(\rho)v^{\rho-1}/(\rho(\rho-1))$.

The far range needs the sharp sum $\psi_\chi(y)$ with zero terms $y^\rho/\rho$, because the exceptional main term $F_\chi(y)$ of §4.10.2 is $-y^{\beta}/\beta$. The passage is a difference quotient. Away from the integers, $\frac{d}{dv}\bigl(S_\chi(v)/v\bigr)=\psi_\chi(v)/v^2$, so in the variable $-1/v$ the derivative of $S_\chi(v)/v$ is $\psi_\chi(v)$. Differencing between $y$ and $u=(1+\delta)y$ recovers $\psi_\chi(y)$ up to the prime powers in $(y,u]$. On the right side the same difference removes $K$, turns $\log v-1$ into approximately $y$, and turns each $v^{\rho-1}/(\rho(\rho-1))$ into approximately $y^\rho/\rho$. There are three costs. The error is multiplied by the reciprocal $c=y(1+\delta)/\delta$ of the step in $-1/v$. The prime powers in the step interval contribute up to $(\delta y+1)\log(2y)$. Each kernel is differenced only approximately, with a defect of at most $2\delta y^{\operatorname{Re}\rho}$. A small step helps the last two costs and hurts the first; §4.10.5 shows how the archive balances them with $\delta=M^{-5}$ and $T=M^{12}$.

The constant $K$ deserves a word. For a nonprincipal $\chi$ it is $-L'/L(1,\chi)$ in the archive's supplier. If $L(s,\chi)$ has a real zero $\beta$ close to $1$, this is, heuristically, about $-1/(1-\beta)$, and nothing in the archive estimates it. Differencing removes $K$ exactly. This works because `ExplicitS` chooses the list $Z$, the weights $m$ and the constant $K$ after the truncation height $T$ but before $y$, so the same data serve both differencing points.

#### 4.10.6.2 Two calculations and two failures [Expository]

Take $M=8$, $y=10$ and the largest permitted step $\delta=1/2$, so that $u=15$ and $c=yu/(u-y)=30$. The characters are the principal character $\chi_0$ modulo $8$ and the character $\chi_8$ of §4.10.1, with values $(1,-1,-1,1)$ on $(1,3,5,7)$. The prime powers in $(10,15]$ are $11$ and $13$. Their weights $c(1/n-1/u)$ are

$$
30\Bigl(\frac1{11}-\frac1{15}\Bigr)=\frac8{11},\qquad 30\Bigl(\frac1{13}-\frac1{15}\Bigr)=\frac4{13},
$$

both in $[0,1]$, as Lemma 4.10.4 below asserts. Write $\Phi(v)$ for the residual of the smoothed formula (§4.10.6.3), so that the hypothesis of `SharpenS` is $\lvert\Phi(y)\rvert,\lvert\Phi(u)\rvert\le E$. All numbers below are rounded to six decimals. They were computed with 50-digit arithmetic, and the difference identity of Theorem 4.10.7 holds to that precision in each case.

**Calculation A: the principal character and the removed pole.** Here $L(s,\chi_0)=(1-2^{-s})\zeta(s)$ has a pole at $1$. For $\chi=1$ the archive uses the entire function $(s-1)L(s,\chi_0)$, Mathlib's `LFunctionTrivChar₁`, whose value at $1$ is $\prod_{p\mid 8}(1-p^{-1})=1/2$. Its constant is $K=-\frac{d}{ds}\bigl((s-1)L(s,\chi_0)\bigr)\big|_{s=1}\big/\tfrac12$ (`explicitFormulaConstant`). From $(s-1)\zeta(s)=1+\gamma(s-1)+O((s-1)^2)$ and $\frac{d}{ds}\log(1-2^{-s})=\log2/(2^s-1)$ one gets

$$
K=-\gamma-\log2\approx-1.270363 .
$$

Take $Z=\varnothing$. Then $S_{\chi_0}(10)/10=0.512890$ and $S_{\chi_0}(15)/15=0.789080$, so $\Phi(10)=0.480667$ and $\Phi(15)=0.351393$, and $E=0.480667$ is legal. The terms of the identity are:

- the left side $\psi_{\chi_0}(10)-10=\log315-10=-4.247427$, since $\Lambda$ takes the values $\log3,\log5,\log7,\log3$ at $3,5,7,9$;
- the differenced residual $c(\Phi(15)-\Phi(10))=-3.878242$, within $2cE=28.840042$;
- the interval term $A=\frac8{11}\log11+\frac4{13}\log13=2.533139$, within $(u-y+1)\log u=6\log15=16.248301$;
- the pole term $P=30\log\frac32-10=2.163953$, within $[0,\delta y]=[0,5]$.

Indeed $-3.878242-2.533139+2.163953=-4.247427$ up to rounding. The constant $K$ appears in none of the three pieces on the right; another choice of $K$ changes only $E$. The midpoint $K=-0.854333$ gives the smallest legal value $E=0.064637$. The archive's bound $4yE/\delta+4(\delta y+1)\log(2y)$ equals $38.453+71.898=110.351$ for $K=-\gamma-\log 2$ and $77.069$ for the midpoint, against $\lvert-4.247427\rvert$. The pole term shows why $\delta$ is bounded. The difference quotient of $\log v-1$ is $c\log(1+\delta)=y\cdot\frac{1+\delta}{\delta}\log(1+\delta)$, which lies between $y$ and $(1+\delta)y$; at $\delta=1/2$ it exceeds $y$ by $21.6\%$.

**Calculation B: a real character with an exceptional slot and a double pair.** Take $\chi=\chi_8$ and the model list $Z=\{\beta,\rho,\bar\rho\}$ with $\beta=999/1000$, the counterfactual zero of §4.10.1, of weight $m(\beta)=1$, and $\rho=0.96+3i$ with $m(\rho)=m(\bar\rho)=2$. These are not zeros of $L(s,\chi_8)$. `SharpenS` asks of the list only that $1/2\le\operatorname{Re}\rho<1$, and the example follows how weights pass through the differencing. Now $\psi_{\chi_8}(10)=-\log3-\log5+\log7+\log3=\log\frac75=0.336472$, there is no pole term, and $A=-\frac8{11}\log11-\frac4{13}\log13=-2.533139$ because $\chi_8(11)=\chi_8(13)=-1$.

The $\beta$-slot contributes $m(\beta)v^{\beta-1}/(\beta(\beta-1))$ to $\Phi(v)$: $-998.698763$ at $v=10$ and $-998.293907$ at $v=15$. This is close to $-1/(1-\beta)=-1000$ and nearly constant. The weighted pair contributes $-0.233570$ and $0.203849$. With $S_{\chi_8}(10)/10=-0.321684$ and $S_{\chi_8}(15)/15=-0.394906$, the midpoint constant is $K=-998.869490$ and $E=0.384526$. So $K$ absorbs the large, almost constant contribution of the slot. For a genuine exceptional zero the supplier's constant $-L'/L(1,\chi_1)$ is, heuristically, also about $-1/(1-\beta_1)$. The differencing then returns

$$
\sum_{\rho'\in Z}m(\rho')\frac{y^{\rho'}}{\rho'}=\frac{y^\beta}{\beta}+4\operatorname{Re}\frac{y^\rho}{\rho}=9.986988+4\cdot2.328389=19.300542 ,
$$

and the left side is $\psi_{\chi_8}(10)+19.300542=19.637014$. The kernel defects (§4.10.6.3) are as follows.

| Zero | Weight | $y^{\rho'}/\rho'$ | Defect $d_\delta(\rho')$ | Bound $2\delta\lvert\rho'\rvert$ | $T(\rho')$ | Bound $2\delta y^{\operatorname{Re}\rho'}$ |
|---|---|---|---|---|---|---|
| $\beta=0.999$ | $1$ | $9.986988$ | $0.216149$ | $0.999$ | $2.158675$ | $9.977001$ |
| $\rho=0.96+3i$ | $2$ | $2.328389-1.721038i$ | $-0.068618+0.646136i$ | $3.149857$ | $0.952254+1.622550i$ | $9.120108$ |
| $\bar\rho$ | $2$ | conjugate | conjugate | $3.149857$ | conjugate | $9.120108$ |

The identity reads $19.637014=23.071565+2.533139-2.158675-2\cdot2\cdot0.952254$, where $23.071565=c(\Phi(15)-\Phi(10))=2cE$ and the imaginary parts of $T(\rho)$ and $T(\bar\rho)$ cancel. For $\beta$ the first-order value $\beta\delta/2=0.24975$ of the defect is close to the true $0.216149$. For $\rho$, where $\delta\lvert\rho\rvert\approx1.57$, the first-order value $\rho\delta/2=0.24+0.75i$ is no longer accurate. The weights enter the output linearly, and they enter the remainder budget $20\delta y\sum m(\rho')y^{\operatorname{Re}\rho'-1}=100\,(10^{-0.001}+4\cdot10^{-0.04})=464.574$ in the same way. The archive's full bound is $567.234$. The $\beta$-slot leaves the differencing as $y^\beta/\beta$, which is $-F_{\chi_1}(y)$ in the notation of §4.10.2. In the far range `one_char` cancels one copy against $F_\chi$, and the remaining weight, here $0$, goes into $W_\chi$; the pair of weight $2$ goes into $W_\chi$ entirely.

**Two failures without the step remainder.** Keep $\chi_8$, $Z=\varnothing$ and the midpoint $K$. For $9\le y<11$ one has $\psi_{\chi_8}(y)=\log\frac75=0.336472$, and the next prime power is $11$, with $\chi_8(11)=-1$.

- *Dropping the interval term.* Take $y=19/2$ and $\delta=1/5$, so $u=57/5$ and $c=57$. The interval holds $11$ with weight $57(\frac1{11}-\frac5{57})=\frac2{11}$, so $A=-\frac2{11}\log11=-0.435981$. Here $E=0.000873$ and $4yE/\delta=0.165848$. Without its last term the bound would read $0.336472\le0.165848$, which is false. The identity explains why: $\psi_{\chi_8}(y)=c(\Phi(u)-\Phi(y))-A=-0.099509+0.435981$, and no choice of $K$ affects $A$. With the interval term the bound is $34.321$.
- *Dropping the boundary integer.* Take $y=10.99$ and $u=11.0016$, so $\delta y=0.0116<1$ and $\delta\approx0.001056$. The interval $(10.99,11.0016]$ still contains $11$, with weight $y(u-11)/(11(u-y))=0.137806$, so $A=-0.330443$. Here $E=2.89\cdot10^{-7}$ and $4yE/\delta=0.012045$. Keeping only the length part $4\delta y\log(2y)=0.143382$ of the interval term gives $0.155427<0.336472$, so the inequality fails. The $+1$ in $\delta y+1$ counts the integer that an interval of length less than $1$ can still contain. With it the bound is $12.516$.

#### 4.10.6.3 Definitions

Fix a positive integer $M$, a Dirichlet character $\chi$ modulo $M$, a finite set $Z\subset\mathbb C$, a weight function $m:\mathbb C\to\mathbb N$, a constant $K\in\mathbb C$, and reals $y\ge2$ and $\delta>0$. Put

$$
u=(1+\delta)y,\qquad c=\frac{yu}{u-y}=\frac{y(1+\delta)}{\delta}.
$$

The **smoothed residual** at $v>0$ is

$$
\Phi(v)=\frac{S_\chi(v)}{v}-K-\mathbf 1_{\chi=1}(\log v-1)+\sum_{\rho\in Z}m(\rho)\frac{v^{\rho-1}}{\rho(\rho-1)},
$$

with $v^{w}$ the principal power of the positive real $v$. The **interval term**, the **pole term** and, for $\rho\notin\{0,1\}$, the **kernel defect** and the **differenced zero term** are

$$
A=\sum_{y<n\le u}\Lambda(n)\chi(n)\,c\Bigl(\frac1n-\frac1u\Bigr),\qquad P=\mathbf 1_{\chi=1}\bigl(c\log(1+\delta)-y\bigr),
$$

$$
d_\delta(\rho)=\frac{1+\delta}{\delta}\cdot\frac{(1+\delta)^{\rho-1}-1}{\rho-1}-1,\qquad T(\rho)=c\,\frac{u^{\rho-1}-y^{\rho-1}}{\rho(\rho-1)}-\frac{y^\rho}{\rho}.
$$

**The interface `SharpenS`.** Its hypotheses are (i) $1/2\le\operatorname{Re}\rho<1$ for all $\rho\in Z$; (ii) $y\ge2$; (iii) $0<\delta\le1/2$; (iv) $\lvert\Phi(y)\rvert\le E$ and $\lvert\Phi(u)\rvert\le E$ for one real $E$. Its conclusion is

$$
\Bigl\lvert\psi_\chi(y)-\mathbf 1_{\chi=1}y+\sum_{\rho\in Z}m(\rho)\frac{y^\rho}{\rho}\Bigr\rvert\le\frac{4yE}{\delta}+20\delta y\sum_{\rho\in Z}m(\rho)y^{\operatorname{Re}\rho-1}+4(\delta y+1)\log(2y).
$$

The hypotheses do not require the elements of $Z$ to be zeros, the weights to be positive, or $K$ to have any particular value. They do require one character, one list with its weights, one constant and one kernel at both points $y$ and $u$.

**The interface `ExplicitS`.** For every $\kappa\in(0,1/20]$ there is $C>0$ such that for every $M\ge3$, every $\chi$ modulo $M$ and every $T\ge2$ there are $Z$, $m$ and $K$ with:

1. each $\rho\in Z$ is a zero of $L(s,\chi)$ other than the pole slot ($\chi\ne1$ or $\rho\ne1$), with $1-\kappa<\operatorname{Re}\rho$ and $\lvert\operatorname{Im}\rho\rvert\le T+1$;
2. every such zero with $\operatorname{Re}\rho\ge1-\kappa/2$ and $\lvert\operatorname{Im}\rho\rvert\le T$ lies in $Z$;
3. $m\ge1$ on $Z$, and $m(\rho)=1$ whenever $L'(\rho,\chi)\ne0$;
4. $\sum_{\rho\in Z,\ \lvert\operatorname{Im}\rho-t\rvert\le1}m(\rho)\le C\log(M(\lvert t\rvert+2))$ for every real $t$;
5. for every $y\ge2$, $\lvert\Phi(y)\rvert\le C\bigl((MT)^Cy^{-\kappa/2}+\log y\,\log^2(MT)/T\bigr)$.

The supplier `smoothed_explicit_formula` takes for $Z$ the zeros of `exLF` with $\sigma_1<\operatorname{Re}\rho$ and $\lvert\operatorname{Im}\rho\rvert<T'$, where $\sigma_1$ and $T'$ depend only on $(\kappa,M,\chi,T)$. It takes for $m$ the analytic order `exOrd`, and for $K$ the value $-\mathrm{exLF}'(1)/\mathrm{exLF}(1)$ (`explicitFormulaConstant`). Here `exLF` is $L(s,\chi)$ for $\chi\ne1$, and for $\chi=1$ it is $(s-1)L(s,\chi)$, extended to $s=1$ by the value $\prod_{p\mid M}(1-p^{-1})$.

#### 4.10.6.4 Lemmas, theorem and the call

**Lemma 4.10.4 (the difference quotient of the smoothed sum; `sharp_identity`, `sharp_term`, `sharp_arith`) [Lean, read].** Let $\chi$ be a Dirichlet character modulo some $N$, let $1\le y<u$ be real, and put $c=yu/(u-y)$. Then

$$
c\Bigl(\frac{S_\chi(u)}u-\frac{S_\chi(y)}y\Bigr)-\psi_\chi(y)=\sum_{\lfloor y\rfloor<n\le\lfloor u\rfloor}\Lambda(n)\chi(n)\,c\Bigl(\frac1n-\frac1u\Bigr).
$$

Every weight $c(1/n-1/u)$ in the sum lies in $[0,1]$, every summand has modulus at most $\log u$, and the left side has modulus at most $(u-y+1)\log u$.

**Lemma 4.10.5 (the kernel defect; `sharp_cpow_sub_one`, `differenced_kernel_bound`, `sharp_kernel`, `sharp_zero_term`) [Lean, read].** Let $\rho\in\mathbb C$ with $\rho\ne0$, $\rho\ne1$ and $\operatorname{Re}\rho\le1$, and let $\delta>0$.

1. For real $t\ge1$, $\lvert t^\rho-1\rvert\le\lvert\rho\rvert(t-1)$.
2. $\bigl\lvert\frac{(1+\delta)^{\rho-1}-1}{\rho-1}+(1+\delta)^{-1}-1\bigr\rvert\le\lvert\rho\rvert\delta^2$.
3. If $\delta\le1/2$, then $\lvert d_\delta(\rho)\rvert\le2\delta\lvert\rho\rvert$.
4. If $1/2\le\operatorname{Re}\rho<1$, $0<\delta\le1/2$ and $y>0$, then $T(\rho)=\frac{y^\rho}{\rho}\,d_\delta(\rho)$ and $\lvert T(\rho)\rvert\le2\delta y\,y^{\operatorname{Re}\rho-1}$.

**Lemma 4.10.6 (the removed pole; `sharp_log_term`) [Lean, read].** For real $y,\delta>0$ and $c=y(1+\delta)/\delta$,

$$
0\le c\bigl((\log((1+\delta)y)-1)-(\log y-1)\bigr)-y\le\delta y .
$$

The archive states the two-sided bound $\lvert\cdot\rvert\le\delta y$; the proof gives both inequalities.

**Theorem 4.10.7 (the differenced explicit formula, `differenced_explicit_formula : SharpenS`) [Lean, read].** Let $M\ge1$, $\chi$ modulo $M$, $Z$, $m$, $K$, $E$, $y$, $\delta$ satisfy hypotheses (i)–(iv) of `SharpenS`. Then the **difference identity**

$$
\psi_\chi(y)-\mathbf 1_{\chi=1}y+\sum_{\rho\in Z}m(\rho)\frac{y^\rho}{\rho}=c\bigl(\Phi(u)-\Phi(y)\bigr)-A+P-\sum_{\rho\in Z}m(\rho)T(\rho),
$$

and the four terms on the right are bounded by $2cE$, $(\delta y+1)\log((1+\delta)y)$, $\delta y$ and $2\delta y\sum_{\rho\in Z}m(\rho)y^{\operatorname{Re}\rho-1}$. Consequently the conclusion of `SharpenS` holds.

**Corollary 4.10.8 (the call with the smoothed formula) [Lean, read].** Assume `ExplicitS`. Fix $\kappa\in(0,1/20]$ and its constant $C$. Let $M\ge3$, let $\chi$ be a character modulo $M$, let $T\ge2$, and let $(Z,m,K)$ be the data of `ExplicitS` at $(M,\chi,T)$. Then every $\rho\in Z$ satisfies $1-\kappa<\operatorname{Re}\rho<1$. For all $y\ge2$ and $0<\delta\le1/2$,

$$
\Bigl\lvert\psi_\chi(y)-\mathbf 1_{\chi=1}y+\sum_{\rho\in Z}m(\rho)\frac{y^\rho}{\rho}\Bigr\rvert\le\frac{4yE_T(y)}{\delta}+20\delta y\sum_{\rho\in Z}m(\rho)y^{\operatorname{Re}\rho-1}+4(\delta y+1)\log(2y),
$$

with $E_T(y)=C\bigl((MT)^Cy^{-\kappa/2}+\log(2y)\log^2(MT)/T\bigr)$.

*Quantifiers and endpoints.* In `ExplicitS` the order is $\forall\kappa\ \exists C\ \forall M,\chi,T\ \exists(Z,m,K)\ \forall y$, and $\delta$ is quantified in `SharpenS`, so the corollary holds for every $\delta\in(0,1/2]$ once $(Z,m,K)$ is fixed. The truncation height enters only through $E_T$ and the clauses on $Z$; `SharpenS` itself mentions neither $T$ nor the lower bound on $M$. The step is strict at $0$ and closed at $1/2$, and $y\ge2$ and $T\ge2$ are closed. `psi_relative_far_range` uses the corollary for $8\mid M$, $T=M^{12}$ (so $T\ge8$) and $\delta=M^{-5}$ (so $\delta\le1/2$).

#### 4.10.6.5 Proofs

*Proof of Lemma 4.10.4.* For $v>0$, $S_\chi(v)/v=\sum_{n\le v}\Lambda(n)\chi(n)(1/n-1/v)$ (`sharp_schi_div`). Split the sum up to $\lfloor u\rfloor$ at $\lfloor y\rfloor$ (`sharp_split`). The terms with $n\le y$ contribute

$$
\sum_{n\le y}\Lambda(n)\chi(n)\Bigl[\Bigl(\frac1n-\frac1u\Bigr)-\Bigl(\frac1n-\frac1y\Bigr)\Bigr]=\Bigl(\frac1y-\frac1u\Bigr)\psi_\chi(y),
$$

and $c(1/y-1/u)=1$. This gives the identity. For $\lfloor y\rfloor<n\le\lfloor u\rfloor$ one has $y<n\le u$, so the weight $w_n=c(1/n-1/u)=y(u-n)/(n(u-y))$ is nonnegative. Moreover $w_n\le1$ is equivalent to $y(u-n)\le n(u-y)$, that is, to $y\le n$. With $\lvert\chi(n)\rvert\le1$ and Mathlib's $\Lambda(n)\le\log n\le\log u$, each summand has modulus at most $\log u$. Finally, $\lfloor u\rfloor-\lfloor y\rfloor\le u-y+1$ because $\lfloor u\rfloor\le u$ and $\lfloor y\rfloor>y-1$. Since $\log u\ge0$, the sum has modulus at most $(u-y+1)\log u$. $\square$

*Proof of Lemma 4.10.5.* (1) For $s\in[1,t]$ the map $s\mapsto s^\rho$ has derivative $\rho s^{\rho-1}$, since positive reals lie in the slit plane. Its modulus is $\lvert\rho\rvert s^{\operatorname{Re}\rho-1}\le\lvert\rho\rvert$ because $s\ge1$ and $\operatorname{Re}\rho\le1$. The mean value inequality (Mathlib's `norm_image_sub_le_of_norm_deriv_le_segment'`) gives $\lvert t^\rho-1\rvert\le\lvert\rho\rvert(t-1)$.

(2) Let $f(t)=(t^{\rho-1}-1)/(\rho-1)+(t^{-1}-1)$ on $[1,1+\delta]$. Then $f(1)=0$ and

$$
f'(t)=t^{\rho-2}-t^{-2}=\frac{t^\rho-1}{t^2}.
$$

By (1) and $t^2\ge1$, $\lvert f'(t)\rvert\le\lvert\rho\rvert(t-1)\le\lvert\rho\rvert\delta$ on $[1,1+\delta)$. The mean value inequality gives $\lvert f(1+\delta)\rvert\le\lvert\rho\rvert\delta\cdot\delta$.

(3) Put $g=((1+\delta)^{\rho-1}-1)/(\rho-1)$ and $e=g+(1+\delta)^{-1}-1$. Since $\frac{1+\delta}{\delta}\bigl((1+\delta)^{-1}-1\bigr)=-1$, we have $d_\delta(\rho)=\frac{1+\delta}{\delta}g-1=\frac{1+\delta}{\delta}e$. By (2), $\lvert d_\delta(\rho)\rvert\le\frac{1+\delta}{\delta}\lvert\rho\rvert\delta^2=(1+\delta)\delta\lvert\rho\rvert\le2\delta\lvert\rho\rvert$.

(4) The strip condition gives $\rho\ne0$, $\rho\ne1$ and $\operatorname{Re}\rho\le1$. For the positive reals $1+\delta$ and $y$, $((1+\delta)y)^{\rho-1}=(1+\delta)^{\rho-1}y^{\rho-1}$ (Mathlib's `mul_cpow_ofReal_nonneg`), and $y^\rho=y\cdot y^{\rho-1}$. Hence

$$
c\,\frac{u^{\rho-1}-y^{\rho-1}}{\rho(\rho-1)}-\frac{y^\rho}\rho=\frac{y^\rho}{\rho}\Bigl(\frac{1+\delta}{\delta}\cdot\frac{(1+\delta)^{\rho-1}-1}{\rho-1}-1\Bigr)=\frac{y^\rho}{\rho}\,d_\delta(\rho).
$$

Since $\lvert y^\rho\rvert=y^{\operatorname{Re}\rho}$, (3) gives $\lvert T(\rho)\rvert\le(y^{\operatorname{Re}\rho}/\lvert\rho\rvert)\,2\delta\lvert\rho\rvert=2\delta y\,y^{\operatorname{Re}\rho-1}$. $\square$

*Proof of Lemma 4.10.6.* The quantity equals $c\log(1+\delta)-y=y\bigl(\frac{1+\delta}{\delta}\log(1+\delta)-1\bigr)$. The inequalities $1-x^{-1}\le\log x\le x-1$ at $x=1+\delta$ give $\delta/(1+\delta)\le\log(1+\delta)\le\delta$, hence $1\le\frac{1+\delta}{\delta}\log(1+\delta)\le1+\delta$. $\square$

*Proof of Theorem 4.10.7.* *Step 1, the identity.* In $c(\Phi(u)-\Phi(y))$ the constant $K$ cancels, and so do the two constants $-1$ of the pole slot:

$$
c\bigl(\Phi(u)-\Phi(y)\bigr)=c\Bigl(\frac{S_\chi(u)}u-\frac{S_\chi(y)}y\Bigr)-\mathbf 1_{\chi=1}c\log(1+\delta)+\sum_{\rho\in Z}m(\rho)\,c\,\frac{u^{\rho-1}-y^{\rho-1}}{\rho(\rho-1)}.
$$

By Lemma 4.10.4 the first term is $\psi_\chi(y)+A$. By definition the second is $-\mathbf 1_{\chi=1}y-P$, and each summand of the third is $m(\rho)(y^\rho/\rho+T(\rho))$. Rearranging gives the difference identity. In the archive this is the identity `key`, proved by `ring` after the zero sum has been distributed (`hsum`).

*Step 2, four bounds.* Since $\lvert\Phi(y)\rvert\le E$, $E\ge0$, and $\lvert c(\Phi(u)-\Phi(y))\rvert\le c(\lvert\Phi(u)\rvert+\lvert\Phi(y)\rvert)\le2cE$. Lemma 4.10.4 with $1\le y<u$ gives $\lvert A\rvert\le(u-y+1)\log u=(\delta y+1)\log((1+\delta)y)$. Lemma 4.10.6 gives $\lvert P\rvert\le\delta y$, and $P=0$ if $\chi\ne1$. Lemma 4.10.5(4) and $m\ge0$ give $\bigl\lvert\sum m(\rho)T(\rho)\bigr\rvert\le2\delta y\sum m(\rho)y^{\operatorname{Re}\rho-1}$.

*Step 3, the exported constants.* As $\delta\le1/2$, $c=(1+\delta)y/\delta\le\frac32y/\delta$, so $2cE\le3yE/\delta\le4yE/\delta$. As $(1+\delta)y\le2y$, $\log((1+\delta)y)\le\log(2y)$. As $2y\ge4>e$ (Mathlib's $e<2.7182818286$), $\log(2y)\ge1$, so $\delta y\le(\delta y+1)\log(2y)$. Adding, the left side of the difference identity is at most $4yE/\delta+2(\delta y+1)\log(2y)+2\delta y\sum m(\rho)y^{\operatorname{Re}\rho-1}$, which is at most the conclusion of `SharpenS`. $\square$

*Proof of Corollary 4.10.8.* Each $\rho\in Z$ has $\operatorname{Re}\rho>1-\kappa\ge19/20$. If $\operatorname{Re}\rho\ge1$, Mathlib's `LFunction_ne_zero_of_one_le_re` would contradict $L(\rho,\chi)=0$, because the pole slot is excluded ($\chi\ne1$ or $\rho\ne1$). Hence $Z$ satisfies (i). For $v\in\{y,(1+\delta)y\}$ one has $2\le y\le v\le2y$ since $\delta\le1$. Clause 5 at $v$, together with $v^{-\kappa/2}\le y^{-\kappa/2}$ and $\log v\le\log(2y)$, gives $\lvert\Phi(v)\rvert\le E_T(y)$. Theorem 4.10.7 with $E=E_T(y)$ finishes the proof. In the archive these steps are `hre`, `hEu` and `hsharp` of `psi_relative_far_range`, after `choose Z m K h1 h2 h3 h4 h5 h6` has fixed the data of `ExplicitS` at $T=M^{12}$ for every character. $\square$

#### 4.10.6.6 Remarks

**One character, one list, one kernel.** The theorem compares the smoothed formula at two points with the same character, the same $(Z,m,K)$ and the same kernel $v^{\rho-1}/(\rho(\rho-1))$. This is why $K$ cancels and why each element of $Z$ can be differenced on its own. If $K$ were allowed to depend on the point, the difference would retain $c(K_u-K_y)$, with $c\ge y/\delta$, and nothing in the hypotheses would bound it. The supplier makes the data independent of $y$ by its choice of $\sigma_1$ and $T'$, which depend on $(\kappa,M,\chi,T)$ only.

**The exceptional slot.** Suppose the selected pair $(\chi_1,\beta_1)$ of §4.10.2 is listed. It then occupies the slot $\rho=\beta_1$ of $Z_{\chi_1}$, with the same weight at both points. Its smoothed term is close to the constant $m(\beta_1)/(1-\beta_1)$ (calculation B), and the constant $K$ offsets it. The differencing returns $m(\beta_1)y^{\beta_1}/\beta_1+m(\beta_1)T(\beta_1)$, with $\lvert T(\beta_1)\rvert\le2\delta y^{\beta_1}\le2\delta y$, which has exactly the shape of the exceptional main term $F_{\chi_1}$. In the far range, `one_char` moves one copy into $F_\chi$, and the remainder of that copy is charged once, as $N_4=20\delta y$ in §4.10.5. A selected zero below $1-\kappa/2$ may be absent from the list. `one_char` then pays $2yt$ for it ($N_5$), and the differencing is unaffected.

**Endpoints.** The bound $y\ge2$ is used twice: for $\log(2y)\ge1$, and in the corollary to evaluate `ExplicitS` at $v\ge y\ge2$. The strict bound $\delta>0$ allows the division. The bound $\delta\le1/2$ gives $c\le3y/(2\delta)$. The kernel bound and $u\le2y$ need only $\delta\le1$. At $\delta=1/2$ the pole term reaches $0.216y$ (calculation A). The kernel bound uses the condition $1/2\le\operatorname{Re}\rho$ only to know that $\rho\ne0$. The far-range consumer uses it once more, for $\lvert\rho\rvert\ge1/2$. The condition $\operatorname{Re}\rho<1$ keeps the pole slot $\rho=1$ out of $Z$; the term $\mathbf 1_{\chi=1}(\log v-1)$ accounts for it separately.

**Where the constants go.** The proof gives $3yE/\delta+2(\delta y+1)\log(2y)+2\delta y\sum m(\rho)y^{\operatorname{Re}\rho-1}$; the archive exports $4$, $4$ and $20$. In §4.10.5 the first becomes $N_1+N_2=M\cdot4yE/\delta$ after summing over at most $M$ characters, and the second becomes $N_3=4M(\delta y+1)\log(2y)$. The third becomes $N_4=20\delta y$ for the selected copy, plus $20\delta yW_\chi\le20yW_\chi$, which is absorbed into $22yW_\chi$.

**The kernel defect at large height.** When $\delta\lvert\rho\rvert$ is small, $d_\delta(\rho)=\rho\delta/2+O(\lvert\rho\rvert^2\delta^2)$, so the bound $2\delta\lvert\rho\rvert$ loses a factor of about $4$. When $\delta\lvert\rho\rvert$ is large, the differenced kernel itself is small and $d_\delta(\rho)$ is close to $-1$. The bound $\lvert T(\rho)\rvert\le2\delta y^{\operatorname{Re}\rho}$ is then weaker than the trivial estimate of order $y^{\operatorname{Re}\rho}/\lvert\rho\rvert$. With $\delta=M^{-5}$ and zeros up to height $M^{12}+1$, both regimes can occur in the far range. The archive uses the single height-uniform bound and pays for it through the zero sum $W_\chi$.

**Classical comparison [Paper].** Landau's *Handbuch* (1909, §53, pp. 193–194) passes from a smoothed sum to $\psi$ in the same way. He starts from $\sum_{n\le x}\Lambda(n)\log(x/n)=x+O\bigl(xe^{-\sqrt[11]{\log x}}\bigr)$, sets $\delta=e^{-\sqrt[12]{\log x}}$, replaces $x$ by $(1+\delta)x$ and subtracts. He bounds the step interval by $0\le\sum_{x<n\le x+\delta x}\Lambda(n)\log\frac{x+\delta x}{n}<\log(1+\delta)\log(2x)(\delta x+1)$, using $\Lambda(n)\le\log n$ and $[x+\delta x]-[x]<\delta x+1$, and obtains $\psi(x)=\frac{\delta}{\log(1+\delta)}x+O(\delta x\log x)$. Lemma 4.10.4 is the twisted analogue, with the weight $1/n-1/v$ in place of $\log(v/n)$. The interval weights again lie in $[0,1]$, and the same $+1$ appears. There are two differences. Landau's coefficients are nonnegative, which makes his interval sum at least $0$, while $S_\chi$ has coefficients of both signs, so the archive's bound is two-sided. And the archive keeps the zeros, differencing each kernel term by Lemma 4.10.5 instead of absorbing them into the error. Tao's 254A Notes 2 take the direct route for comparison: Theorem 21 there is a truncated explicit formula for $\psi(x)$ obtained from a truncated Perron formula, and Exercise 22 is a smoothed explicit formula whose zero sum converges absolutely. [Landau1909](https://archive.org/details/handbuchderlehre01landuoft/page/n216/mode/1up) · [Tao2014](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/)

#### 4.10.6.7 Source map and reading boundary

Paths are relative to the root of the joined Lean archive with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The archive files cited here (`PNTSharp`, `PNTSharpA`, `PNTSharpB`, `DeuringHeilbronnM`, `PNTBAsm`, `PNTFinal`, `PNTExplMain`, `PNTExplDefs`, `LogDerivRegionChiOf`, `SiegelWalfiszAP`, `Statement`) were compared byte for byte with the members of that tarball.

| Role | Archive path and lines | Status |
|---|---|---|
| `differenced_explicit_formula`: identity `key`, bounds and exported constants | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharp.lean:69–156` | [Lean, read] |
| `sharp_zero_term` (Lemma 4.10.5(4)) and `sharp_log_term` (Lemma 4.10.6) | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharp.lean:13–42,44–67` | [Lean, read] |
| `sharp_cpow_sub_one`, `differenced_kernel_bound`, `sharp_kernel` (Lemma 4.10.5(1)–(3)) | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpA.lean:9–24,26–60,62–81` | [Lean, read] |
| `sharp_split`, `sharp_schi_div`, `sharp_identity`, `sharp_term`, `sharp_arith` (Lemma 4.10.4) | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpB.lean:12–23,25–37,39–69,71–104,106–123` | [Lean, read] |
| `ExplicitS`, `SharpenS`, `PsiRelBOf` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DeuringHeilbronnM.lean:53–75,111` | Definitions |
| `Schi`, `Fchi`, `PerronChi`; `psiChi`; `IsLZero` | `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:11–20`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean:10–11`, `src/Formalism/LandauZeroFreeBounds/Statement.lean:12–13` | Definitions |
| `exLF`, `exOrd`, `exKer`, `explicitFormulaConstant` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplDefs.lean:12–20` | Definitions |
| `smoothed_explicit_formula`: the constant $C$, the choice of $(Z,m,K)$ and list clauses 1–4 from its named inputs | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMain.lean:15–74` | [Lean, read] |
| `smoothed_explicit_formula`: the residual estimate (see §4.10.7) | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMain.lean:75–97`, with `ex_choose`, `ex_box`, and `exm_core` | [Lean, read] for the assembly |
| `explicitS_proof'` and the top-level wiring | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:16,22–24` | [Lean, read], §4.10.3 |
| The call: $C$ at $\kappa$, $T=M^{12}$, $\delta=M^{-5}$, $E$, `hre`, `hEu`, `hsharp` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsm.lean:18,29–38,52–91` | [Lean, read], §4.10.3 |
| Consumers of the output (`one_char`, the sum over characters) | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsm.lean:92–138`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmB.lean:11–153` | [Lean, read], §4.10.3 |

The proof bodies in the first four rows are read in full (local R3), together with the witness choice in `smoothed_explicit_formula`. Their remaining dependencies are Mathlib declarations at the pinned commit `0df444a`, used at statement level [Lean]: `norm_image_sub_le_of_norm_deriv_le_segment'` (`Mathlib/Analysis/Calculus/MeanValue.lean:326`), `Complex.hasStrictDerivAt_cpow_const` (`Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:190`), `Complex.cpow_sub`, `Complex.cpow_natCast` and `Complex.mul_cpow_ofReal_nonneg` (`Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean:94,124,186`), `Complex.norm_cpow_eq_rpow_re_of_pos`, `Real.rpow_sub_one` and `Real.rpow_le_one_of_one_le_of_nonpos` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:337,455,668`), `Real.log_le_sub_one_of_pos`, `Real.one_sub_inv_le_log_of_pos`, `Real.log_le_log` and `Real.le_log_iff_exp_le` (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:307,312,151,165`), `Real.exp_one_lt_d9` (`Mathlib/Analysis/Complex/ExponentialBounds.lean:38`), `ArithmeticFunction.vonMangoldt_nonneg` and `vonMangoldt_le_log` (`Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean:80,151`), `DirichletCharacter.norm_le_one` (`Mathlib/NumberTheory/DirichletCharacter/Bounds.lean:33`), `DirichletCharacter.LFunction_ne_zero_of_one_le_re` (`Mathlib/NumberTheory/LSeries/Nonvanishing.lean:398`) and `DirichletCharacter.LFunctionTrivChar₁` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:338`), together with the floor and finite-sum lemmas named in the proofs. Reading `SharpenS` raises the status of no other analytic supplier. Section 4.10.7 reads the residual assembly of `smoothed_explicit_formula` from named analytic inputs. The zero sum (`PNTZSumL`) with its zero-density (`PNTDens`) and Deuring–Heilbronn (`DeuringHeilbronnMB`, `PNTDHB`) inputs, and the Siegel input behind $c_1$ keep R2. Their proofs remain [Open] for the book's reading record.

### 4.10.7 The residual of the smoothed explicit formula

#### 4.10.7.1 Motivation

The difference theorem in §4.10.6 evaluates a smoothed formula twice. It needs the same finite zero sum and the same constant at both arguments. The archive selects the left edge and the two heights using the zeros of one character at a fixed nominal height. Only the right edge depends on the evaluation point. The four residual budgets come from the full Perron integral's omitted tails, the left edge, and the two horizontal edges.

#### 4.10.7.2 Two modulus-eight calculations [Expository]

Take $\kappa=1/20$ and use model zero configurations. In the archive (`ex_negLD_bound`, `PNTExplNeg.lean:33`), $C_2=2C_0+100/7+C_3$, where §4.10.8 gives $C_0=180(\log(10100C_G)+3)$ and §4.10.9 reads the archive's actual growth witness $C_G=\max(9,6)=9$. Meanwhile `LogDerivRight.lean:14` defines $C_3=\max(\max(B,0),-\zeta'(1+\varepsilon/2)/\zeta(1+\varepsilon/2))>0$ from the Laurent remainder proof read in [§4.10.10](#41010-the-pole-subtracted-zeta-logarithmic-derivative), so $C_3=0$ is not the witness used by the archive's proof. Section 4.10.10 supplies a positive numerical witness for the same inequalities. Replacing $C_3>0$ by $0$ yields the explicit strict lower bound $C_2>C_2^{\mathrm{lb}}:=360(\log90900+3)+100/7\approx5204.59$. Because the four budget expressions below increase strictly with $(C_2,C_3)$, evaluating them at the baseline $(C_2^{\mathrm{lb}},0)$ gives explicit lower bounds for the archive's budgets at these parameters rather than admissible witnesses. With clearance $d$, left edge $\sigma$, height $H$, and $N=2C_2\log(8T)/d$, the four normalized budgets to be derived are
$$
a=\frac{e(\log y+C_3)}{\pi H},\qquad
b=\frac{H(N+4/(3\kappa))y^{\sigma-1}}{\pi\sigma(1-\sigma)},\qquad
c_-=c_+=\frac{3e(N+1)}{2\pi H^2}.
$$

**Principal character.** Take $T=2$ and an empty model box up to height $5$. The midpoints of $[19/20,77/80]$ and $[2,3]$ give $\sigma=153/160$ and $H=5/2$. The selection rule gives $d=1/160$. Zeros beyond height $5$ are at height distance greater than $5/2$. At $y=10$ the right edge is $1+1/\log10$, the baseline $N^{\mathrm{lb}}=320C_2^{\mathrm{lb}}\log16\approx4.617661\times10^{6}$, $\sigma(1-\sigma)=1071/25600$, and $y^{\sigma-1}=10^{-7/160}$. Substitution at $(C_2^{\mathrm{lb}},0)$ gives the budget lower bounds
$$
a^{\mathrm{lb}}=\frac{2e\log10}{5\pi}\approx0.796930,\qquad
b^{\mathrm{lb}}=\frac{(5/2)(N^{\mathrm{lb}}+80/3)10^{-7/160}}{\pi(1071/25600)}\approx7.941731\times10^{7},
$$
and each horizontal budget exceeds $3e(N^{\mathrm{lb}}+1)/(2\pi(5/2)^2)\approx9.589103\times10^{5}$, so the archive's total budget exceeds $8.133514\times10^{7}$. The residue contributes $\log10-1$ after normalization and the constant is $-\gamma-\log2$. The model finite sum is empty.

**Real character $\chi_8$.** Use the same model slots as §4.10.6, namely $\beta=999/1000$ and $24/25\pm3i$ of orders $1,2,2$. Take $T=4$, with three distinct model zeros in the selection box up to height $7$. The choices $\sigma=153/160$ and $H=17/4$ are admissible points picked by hand, not the midpoints produced by the selection lemma with $n=3$. Their minimum gaps $3/800$ and $5/4$ both exceed $d=1/640$. Zeros beyond height $7$ have height distance greater than $11/4$. All three chosen slots lie in the rectangle. At $y=16$ the right edge is $1+1/\log16$ and the baseline $N^{\mathrm{lb}}=1280C_2^{\mathrm{lb}}\log32\approx2.308831\times10^{7}$. Substitution at $(C_2^{\mathrm{lb}},0)$ gives the budget lower bounds
$$
a^{\mathrm{lb}}=\frac{4e\log16}{17\pi}\approx0.564470,\qquad
b^{\mathrm{lb}}=\frac{(17/4)(N^{\mathrm{lb}}+80/3)16^{-7/160}}{\pi(1071/25600)}
\approx6.613051\times10^{8}.
$$
Each horizontal budget exceeds $3e(N^{\mathrm{lb}}+1)/(2\pi(17/4)^2)\approx1.659014\times10^{6}$, so the archive's total budget exceeds $6.646231\times10^{8}$. The pole correction is zero for this character, although the universal budget still includes the pole allowance $80/3$. The real model zero contributes $16^{\beta-1}/(\beta(\beta-1))$ to the residual and the pair contributes $4\Re(16^{z-1}/(z(z-1)))$ with $z=24/25+3i$. These are parameter and lower-bound budget calculations for the model, with the actual zero configurations left unspecified.

#### 4.10.7.3 Definitions and analytic inputs

Let $p_\chi$ be the principal-character indicator and let $f_\chi$ denote the entire continuation of $(s-1)L(s,\chi)$ for the principal character, and $L(s,\chi)$ otherwise. Write $m(\rho)$ for its order at $\rho$, $K=-f_\chi'(1)/f_\chi(1)$, $D=-L'/L$, $k_y(s)=y^s/(s(s-1))$ and $F_y=Dk_y$. Take $y^s=\exp(s\log y)$. Use the pinned zero identification and nonvanishing input: $f_\chi(1)\ne0$, its zeros are the archive's Dirichlet zeros, and they have real part less than one. Orders are positive there. A nonzero $L'(\rho,\chi)$ gives order one, since in the principal case $f_\chi'(\rho)=(\rho-1)L'(\rho,\chi)$.

- **Local expansion (`ex_local`).** For $M\ge3$ the exact finite zero set $D_t$ in the closed disc of radius $2/15$ at $101/100+it$ has total order at most $C_0\log(M(|t|+2))$ for an absolute $C_0>0$. In the concentric closed disc of radius $1/15$, away from zeros, the difference between $f_\chi'/f_\chi$ and $\sum_{\rho\in D_t}m(\rho)/(s-\rho)$ is bounded in modulus by the same majorant. Section 4.8.8 gives the method and the right-half-plane input `l_log_deriv_right`, namely $|D(s)|\le 1/(\Re s-1)+C_3$ for $\Re s>1$ with absolute $C_3\ge0$. Proposition 4.10.10 in §4.10.8 proves the exact `ex_local` specialization, with $C_0=180(\log(10100C_G)+3)$.
- **Perron (`perron_formula_character`).** Lemma 4.8.7.3 in §4.8.7 gives absolute convergence of $I_\infty=\int_{\mathbb R}F_y(c+it)\,dt$ for $y\ge1$ and $c>1$, and $S_\chi(y)=I_\infty/(2\pi)$ with $S_\chi(y)=\sum_{n\le y}\Lambda(n)\chi(n)(y/n-1)$.
- **Rectangle (`ex_rect_Fchi`).** For $0<\sigma<1<c$, $H>0$, the exact interior list $Z$ and a zero-free boundary, the positive contour integral equals $2\pi iQ$, where $Q=Ky+p_\chi y(\log y-1)-\sum_{\rho\in Z}m(\rho)k_y(\rho)$. The residue at $1$ follows from $D=p_\chi/(s-1)-f_\chi'/f_\chi$ and $k_y(s)=y/(s-1)+y(\log y-1)+O(s-1)$. At a zero $\rho$ the residue is $-m(\rho)k_y(\rho)$, and the pole at $0$ sits outside. Theorem 4.10.13 in §4.10.8 proves this identity from the archive's production proof.

#### 4.10.7.4 Lemma and conditional theorem [Lean, read]

**Box and selection lemma.** The set $B(U)$ of zeros with $\Re\rho\ge9/10$ and $|\Im\rho|\le U$ is finite for every $U\ge0$. Its total order in $|\Im\rho-t|\le1$ is at most $C_4\log(M(|t|+2))$, and $|B(U)|\le C_4(U+1)\log(M(U+2))$, with $C_4=180C_0$. For $0<\kappa\le1/20$ and $T\ge2$, choose
$$
1-\kappa\le\sigma\le1-3\kappa/4,\quad T\le H\le T+1,\quad
0<d\le1/20.
$$
The real-part gap $|\Re\rho-\sigma|\ge d$ holds throughout $B(T+3)$. The height gap $\big||\Im\rho|-H\big|\ge d$ holds for all zeros with $\Re\rho\ge9/10$. One can take $d=\kappa/(8(|B(T+3)|+1))$, with $d\ge\kappa/(C_1(T+1)\log(M(T+2)))$ and $C_1=8(4C_4+1)$.

**Residual theorem.** Assume the named inputs. For any choice satisfying the intervals and gaps, take $Z=\{\rho:f_\chi(\rho)=0,\ \Re\rho>\sigma,\ |\Im\rho|<H\}$ and $N=2C_2\log(MT)/d$ for an absolute $C_2>0$. For every $y\ge2$,
$$
R_\chi(y)=S_\chi(y)/y-K-p_\chi(\log y-1)+
\sum_{\rho\in Z}\frac{m(\rho)y^{\rho-1}}{\rho(\rho-1)}
$$
has modulus at most $a+b+c_-+c_+$ as given in §4.10.7.2. With the lemma's choice,
$$
|R_\chi(y)|\le C\left((MT)^C y^{-\kappa/2}+\log y\,\log^2(MT)/T\right).
$$
The quantifiers are $\forall\kappa\in(0,1/20]\ \exists C>0\ \forall M\ge3,\chi\bmod M,T\ge2\ \exists Z,m,K\ \forall y\ge2$. The proof also supplies the finite-list clauses of `ExplicitS`.

#### 4.10.7.5 Proof

**From discs to the box.** A zero with $\Re\rho\ge9/10$ and $|\Im\rho-u|\le1/14$ lies in $D_u$, since $\Re\rho<1$ and $(11/100)^2+(1/14)^2<(2/15)^2$. Round $7\Im\rho$ to the nearest integer. The centers $k/7$ with $|k|\le7\lceil U\rceil$ cover the box, and filtering their finite union gives exactly $B(U)$. For the window at $t$, round $7(\Im\rho-t)$ instead, obtaining fifteen centers $t+k/7$, $|k|\le7$. For $a\ge0$ and $0\le b\le a+1$, $M(b+2)\le2M(a+2)\le(M(a+2))^2$. Each local logarithm is therefore at most twice the window logarithm, giving a window bound with coefficient $30C_0$. Repeated zeros in the cover only increase the sum of nonnegative orders. The integer windows with centers $|j|\le\lceil U\rceil$ cover all of $B(U)$, by rounding imaginary parts. There are at most $3(U+1)$ such centers, each costing at most $60C_0\log(M(U+2))$. Each zero contributes at least its unit count. This gives $C_4$ for cardinality and allows the same constant for windows.

**Avoid the zeros.** For a forbidden set of $n$ real points in or outside an interval of length $l$, test the midpoints of its $n+1$ equal subintervals. Each forbidden point can lie strictly within $l/(2(n+1))$ of at most one midpoint. At least one midpoint therefore has the desired clearance. Apply this to the two projections of $B(T+3)$, onto real parts and absolute heights, in intervals of lengths $\kappa/4$ and $1$. The projections have at most $|B(T+3)|$ points. This proves both gaps with the displayed $d$ inside the box, and outside the box the height gap exceeds $2$. From $T+4\le2(T+1)$, the logarithm comparison $\log(M(T+5))\le2\log(M(T+2))$ from $T+5\le2(T+2)$ and $M(T+2)\ge2$, and $1\le(T+1)\log(M(T+2))$, the box cardinality bound gives the claimed lower bound for $d$.

**Control the numerator.** For $19/20\le\Re s\le3$, $s\ne1$, suppose zeros with $\Re\rho\ge9/10$ and $|\rho-s|\le1/5$ have distance at least $d$. At $\Re s\ge107/100$ the right-half-plane bound is at most $100/7+C_3$. Otherwise $s$ lies within $1/15$ of $101/100+i\Im s$, and it cannot itself be a zero by the clearance hypothesis. The local zeros are within $2/15+1/15=1/5$ of $s$. Those with $\Re\rho<9/10$ have horizontal distance greater than $1/20\ge d$. The finite sum costs at most $C_0\log(M(|\Im s|+2))/d$ by the total order bound. The local remainder costs at most the same because $d\le1$. Adding $p_\chi/|s-1|$ proves the numerator estimate with $C_2=2C_0+100/7+C_3$, using $\log(M(|\Im s|+2))\ge1$.

Set $c=1+1/\log y$, so $1<c\le3$, $\sigma\ge19/20$ and $y^c=ey$. On the three moved sides $M(|\Im s|+2)\le M(T+3)\le(MT)^2$. On the left side the nearby zeros have $|\Im\rho|\le H+1/5\le T+3$, so real-part clearance applies. Also $|s-1|\ge1-\sigma\ge3\kappa/4$. Thus $|D|\le N+4/(3\kappa)$ there. On the horizontal sides, the reverse triangle inequality bounds distance below by the absolute-height gap and $|s-1|\ge H\ge2$. Both numerators are at most $N+1$. The gaps exclude boundary zeros on these three sides. The right side lies in $\Re s>1$.

**Integrate the four terms.** Let $R,L$ be the upwards parameter integrals on right and left, and $B,P$ the rightwards parameter integrals on bottom and top. The rectangle says $B-P+iR-iL=2\pi iQ$. Multiplying by $i$ and using Perron gives
$$
R_\chi(y)=\frac{I_\infty-2\pi Q}{2\pi y}
=\frac{(I_\infty-R)+L+i(B-P)}{2\pi y}.
$$
On the right tail, $|s(s-1)|\ge t^2$ and $|D|\le\log y+C_3$, giving $2(\log y+C_3)ey/H$ after integrating $t^{-2}$ over $|t|>H$. On the left, $|s(s-1)|\ge\sigma(1-\sigma)$ and $|y^s|=y^\sigma$. Multiply the resulting pointwise bound by the length $2H$. On each horizontal edge, $|s(s-1)|\ge H^2$, $|y^s|\le ey$, and the length $c-\sigma$ is at most $3$. The triangle inequality after division by $2\pi y$ gives exactly the four displayed budgets.

**Uniformize.** Put $X=MT$, $\ell=\log X\ge1$, $W=\log y\,\ell^2/T$, $G=6C_1C_2/\kappa$ and $q=4/(3\kappa)$. The lower bound on $d$, $T+1\le3T/2$, and $\log(M(T+2))\le2\ell$ give $N\le GT\ell^2$. Since $e<\pi$, $H\ge T$, and $\log y\ge1/2$, the tail is at most $(1+2C_3)W$. Each horizontal budget is at most $3(G+1)W$, from $N+1\le(G+1)T\ell^2$ and $e/(2\pi)\le\log y$. For the left edge, $\sigma(1-\sigma)\ge57\kappa/80$, hence $\pi\sigma(1-\sigma)\ge2\kappa$. Also $H(N+q)\le(3/2)(G+q)(T\ell)^2\le(3/2)(G+q)X^4$ and $y^{\sigma-1}\le y^{-\kappa/2}$. Use the archive's looser coefficient $A_L=3(G+q)(2/\kappa)$ and take $A_W=1+2C_3+6(G+1)$. Then $C=\max(4,C_4,A_L,A_W)$ increases both coefficients and, since $X\ge1$, increases $X^4$ to $X^C$.

**Supply the list and the downstream call.** Filter $B(T+1)$ by $\sigma<\Re\rho$ and $|\Im\rho|<H$ to obtain exactly $Z$. Each member has $1-\kappa<\Re\rho<1$ and $|\Im\rho|\le T+1$. A zero with $\Re\rho\ge1-\kappa/2$ and $|\Im\rho|\le T$ has real part greater than $\sigma$. It also has $|\Im\rho|<H$, since equality would contradict the gap. Order positivity and simplicity follow from the stated facts for $f_\chi$. Filtering only decreases the nonnegative order sum in each unit window, whose coefficient $C_4$ is at most $C$. This pays all clauses, including the closed endpoints $M=3$, $T=2$, and $y=2$.

The archive's `explicitS_proof'` passes the result to `psi_relative_far_range`, which fixes $T=M^{12}$ and selects one triple for each $\chi$. The step $\eta=M^{-5}$ puts both arguments $u=y,(1+\eta)y$ in $[y,2y]$. There $u^{-\kappa/2}\le y^{-\kappa/2}$ and $\log u\le\log(2y)$, so both residuals have the common bound
$$
E=C\left((MT)^C y^{-\kappa/2}+\log(2y)\log^2(MT)/T\right).
$$
The real parts lie in $[1/2,1)$, as required by §4.10.6. The consumer applies the difference theorem with this $E$ and the same triple, so $K$ cancels. The clearance $d$ controls the contour, while $\eta$ controls the later difference.

#### 4.10.7.6 Remarks and source map

**Failure without real-part clearance [Expository].** In the local model $f(s)=s-\sigma$ with zero at height $0$ and no principal pole, $-k_y(s)/(s-\sigma)$ has a pole on the left path because $k_y(\sigma)\ne0$. The integral there fails absolute convergence, although all horizontal gaps can hold. Moving the zero to $\sigma+\epsilon$ gives numerator modulus $1/|\epsilon|$ at the center of the left side, so even avoiding exact equality cannot give a pointwise bound using fixed $d>0$.

**Classical comparison [Paper].** Tao's Theorem 21 chooses an avoiding height in $[T,T+1]$ and a left real part by averaging integrated logarithmic derivatives of zeta. Exercise 22 uses a compactly supported smooth weight on the log scale. Here the pointwise coordinate gaps and the rational Mellin kernel give four separate finite-contour budgets. [Tao2014, Theorem 21 and Exercise 22](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/#vnmef)

Archive A2 joined SHA-256 is 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. Short PNT paths are relative to src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/.

| Role | Location | Reading |
| --- | --- | --- |
| Box and contour selection | PNTExplBox.lean:11–211; PNTExplPick.lean:11–110 | Local R3 [Lean, read] |
| Numerator and edge bounds | PNTExplNeg.lean:11–102; PNTExplEdge.lean:12–148 | Local R3 [Lean, read] for the displayed estimates |
| Core residual and final estimate | PNTExplMainB.lean:15–168; PNTExplMainA.lean:9–249; PNTExplMain.lean:15–97 | Local R3 [Lean, read] |
| Named predecessors | src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean:283 and LRight.lean:116 in the same directory | Inherited Perron (§4.8.7) and right-half-plane input (§4.8.8) |
| Exact analytic suppliers | `ex_local` at PNTExplLocL.lean:86 and `ex_rect_Fchi` at PNTExplRectF.lean:154, read in §4.10.8; `exLF_growth` at PNTExplLF.lean:129, read in §4.10.9 | Local R3 [Lean, read] in §§4.10.8–4.10.9 |
| Interface and consumer | DeuringHeilbronnM.lean:53–75; PNTFinal.lean:16,24; PNTBAsm.lean:38,55–91; PNTSharp.lean:69–156 | Interface and call checked; difference proof inherited |

The levels record the extent of source reading. See the [source ledger](../sources/SOURCES.md#chapter-4-4107-the-smoothed-explicit-residual).

### 4.10.8 The local expansion and the rectangle identity: `ex_local` and `ex_rect_Fchi`

Section 4.10.7 takes two analytic statements of the archive as named inputs: the local expansion `ex_local` and the finite rectangle identity `ex_rect_Fchi`. This subsection proves both from their production proofs. It shows how a local principal part splits off the zero contribution with exact multiplicities. It also shows how one rectangle integral of $F_y$ produces $Ky$, the principal-character correction $y\log y-y$ and the multiplicity-weighted zero sum. These come with the orientation and the signs that the four residual budgets of §4.10.7 consume.

#### 4.10.8.1 Motivation

Two functions carry the same zeros. The numerator of the Perron integrand is $D=-L'/L$, and for the principal character $L$ has a pole at $1$. The archive therefore works with $f_\chi$, which is $(s-1)L(s,\chi)$ for the principal character and $L(s,\chi)$ otherwise. This function is entire, nonzero at $1$, and has the same zeros as $L$ away from $1$. Tao removes the pole of $\zeta$ in the same way, multiplying by $(s-1)$, before he applies a local disc estimate [[Tao2014, Proposition 19](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/)]. A disc estimate needs an upper bound on the disc and a lower bound at the centre. Near the line $\operatorname{Re}s=101/100$ both are available for $f_\chi$, uniformly in the modulus.

Near a zero $\rho$ the logarithmic derivative is unbounded, but its singular part there is exactly $m/(s-\rho)$, where $m$ is the order of the zero. After the finitely many principal parts are subtracted, the remainder has size $O(\log(M(|t|+2)))$. The weight must be the analytic order. The archive's general disc interface `LandauLocal` only provides some weights $m_\rho\ge1$, and these would not identify the residues of the contour integrand. The archive therefore proves a version with analytic orders, `ex_landau_ord`, and specializes it in `ex_local`.

For the contour, $F_y=Dk_y$ with $k_y(s)=y^s/(s(s-1))$ is meromorphic on $\operatorname{Re}s>0$. Inside a rectangle whose left side has real part $\sigma_1>0$, its only poles are at $1$ and at the zeros. At a zero the residue is $-m\,k_y(\rho)$. At $1$ the simple pole of $k_y$ meets the regular part $-f_\chi'/f_\chi$ of $D$ and gives $Ky$. For the principal character $D$ also has a simple pole at $1$, so $F_y$ has a double pole there. The extra residue is $y\log y-y$, the derivative of $y^s/s$ at $s=1$. The pole of $k_y$ at $0$ stays outside because $\sigma_1>0$. Once no zero lies on the boundary the identity is exact, and §4.10.7 then estimates its four edges.

#### 4.10.8.2 Two modulus-eight calculations [Expository]

**Principal character modulo $8$.** Here $L(s,\chi_0)=\zeta(s)(1-2^{-s})$ and $f(s)=(s-1)\zeta(s)(1-2^{-s})$. Hence $f(1)=1-1/2=1/2$, which is the archive's value $\prod_{p\mid8}(1-p^{-1})$. From $(s-1)\zeta(s)=1+\gamma(s-1)+O((s-1)^2)$ and $\frac{d}{ds}\log(1-2^{-s})=\log2/(2^s-1)$ we get $f'(1)/f(1)=\gamma+\log2$, so
$$
K=-\gamma-\log2\approx-1.270363 .
$$
The zeros of $f$ are the zeros of $\zeta$ in the critical strip and the points $2\pi ik/\log2$ with $k\in\mathbb Z$ on $\operatorname{Re}s=0$, where the Euler factor vanishes. The point $s=0$ is one of them. For $s=1+w$ we have $D(1+w)=1/w+K+O(w)$ and $k_y(1+w)=y/w+y(\log y-1)+O(w)$, so
$$
F_y(1+w)=\frac{y}{w^2}+\frac{Ky+y\log y-y}{w}+O(1).
$$
At $y=10$ the residue at $1$ is $10(\log10-1-\gamma-\log2)=10(\log5-1-\gamma)\approx0.322222$.

- *Rectangle $[1/4,2]\times[-10,10]$.* In [[Odlyzko's table](https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1)] the first zero of $\zeta$ in the upper half-plane is $\rho_1=1/2+i\gamma_1$ with $\gamma_1\approx14.134725$. Conditionally on $\zeta$ having no zero in $0<\operatorname{Re}s<1$ with $|\operatorname{Im}s|\le10$ (supported numerically by that table and by the argument-principle quadrature below), and since the Euler-factor zeros have real part $0<1/4$, we have $Z=\emptyset$, the boundary is zero-free, and Theorem 4.10.13 gives $2\pi i\cdot0.322222$.
- *Rectangle $[1/4,2]\times[-20,20]$.* The next tabulated zero height is $\gamma_2\approx21.022$. Conditionally on $Z=\{\rho_1,\bar\rho_1\}$ being the complete critical-strip zero set in $|\operatorname{Im}s|\le20$ with both zeros simple (consistent with the numerical argument-principle value $2$ below), $\rho_1(\rho_1-1)=-(1/4+\gamma_1^2)\approx-200.040455$ and
$$
k_{10}(\rho_1)=-\frac{\sqrt{10}\,e^{i\gamma_1\log10}}{1/4+\gamma_1^2}\approx-0.006738-0.014300i .
$$
The pair contributes $-(k_{10}(\rho_1)+k_{10}(\bar\rho_1))=-2\operatorname{Re}k_{10}(\rho_1)\approx0.013476$, so $Q\approx0.335698$. The Euler-factor zeros $\pm2\pi i/\log2\approx\pm9.0647i$ and $\pm18.1294i$ lie within the height bound, but on $\operatorname{Re}s=0$, outside the rectangle.
- *The rectangle of §4.10.7.2*, $[153/160,1+1/\log10]\times[-5/2,5/2]$: conditionally on its containing no zero of $\zeta$, $Q/y=K+\log10-1=\log5-1-\gamma\approx0.032222$, the normalized residue with constant $-\gamma-\log2$ used in that calculation.
- *`ex_local` at $M=8$, $t=0$.* The centre is $c_0=101/100$, and the lower bound (I) below gives $|f(c_0)|\ge1/10100$. Take the archive's actual growth witness $C_G=\max(9,6)=9$, read in §4.10.9. Then $B=10100\cdot9\cdot8\cdot3^2=6544800$ and $\log B\approx15.6942$. The disc of radius $2/15$ therefore carries total order at most $\log B/\log2\approx22.64$, that is at most $22$. On the disc of radius $1/15$ the remainder is at most $180\log B\approx2824.95$. Conditionally on this disc containing no zero of $\zeta$, the remainder equals $f'/f$, whose modulus at $101/100\pm1/15$ and $101/100\pm i/15$ is $\approx1.19$, $1.34$, $1.26$ and $1.26$. The constant of Proposition 4.10.10 for $C_G=9$ is $C_{\mathrm{loc}}=180(\log90900+3)\approx2595.15$, and at $t=0$ its bound $C_{\mathrm{loc}}\log16\approx7195.29$ is far from sharp.

**Real character $\chi_8=(8/\cdot)$.** Its values are $\chi_8(1)=\chi_8(7)=1$ and $\chi_8(3)=\chi_8(5)=-1$, so it is even and primitive of conductor $8$. Here $f=L(\cdot,\chi_8)$ is entire and there is no pole correction. Grouping the series in blocks of eight gives
$$
L(1,\chi_8)=\int_0^1\frac{1-x^2-x^4+x^6}{1-x^8}\,dx=\int_0^1\frac{1-x^2}{1+x^4}\,dx=\frac{\log(1+\sqrt2)}{\sqrt2}\approx0.623225 .
$$
The summed terms $x^{8k}(1-x^2)(1-x^4)$ are nonnegative on $[0,1]$, so monotone convergence justifies the interchange. The last integral follows from the primitive $-\frac1{2\sqrt2}\log\frac{x^2-\sqrt2x+1}{x^2+\sqrt2x+1}$ and from $(2+\sqrt2)/(2-\sqrt2)=(1+\sqrt2)^2$. Numerically $L'(1,\chi_8)\approx0.393950$, so $K=-L'(1,\chi_8)/L(1,\chi_8)\approx-0.632115$. Because $\chi_8$ is even, $L(0,\chi_8)=0$, and numerically $L'(0,\chi_8)\approx0.881374\ne0$. This trivial zero sits at the pole of $k_y$, and the hypothesis $\sigma_1>0$ keeps it outside. At $y=16$ the residue at $1$ is $16K\approx-10.113839$. Put $\Lambda(s)=(8/\pi)^{s/2}\Gamma(s/2)L(s,\chi_8)$. Numerically, the real function $\Lambda(1/2+it)$ changes sign at $t\approx4.899974$, $7.628429$ and $10.806588$.

- *Rectangle $[1/4,2]\times[-3,3]$.* Conditionally on $L(s,\chi_8)$ having no zero in $[1/4,2]\times[-3,3]$, the integral is $2\pi i\cdot16K\approx2\pi i\,(-10.113839)$.
- *Rectangle $[1/4,2]\times[-6,6]$.* Conditionally on $Z=\{1/2\pm i\gamma_1^{(8)}\}$ ($\gamma_1^{(8)}\approx4.899974$) being the only zeros in $[1/4,2]\times[-6,6]$ and both being simple, $k_{16}(\rho)\approx-0.086400-0.140432i$, the pair contributes $-2\operatorname{Re}k_{16}(\rho)\approx0.172800$, and $Q\approx-9.941039$.
- *The rectangle of §4.10.7.2*, $[153/160,1+1/\log16]\times[-17/4,17/4]$: conditionally on its containing no zero of $L(s,\chi_8)$, $Q/y=K$. The constants of `ex_local` do not depend on the character, so at $t=0$ with $C_G=9$ the same $B=6544800$, order bound $22$ and remainder bound $2824.95$ apply.

**Numerical supplement.** The four integrals over rectangles with left side $1/4$ were computed by 20-digit quadrature and agree with $2\pi iQ$ to within $2\times10^{-13}$, while numerical quadrature of the argument principle gives $0,2,0,2$ to the same precision. These floating-point computations corroborate the conditional zero lists, signs and residues above, and do not constitute certified zero counts or part of the proofs below.

#### 4.10.8.3 Definitions and named inputs

Fix $M\ge1$ and a character $\chi$ modulo $M$. Put $p_\chi=1$ if $\chi$ is principal and $p_\chi=0$ otherwise.

- $f_\chi$ (`exLF`) is $(s-1)L(s,\chi)$ for the principal character, with value $\prod_{p\mid M}(1-p^{-1})$ at $s=1$ (Mathlib's `LFunctionTrivChar₁`), and $L(s,\chi)$ otherwise.
- $m_\chi(\rho)$ (`exOrd`) is the analytic order of $f_\chi$ at $\rho$, and $K_\chi=-f_\chi'(1)/f_\chi(1)$ (`explicitFormulaConstant`).
- For $y>0$ put $y^w=\exp(w\log y)$ and $k_y(w)=y^w/(w(w-1))$ (`exKer`). Further $D=-L'/L$ (`negLD`) and $F_y=Dk_y$ (`Fchi`).
- For $x_0<x_1$ and $y_0<y_1$ the rectangle integral (`rectInt`) is the positively oriented boundary integral
$$
I(g;x_0,x_1,y_0,y_1)=\int_{x_0}^{x_1}g(x+iy_0)\,dx-\int_{x_0}^{x_1}g(x+iy_1)\,dx+i\int_{y_0}^{y_1}g(x_1+it)\,dt-i\int_{y_0}^{y_1}g(x_0+it)\,dt .
$$
It uses only the values of $g$ on the boundary $\partial R$ (`exBdry`). In the notation of §4.10.7 the four parameter integrals are $B,P,R,L$ in this order, so $I=B-P+iR-iL$.

The proofs use the following inputs.

- (N) Facts about $f_\chi$ [Lean, read]; the Mathlib continuation and nonvanishing theorems behind them are used by statement. $f_\chi$ is entire and $f_\chi(1)\ne0$, and $L(s,\chi)\ne0$ on $\operatorname{Re}s\ge1$ except at the principal pole. Hence every zero of $f_\chi$ has real part less than $1$, and away from $1$ these zeros are the zeros of $L(s,\chi)$ (`exLF_differentiable`, `exLF_one_ne_zero`, `exLF_eq_zero_iff`, `exLF_re_lt_one`). Where $s\ne1$ and $f_\chi(s)\ne0$, $D(s)=p_\chi/(s-1)-f_\chi'(s)/f_\chi(s)$ (`negLD_eq_exLF`).
- (G) Growth, `exLF_growth` [Lean, read], proved in §4.10.9. There is $C_G\ge1$ with $|f_\chi(s)|\le C_GM(1+|s|)^2$ for all $M\ge1$, all $\chi$ modulo $M$ and $\operatorname{Re}s\ge1/2$. Section 4.10.9 reads the archive's witnesses $C_P=9$ in `lfunction_polynomial_growth` and $C_G=\max(C_P,6)=9$ in `exLF_growth`.
- (I) Centre lower bound, `exLF_lower` [Lean, read]. For $\operatorname{Re}s>1$, $|f_\chi(s)|\ge\min(1,|s-1|)(\operatorname{Re}s-1)/\operatorname{Re}s$. This follows from the inverse bound $|L(s,\chi)|^{-1}\le\sigma/(\sigma-1)$ of Theorem 4.8.8.4.
- (Lz) Zero-free disc estimate [Lean, read]. Let $h$ be holomorphic on $\overline B(c,r)$ with no zero on $\overline B(c,r/3)$, and let $|h|\le H|h(c)|$ on $\overline B(c,r)$ with $H\ge1$. Then $|h'/h|\le72\log H/r$ on $\overline B(c,r/6)$. This is Lemma 4.8.8.3 with $Z=\emptyset$. In the archive it is `landauLocal` with an empty zero list; `landauLocal` combines `zeroFactorization` with the disc bound `logDerivBoundOnBall` on the radius $r/3$.
- (Res) Rectangle residue theorem [Lean, read], read in §4.8.7. Let finitely many points $p$ lie strictly inside, let $G$ be holomorphic on an open set containing the closed rectangle, and let $g=G+\sum_pb_p/(w-p)$ away from the points $p$. Then $I(g)=2\pi i\sum_pb_p$.
- (Fac) Finite factorization on a disc, `zeroFactorization` [Lean, read], read in §4.8.8. Let $f$ be holomorphic on $\overline B(z_0,r)$ with $f(z_0)\ne0$, and let $0<R_1<r$. Then the zeros in $\overline B(z_0,R_1)$ form a finite set $Z_b$, and there are exponents $m\ge1$ and a function $h$ with $f=\prod_{Z_b}(w-\rho)^{m_\rho}h$. Here $h$ is holomorphic on $\overline B(z_0,r)$ and nonzero on $\overline B(z_0,R_1)$.

#### 4.10.8.4 The local expansion and the rectangle identity

**Lemma 4.10.9 (disc expansion with exact orders, `ex_landau_ord`) [Lean, read], given (Lz).** Let $r>0$ and $B\ge1$, and let $f$ be complex differentiable on $\overline B(z_0,r)$ with $f(z_0)\ne0$ and $|f|\le B|f(z_0)|$ there. Let $Z$ be the set of zeros of $f$ in $\overline B(z_0,r/3)$, and let $m_\rho$ be the analytic order of $f$ at $\rho$. Then $Z$ is finite, every $m_\rho\ge1$, and $\sum_{\rho\in Z}m_\rho\le\log B/\log2$. For every $s\in\overline B(z_0,r/6)$ with $f(s)\ne0$,
$$
\Big|\frac{f'(s)}{f(s)}-\sum_{\rho\in Z}\frac{m_\rho}{s-\rho}\Big|\le\frac{72\log B}{r}.
$$

**Proposition 4.10.10 (`ex_local`) [Lean, read], given (G), (I) and (Lz).** Put $C_{\mathrm{loc}}=180(\log(10100C_G)+3)>0$. This is the constant called $C_0$ in §4.10.7.3. Let $M\ge3$, let $\chi$ be a character modulo $M$, let $t\in\mathbb R$, and put $c_t=101/100+it$. Then the set $Z_t$ of zeros of $f_\chi$ in $\overline B(c_t,2/15)$ is finite and
$$
\sum_{\rho\in Z_t}m_\chi(\rho)\le C_{\mathrm{loc}}\log(M(|t|+2)).
$$
For every $s\in\overline B(c_t,1/15)$ with $f_\chi(s)\ne0$,
$$
\Big|\frac{f_\chi'(s)}{f_\chi(s)}-\sum_{\rho\in Z_t}\frac{m_\chi(\rho)}{s-\rho}\Big|\le C_{\mathrm{loc}}\log(M(|t|+2)).
$$
The constant depends only on $C_G$ and is the same for all $M$, $\chi$ and $t$.

**Lemma 4.10.11 (the double pole, `ex_rect_double` with `rectangle_double_pole`) [Lean, read], given (Res).** Let $y>0$, $0<x_0<1<x_1$ and $y_0<0<y_1$. Then
$$
I\Big(\frac{k_y(w)}{w-1};x_0,x_1,y_0,y_1\Big)=2\pi i\,(y\log y-y).
$$

**Theorem 4.10.12 (rectangle identity for an entire function, `ex_rect_logDeriv`) [Lean, read], given (Res) and (Fac).** Let $f$ be entire with $f(1)\ne0$, let $y>0$, and let $0<x_0<1<x_1$ and $y_0<0<y_1$. Let $Z$ be the set of zeros of $f$ in the open rectangle $(x_0,x_1)\times(y_0,y_1)$, and assume that every zero of $f$ in the closed rectangle lies in the open one. Then $Z$ is finite, and with $m_\rho$ the analytic order of $f$ at $\rho$,
$$
I\Big(-\frac{f'}{f}\,k_y;x_0,x_1,y_0,y_1\Big)=2\pi i\Big(-\frac{f'(1)}{f(1)}\,y-\sum_{\rho\in Z}m_\rho\,k_y(\rho)\Big).
$$

**Theorem 4.10.13 (`ex_rect_Fchi`) [Lean, read], given (N), (Res) and (Fac).** Let $\chi$ be a character modulo $M$, and let $y>0$, $0<\sigma_1<1<\sigma_0$ and $T'>0$. Put
$$
Z=\{\rho:\ f_\chi(\rho)=0,\ \sigma_1<\operatorname{Re}\rho,\ |\operatorname{Im}\rho|<T'\}.
$$
Assume that every zero $w$ of $f_\chi$ with $\sigma_1\le\operatorname{Re}w\le\sigma_0$ and $|\operatorname{Im}w|\le T'$ satisfies $\sigma_1<\operatorname{Re}w$ and $|\operatorname{Im}w|<T'$. Then
$$
I(F_y;\sigma_1,\sigma_0,-T',T')=2\pi i\Big(K_\chi y+p_\chi(y\log y-y)-\sum_{\rho\in Z}m_\chi(\rho)\,k_y(\rho)\Big).
$$
Each zero enters with weight $m_\chi(\rho)$ and with the sign of $-k_y(\rho)$. No condition $\operatorname{Re}\rho<\sigma_0$ is needed in $Z$, by (N). In both theorems the archive passes $Z$ as a `Finset` with exactly the displayed membership; the first step of the proof of Theorem 4.10.12 shows that the set is finite, so the two forms agree.

**Corollary 4.10.14 (the call in `exm_core`).** Take the parameters of §4.10.7.4: $0<\kappa\le1/20$, $T\ge2$, $1-\kappa\le\sigma_1\le1-3\kappa/4$, $T\le T'\le T+1$ and a gap $d>0$. Assume the real-part gap for the zeros with $\operatorname{Re}\rho\ge9/10$ and $|\operatorname{Im}\rho|\le T+3$, and the absolute-height gap for the zeros with $\operatorname{Re}\rho\ge9/10$. Let $Z$ be as there, $y\ge2$ and $\sigma_0=1+1/\log y$. Then Theorem 4.10.13 applies, and for the parameter integrals $B,P,R,L$ of §4.10.7.5,
$$
B-P+iR-iL=2\pi iQ,\qquad \frac{Q}{y}=K_\chi+p_\chi(\log y-1)-\sum_{\rho\in Z}\frac{m_\chi(\rho)\,y^{\rho-1}}{\rho(\rho-1)} .
$$
With $S_\chi(y)=I_\infty/(2\pi)$, the residual of §4.10.7 becomes $R_\chi(y)=(I_\infty-2\pi Q)/(2\pi y)=((I_\infty-R)+L+i(B-P))/(2\pi y)$. These are the four terms that §4.10.7.5 bounds.

#### 4.10.8.5 Proofs

**Proof of Lemma 4.10.9.** *Finiteness and orders.* The function $f$ is analytic on the open disc $B(z_0,r)$. Infinitely many zeros in the compact disc $\overline B(z_0,r/3)$ would accumulate at a point of $B(z_0,r)$. The identity theorem on the connected disc would then force $f\equiv0$, contrary to $f(z_0)\ne0$. For the same reason every order is finite, and at a zero it is at least $1$.

*Factorization with exact orders.* Put $P(w)=\prod_{\rho\in Z}(w-\rho)^{m_\rho}$. At $\rho\in Z$ write $f=(w-\rho)^{m_\rho}h_\rho$ near $\rho$ with $h_\rho(\rho)\ne0$. Then $k_\rho=h_\rho/\prod_{\sigma\in Z,\sigma\ne\rho}(w-\sigma)^{m_\sigma}$ is analytic at $\rho$, $k_\rho(\rho)\ne0$, and $f/P=k_\rho$ on a punctured neighbourhood of $\rho$. Define $g=f/P$ off $Z$ and $g(\rho)=k_\rho(\rho)$. Then $g$ is complex differentiable on $\overline B(z_0,r)$, $f=Pg$ there, and $g\ne0$ at every point of $Z$. The archive's `exists_factor_zeros_differentiableOn_nonvanishing` makes this construction, and its exponents are the analytic orders by definition.

*Counting.* Let $N=\sum_{\rho\in Z}m_\rho$. Since $|z_0-\rho|\le r/3$, $|P(z_0)|\le(r/3)^N$. On $|w-z_0|=r$ every $\rho\in Z$ has $|w-\rho|\ge2r/3$, so $|P(w)|\ge2^N(r/3)^N$. Therefore
$$
|g(w)|=\frac{|f(w)|}{|P(w)|}\le\frac{B\,|P(z_0)|\,|g(z_0)|}{|P(w)|}\le\frac{B}{2^N}\,|g(z_0)|\qquad(|w-z_0|=r).
$$
The maximum modulus principle extends the bound to $\overline B(z_0,r)$. At $w=z_0$, where $g(z_0)\ne0$, it gives $2^N\le B$, that is, $N\le\log B/\log2$.

*The zero-free factor.* The function $g$ has no zero on $\overline B(z_0,r/3)$: such a zero would be a zero of $f=Pg$, hence a point of $Z$, where $g\ne0$. Apply (Lz) to $g$ with $H=B/2^N\ge1$. On $\overline B(z_0,r/6)$ this gives $|g'/g|\le72\log(B/2^N)/r\le72\log B/r$.

*Splitting.* Let $s\in\overline B(z_0,r/6)$ with $f(s)\ne0$. Then $P(s)\ne0$ and $g(s)\ne0$, and the product rule gives $f'/f=P'/P+g'/g$ at $s$. Logarithmic differentiation of the finite product gives $P'(s)/P(s)=\sum_{\rho\in Z}m_\rho/(s-\rho)$. The difference in the lemma is therefore $g'(s)/g(s)$. $\square$

**Proof of Proposition 4.10.10.** *Lower bound at the centre.* Here $\operatorname{Re}c_t=101/100$ and $|c_t-1|\ge|\operatorname{Re}(c_t-1)|=1/100$, so (I) gives
$$
|f_\chi(c_t)|\ge\frac1{100}\cdot\frac{1/100}{101/100}=\frac1{10100}>0 .
$$
*Upper bound on the disc of radius $2/5$.* If $|z-c_t|\le2/5$, then $\operatorname{Re}z\ge101/100-2/5=61/100\ge1/2$ and $|z|\le2/5+101/100+|t|\le|t|+2$. By (G), $|f_\chi(z)|\le C_GM(|t|+3)^2$. Put $B=10100\,C_GM(|t|+3)^2\ge1$. Then $|f_\chi(z)|\le B/10100\le B\,|f_\chi(c_t)|$.

*Lemma 4.10.9 with $r=2/5$.* Then $r/3=2/15$, $r/6=1/15$ and $72/r=180$, the zero set is $Z_t$, and the orders are $m_\chi$. So the total order is at most $\log B/\log2$, and the remainder is at most $180\log B$.

*Comparison of logarithms.* Put $X=M(|t|+2)$. Then $X\ge6>e$, so $\log X\ge1$. Since $M\le X$ and $|t|+3\le X$, we have $B\le10100\,C_GX^3$. Using $\log(10100C_G)\ge0$ and $\log X\ge1$,
$$
\log B\le\log(10100C_G)+3\log X\le(\log(10100C_G)+3)\log X .
$$
Since $\log2\ge1/2$, also $\log B/\log2\le2\log B\le180\log B$. Both quantities are therefore at most $180(\log(10100C_G)+3)\log X=C_{\mathrm{loc}}\log X$. $\square$

For the count the factor $180$ is wasteful, but it costs nothing downstream, since §4.10.7 uses one constant for both clauses.

**Proof of Lemma 4.10.11.** Let $\varphi(w)=y^w/w$. It is holomorphic on $\operatorname{Re}w>0$, and the quotient rule gives $\varphi(1)=y$ and $\varphi'(1)=y\log y-y$. Let $G$ be the second difference quotient of $\varphi$ at $1$: $G(w)=(\varphi(w)-\varphi(1)-\varphi'(1)(w-1))/(w-1)^2$ for $w\ne1$ and $G(1)=\varphi''(1)/2$. It is holomorphic on $\operatorname{Re}w>0$, and for $w\ne1$
$$
\frac{k_y(w)}{w-1}=\frac{\varphi(w)}{(w-1)^2}=G(w)+\frac{y}{(w-1)^2}+\frac{y\log y-y}{w-1}.
$$
The closed rectangle lies in $\operatorname{Re}w>0$, and no edge passes through $1$. On each edge $-y/(w-1)$ is a primitive of $y/(w-1)^2$. Each edge integral of that term is the difference of the primitive at its endpoints, and the four differences cancel around the boundary. The remaining terms $G+(y\log y-y)/(w-1)$ have one simple pole inside, and (Res) with the single point $1$ gives $2\pi i(y\log y-y)$. $\square$

**Proof of Theorem 4.10.12.** *A disc around the rectangle.* Put $R_1=|x_0-1|+|x_1-1|+|y_0|+|y_1|+1$. Every point of the closed rectangle satisfies $|w-1|\le|\operatorname{Re}(w-1)|+|\operatorname{Im}w|<R_1$. Apply (Fac) to $f$ on $\overline B(1,R_1+1)$ with inner radius $R_1$. This gives the finite set $Z_b$ of zeros of $f$ in $\overline B(1,R_1)$, exponents $m$, and a cofactor $h$ nonzero on $\overline B(1,R_1)$ with $f=\prod_{Z_b}(w-\rho)^{m_\rho}h$. Then $Z\subseteq Z_b$. Since $h(\rho)\ne0$, $m_\rho$ is the analytic order of $f$ at $\rho$ (`exr_ord`). Multiple zeros therefore carry their exact weights.

*An open set without the other poles.* Let $U=B(1,R_1)\setminus\big((Z_b\setminus Z)\cup\{0\}\big)$, which is open because only finitely many points are removed. The closed rectangle lies in $U$. It misses $0$ because $x_0>0$. A point of $Z_b\setminus Z$ in the closed rectangle would be a zero of $f$ there, hence, by hypothesis, a zero in the open rectangle, that is, a point of $Z$. This is the only use of the boundary hypothesis. Also $1\in U$, $Z\subset U$ and $1\notin Z$.

*The regular part of the logarithmic derivative.* On $U\setminus Z$,
$$
\frac{f'}{f}(w)=\sum_{\rho\in Z}\frac{m_\rho}{w-\rho}+\Lambda(w),\qquad
\Lambda=\frac{h'}{h}+\sum_{\rho\in Z_b\setminus Z}\frac{m_\rho}{w-\rho},
$$
and $\Lambda$ is holomorphic on $U$ (`exr_logDeriv`).

*Principal parts.* Put $\varphi(w)=y^w/w$. It is holomorphic on $U$ because $0\notin U$, and $k_y=\varphi/(w-1)$. Set
$$
b_1=-\frac{f'(1)}{f(1)}\,y,\qquad b_\rho=-m_\rho\,k_y(\rho)\quad(\rho\in Z).
$$
For $\psi$ holomorphic on $U$ and $a\in U$, the difference quotient $\delta_a\psi$ is defined by $\delta_a\psi(w)=(\psi(w)-\psi(a))/(w-a)$ for $w\ne a$ and $\delta_a\psi(a)=\psi'(a)$. It is again holomorphic on $U$, so
$$
G_0=-\delta_1(\Lambda\varphi)-\sum_{\rho\in Z}\frac{m_\rho}{\rho-1}\big(\delta_\rho\varphi-\delta_1\varphi\big)
$$
is holomorphic on $U$. We claim that for $w\in U$ outside $\{1\}\cup Z$,
$$
-\frac{f'}{f}(w)\,k_y(w)-\frac{b_1}{w-1}-\sum_{\rho\in Z}\frac{b_\rho}{w-\rho}=G_0(w).
$$
Insert the decomposition of $f'/f$ at $w$ and at $1$, using $f'(1)/f(1)=\sum_\rho m_\rho/(1-\rho)+\Lambda(1)$ and $\varphi(1)=y$. The terms in $\Lambda$ give $(-\Lambda(w)\varphi(w)+\Lambda(1)\varphi(1))/(w-1)=-\delta_1(\Lambda\varphi)(w)$. For each $\rho$, with $m=m_\rho$, it remains to check
$$
-\frac{m}{w-\rho}\,\frac{\varphi(w)}{w-1}+\frac{m}{1-\rho}\,\frac{y}{w-1}+\frac{m\,k_y(\rho)}{w-\rho}+\frac{m}{\rho-1}\Big(\frac{\varphi(w)-\varphi(\rho)}{w-\rho}-\frac{\varphi(w)-y}{w-1}\Big)=0
$$
(`exr_term`). By $1/(w-\rho)-1/(w-1)=(\rho-1)/((w-\rho)(w-1))$, the bracket contributes three terms: $m\varphi(w)/((w-\rho)(w-1))$, which cancels the first term; $-m\varphi(\rho)/((\rho-1)(w-\rho))=-m\,k_y(\rho)/(w-\rho)$, which cancels the third; and $my/((\rho-1)(w-1))$, which cancels the second.

*Residue theorem.* Put $G=G_0$ on $\{1\}\cup Z$ and $G=-(f'/f)k_y-\sum_pb_p/(w-p)$ elsewhere on $U$. By the claim $G=G_0$ on $U$, so $G$ is holomorphic there. Away from $\{1\}\cup Z$ the integrand is $G+\sum_pb_p/(w-p)$, and every $p$ lies strictly inside the rectangle. Then (Res) gives $I=2\pi i(b_1+\sum_{\rho\in Z}b_\rho)$, which is the stated formula. $\square$

**Proof of Theorem 4.10.13.** *The zero list.* By (N) every zero of $f_\chi$ has real part less than $1<\sigma_0$. Hence $Z$ is the set of zeros in the open rectangle $(\sigma_1,\sigma_0)\times(-T',T')$, and the hypothesis says that every zero in the closed rectangle lies in the open one. Theorem 4.10.12 applies to the entire function $f_\chi$, which satisfies $f_\chi(1)\ne0$, and gives
$$
I\Big(-\frac{f_\chi'}{f_\chi}\,k_y\Big)=2\pi i\Big(K_\chi y-\sum_{\rho\in Z}m_\chi(\rho)\,k_y(\rho)\Big).
$$
*Non-principal $\chi$.* Here $f_\chi=L(\cdot,\chi)$, so $F_y=-(f_\chi'/f_\chi)k_y$ identically.

*Principal $\chi$.* Let $w\in\partial R$. Then $w\ne0$, because $\operatorname{Re}w\ge\sigma_1>0$. Also $w\ne1$, because $1$ lies strictly inside, and $f_\chi(w)\ne0$, because boundary zeros are excluded. Since $f_\chi=(s-1)L(s,\chi)$ near $w$, we get $L(w,\chi)\ne0$ and $f_\chi'(w)=L(w,\chi)+(w-1)L'(w,\chi)$. Hence
$$
F_y(w)=-\frac{f_\chi'(w)}{f_\chi(w)}\,k_y(w)+\frac{k_y(w)}{w-1}\qquad(w\in\partial R).
$$
Both summands are continuous on $\partial R$. Since $I$ uses only boundary values, it is the sum of the two rectangle integrals (`ex_rectInt_congr`, `ex_rectInt_add`). Lemma 4.10.11 evaluates the second one as $2\pi i(y\log y-y)$. $\square$

The value of Mathlib's principal $L$-function at its pole $s=1$ is a convention and never enters. The point $1$ is not on the boundary, and the residue at $1$ is computed from $f_\chi$ and from $k_y/(w-1)$.

**Proof of Corollary 4.10.14.** The parameters satisfy $\sigma_1\ge1-\kappa\ge19/20>0$, $\sigma_1\le1-3\kappa/4<1$, $\sigma_0>1$ and $T'\ge T\ge2>0$. Let $w$ be a zero of $f_\chi$ with $\sigma_1\le\operatorname{Re}w\le\sigma_0$ and $|\operatorname{Im}w|\le T'$. Then $\operatorname{Re}w\ge19/20\ge9/10$ and $|\operatorname{Im}w|\le T+1\le T+3$. The real-part gap gives $|\operatorname{Re}w-\sigma_1|\ge d>0$, hence $\operatorname{Re}w>\sigma_1$. The height gap gives $\big||\operatorname{Im}w|-T'\big|\ge d>0$, hence $|\operatorname{Im}w|<T'$. The right side needs no gap, since $\operatorname{Re}w<1<\sigma_0$. This is the boundary hypothesis that the archive derives at `PNTExplMainB.lean:138–148` before it calls `ex_rect_Fchi` at `:149`.

Unfolding $I$ gives $B-P+iR-iL=2\pi iQ$. Division by $y$ uses $(y\log y-y)/y=\log y-1$ and $k_y(\rho)/y=y^{\rho-1}/(\rho(\rho-1))$ (`:153–164`), and the archive combines the result with Perron (`:150`) and the algebra `exm_alg` (`:152`). Multiplying the identity by $-i$ gives $R=2\pi Q+L+i(B-P)$, hence $I_\infty-2\pi Q=(I_\infty-R)+L+i(B-P)$. $\square$

#### 4.10.8.6 Failure examples and remarks

**Without $\sigma_1>0$ [Expository].** For $\chi_8$ at $y=16$ take the rectangle $[-1/2,2]\times[-3,3]$, which reaches $\operatorname{Re}s<0$. It contains $s=0$, which is both the pole of $k_y$ and the trivial zero of $L(s,\chi_8)$. There $D(s)=-1/s+c_0+O(s)$ with $c_0=-L''(0,\chi_8)/(2L'(0,\chi_8))\approx0.296464$, and $k_y(s)=-1/s-(\log y+1)+O(s)$. So $F_y$ has a double pole at $0$, with residue $\log y+1-c_0\approx3.476125$, and the integral is $2\pi i(16K+3.476125)\approx2\pi i\,(-6.637715)$. With the hypothesis $\sigma_1>0$ deleted, the right side of Theorem 4.10.13 gives $2\pi i\cdot16K$ instead. The point $0$ belongs to $Z$ with order $1$, but $k_y(0)$ has no value; the Lean convention $x/0=0$ assigns it $0$, so the formula silently drops the double-pole residue $3.476125$. A 20-digit contour computation confirms the value $2\pi i\,(-6.637715)$ (numerical supplement). The next trivial zero, $-2$, is still outside. For $\chi_0$ modulo $8$ the obstruction is worse: $f$ vanishes at every point $2\pi ik/\log2$ of the line $\operatorname{Re}s=0$. A left edge on that line meets zeros. A left edge beyond it encloses $s=0$, where $k_y$ has a pole and $f$ a simple zero.

**A zero on the boundary.** Take $f(s)=s-1/2$, $y=4$ and the rectangle $[1/2,2]\times[-1,1]$. On the left edge $s=1/2+it$, the integrand $-k_4(s)/(s-1/2)$ behaves like $-k_4(1/2)/(it)$, where $|k_4(1/2)|=8$. It is therefore not integrable near $t=0$, and the boundary integral is undefined. The symmetric principal value exists and picks up half the residue at $1/2$, so neither counting this zero nor omitting it reproduces it. This is why Theorem 4.10.13 assumes a zero-free boundary, and why §4.10.7 derives that assumption from gaps of size $d$. The failure example in §4.10.7.6 shows that a zero merely close to the left edge already destroys the pointwise edge bounds.

**Weights.** Take $f(s)=(s-1/2)^2$ and $y=9$ on any rectangle as in Theorem 4.10.12 that contains $1/2$. Here $-f'(1)/f(1)=-4$ and $k_9(1/2)=3/(-1/4)=-12$, so the theorem gives $I=2\pi i(-36+24)=2\pi i\,(-12)$. With weight $1$ instead of the order $2$, the formula would predict $2\pi i\,(-24)$. The discrepancy $24\pi i$ is one unit of multiplicity times $2\pi i\,|k_9(1/2)|$. The archive's interface `LandauLocal` alone cannot exclude this, since its weights only satisfy $m_\rho\ge1$, while the residue theorem needs the analytic order. Lemma 4.10.9 and `exr_ord` supply it.

**The principal correction.** For $\chi_0$ the theorem is not Theorem 4.10.12 applied to $L$: $L$ has a pole at $1$, so the hypothesis "entire with $f(1)\ne0$" fails. Applying Theorem 4.10.12 to $f_\chi$ integrates $-(f_\chi'/f_\chi)k_y$ instead of $F_y$ and misses $2\pi i(y\log y-y)$. At $y=10$ this missing term is $2\pi i\cdot13.025851$, about forty times the full residue $0.322222$. After division by $y$ it is the term $p_\chi(\log y-1)$ of §4.10.7.

**The pole at $1$ must be inside.** If $\sigma_0<1$ the point $1$ lies outside and the terms $K_\chi y$ and $p_\chi(y\log y-y)$ are absent; if $\sigma_0=1$ the pole lies on the right edge and that edge integral diverges. In the archive $\sigma_0=1+1/\log y$, and $\sigma_1<1$ follows from $\sigma_1\le1-3\kappa/4$.

**Classical comparison [Paper].** Tao's 254A Notes 2 take the same two steps for $\zeta$ [[Tao2014, Proposition 19, Remark 17 and Theorem 21](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/)]. Proposition 19 replaces $\zeta$ by $(s-1)\zeta(s)$ and applies a local disc theorem on a disc centred at $2+it$. It then removes the zeros farther than $\varepsilon/2$ from $s$ with the crude count of Proposition 16. Remark 17 fixes the convention that sums over zeros count multiplicity. The proof of Theorem 21 applies the residue theorem to the rectangle $\varepsilon'\le\operatorname{Re}s\le1+1/\log x$, $|\operatorname{Im}s|\le T'$. The residues there are $x$ at $1$ and, at each zero, $-x^\rho/\rho$ times the multiplicity. The archive differs in three ways. Its discs are centred at $101/100+it$, just to the right of $\operatorname{Re}s=1$, and normalized by the inverse bound. Its kernel $y^s/(s(s-1))$ is Riesz-smoothed, which creates the double pole at $1$ for the principal character. It also keeps the exact identity of Theorem 4.10.13 separate from the edge estimates, which §4.10.7 carries out with coordinate gaps. Lemma 4.10.9 is the local Landau lemma of §4.8.8 with the exact orders made explicit.

**What the constant means for §4.10.7.** The numerator constant of §4.10.7 is $C_2=2C_{\mathrm{loc}}+100/7+C_3$ (`ex_negLD_bound`, `PNTExplNeg.lean:33`). Section 4.10.9 reads the archive's actual witness $C_G=\max(9,6)=9$, which fixes $C_{\mathrm{loc}}=180(\log90900+3)\approx2595.15$. Meanwhile `LogDerivRight.lean:14` defines $C_3=\max(\max(B,0),-\zeta'(1+\varepsilon/2)/\zeta(1+\varepsilon/2))$ from the Laurent remainder proof read in [§4.10.10](#41010-the-pole-subtracted-zeta-logarithmic-derivative), and since $-\zeta'(\sigma)/\zeta(\sigma)=\sum_{n\ge1}\Lambda(n)n^{-\sigma}>0$ for $\sigma>1$, one has $C_3>0$ strictly. Consequently
$$
C_2>C_2^{\mathrm{lb}}:=360(\log90900+3)+\frac{100}{7}\approx5204.59 ,
$$
and the baseline $(C_2^{\mathrm{lb}},0)$ used in §4.10.7.2 gives explicit budget lower bounds rather than an admissible witness pair.

#### 4.10.8.7 Source map and reading boundary

Archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Short `PNTExpl*` paths are relative to `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/` and the other paths to `src/Formalism/`. All cited members were extracted from the tarball and compared byte for byte with the read-only copy.

| Step | Location | Reading |
|---|---|---|
| `ex_local` | `PNTExplLocL.lean:86–146`; helpers `ex_centre_re`, `ex_centre_norm`, `ex_centre_lower`, `ex_log_bound` at `:12–84` | Local R3 [Lean, read] |
| Disc lemma with exact orders | `ex_landau_ord_core`, `ex_landau_ord` at `PNTExplLoc.lean:115–319`; the private factorization and finiteness lemmas at `:12–111` | Local R3 |
| Zero-free disc estimate | `landauLocal` at `ZeroFreeRegion/FinalZFR.lean:15`; `localZeroExpansionOfFactorization` at `ZeroFreeRegion/ZetaLogDerivativeBounds/LandauLocalOf.lean:69–180` | Local R3; its suppliers `zeroFactorization` (`ZeroFactor.lean:120–168`), `logDerivBoundOnBall` (`LogDerivBound.lean:42–120`) and `landauLocal_logDeriv_prod` (`LandauLocalOf.lean:44–50`) are inherited from §4.8.8 |
| `ex_rect_Fchi` | `PNTExplRectF.lean:154–240`; boundary set, congruence, additivity and continuity at `:62–151` | Local R3 |
| Double pole | `ex_phi_hasDerivAt`, `ex_phi_differentiableOn`, `ex_rect_double` at `PNTExplRectF.lean:12–60`; `rectangle_double_pole` and its edge primitives at `ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean:10–149`, statement at `ZeroFreeRegion/SmallHeightLogDeriv.lean:71–76` | Local R3 |
| Rectangle identity for entire $f$ | `ex_rect_logDeriv` at `PNTExplRect.lean:15–189`; `exr_ord`, `exr_logDeriv`, `exr_term` at `PNTExplRectA.lean:9–72` | Local R3 |
| Residue theorem | `rectangle_residue` at `LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean:123`, statement at `LFunctionBounds/ExpSumLowerBound.lean:34–43` | Inherited from §4.8.7 |
| Facts about $f_\chi$ | `exLF_of_ne` through `exOrd_eq_one`, `exLF_prod_le` and `exLF_lower` at `PNTExplLF.lean:13–127,186–205` | Local R3 for the A2 bodies |
| Growth | `exLF_growth` at `PNTExplLF.lean:129–184` | Named input (G) here; read at local R3 [Lean, read] in §4.10.9 |
| Inverse and right-half-plane bounds | `inverseBound`, `l_log_deriv_right` at `LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean:23–86,116–126` | Inherited from §4.8.8 |
| Definitions | `exLF`, `exOrd`, `exKer`, `explicitFormulaConstant` at `PNTExplDefs.lean:12–20`; `Fchi` at `LandauZeroFreeBounds/LogDerivRegionChiOf.lean:14–15`; `negLD` at `LandauZeroFreeBounds/NoZeroComplexOf.lean:10–11`; `rectInt` at `ZeroFreeRegion/SmallHeightLogDeriv.lean:9–11` | Read |
| Consumers | `ex_negLD_bound` at `PNTExplNeg.lean:27–102`; the box count at `PNTExplBox.lean:121`; the call in `exm_core` at `PNTExplMainB.lean:138–168` | Read in §4.10.7; call sites re-read |

Section 4.10.9 reads `exLF_growth` together with its suppliers `lfunction_polynomial_growth` (`LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:53–71`) and `growthBound` (`ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaGrowth.lean:78`). The Mathlib facts are used at statement level at the A2 pin: `LFunctionTrivChar₁` with its value at $1$, `LFunction_ne_zero_of_one_le_re`, the maximum modulus theorem `Complex.norm_le_of_forall_mem_frontier_norm_le`, `differentiableOn_dslope` and the analytic-order API. The examples and the numerical supplement are [Expository]. Local R3 records source reading, not a Lean kernel check. See the [source ledger](../sources/SOURCES.md#chapter-4-4108-local-expansion-and-rectangle-identity).

### 4.10.9 Uniform polynomial growth in the half-plane: `lfunction_polynomial_growth` and `exLF_growth`

Section 4.10.8 retained one archive proof as a named `R2` input: the uniform polynomial-growth bound `exLF_growth`, which controls the pole-removed function $f_\chi$ across all moduli $M\ge1$, all characters $\chi$ modulo $M$ and the entire closed half-plane $\operatorname{Re}s\ge1/2$. Earlier, §4.8.8 retained its non-principal counterpart `lfunction_polynomial_growth` beneath the `TailBox` edge bound. This subsection reads both production proofs in full, together with the bad-prime Euler-product bound `exLF_prod_le` and the power-difference continuation `growthBound` of $\zeta(s)$ on $\operatorname{Re}s>0$, tracks the exact origin of the constants $C_P=9$, $6$ and $C_G=\max(C_P,6)=9\ge1$, and connects them to their Perron, rectangle, `TailBox` and explicit-formula consumers.

#### 4.10.9.1 Motivation

Every local logarithmic-derivative estimate in Chapter 4 — `landau_lemma_lfunction_zeros` inside `TailBox` (§4.8.8), `ex_local` inside the smoothed explicit formula (§4.10.8), and `deuring_heilbronn_local` inside the relative PNT package — applies the Borel–Carathéodory / maximum-modulus disc lemma on a disc centred just to the right of $\operatorname{Re}s=1$ whose outer circle reaches left to $\operatorname{Re}s\ge1/2$ ($21/20-11/20=1/2$, $101/100-2/5=61/100$, and $26/25-12/25=14/25$). None of those consumers needs subconvexity or the functional equation: because the disc lemma takes $\log B$ of the boundary-to-centre ratio $B$, any bound polynomial in $M$ and $1+|s|$ on $\operatorname{Re}s\ge1/2$ becomes an $O(\log(M(|t|+2)))$ budget for both the local zero count and the regular remainder. What is indispensable is that a single absolute constant work uniformly across every modulus $M\ge1$, every character $\chi$ modulo $M$, and every vertical height $t=\operatorname{Im}s$, right through the critical strip down to $\operatorname{Re}s=1/2$.

Why must the archive split this uniform bound into two separate analytic routes?

1. **Non-principal characters ($\chi\ne1$): periodic cancellation and Abel summation.** When $\chi$ is non-principal, its values sum to $0$ over every complete period of length $M$. Partial character sums $\sum_{n=1}^K\chi(n)$ therefore never grow with $K$: in §4.7 the archive bounds them universally by $M+1$. Applying Abel partial summation to the tail after the $N=1$ term $1^{-s}\chi(1)$ continues $L(s,\chi)$ to $\operatorname{Re}s>0$ and bounds $|L(s,\chi)|$ by $1+2(M+1)(1+|s|/\operatorname{Re}s)$. Restricting to $\operatorname{Re}s\ge1/2$ turns $1/\operatorname{Re}s$ into $2$ and collapses the linear combination into $9M(1+|s|)$, giving `lfunction_polynomial_growth` with witness $C_P=9$.
2. **Principal character ($\chi=1$): `exLF` pole removal, Euler–Maclaurin differences and bad-prime factors.** For the principal character $\chi_0$ modulo $M$, partial sums of $\chi_0(n)$ grow like $(\varphi(M)/M)K$ rather than cancelling, and $L(s,\chi_0)=\zeta(s)\prod_{p\mid M}(1-p^{-s})$ has a simple pole at $s=1$ of residue $\prod_{p\mid M}(1-p^{-1})$. No finite partial-sum bound exists near $s=1$. Instead, the archive's `exLF` multiplies $L(s,\chi_0)$ by $(s-1)$ (updating the removable value at $s=1$ to $\prod_{p\mid M}(1-p^{-1})$). To bound $(s-1)\zeta(s)$ on $\operatorname{Re}s>0$ without importing the functional equation, `ZetaGrowth.lean` telescopes $(n+1)^{1-s}-(n+2)^{1-s}-(s-1)(n+2)^{-s}$ into an absolutely convergent series $D_z(s)$ with $(s-1)\zeta(s)=s-D_z(s)$ and $|D_z(s)|\le|s-1|\,|s|(1+1/\operatorname{Re}s)$. Removing the pole via multiplication by $(s-1)$ raises the archimedean degree from $(1+|s|)$ to $6(1+|s|)^2$, while each bad-prime factor on $\operatorname{Re}s\ge0$ satisfies $|1-p^{-s}|\le2\le p$, so their product is bounded by $\prod_{p\mid M}p\le M$ (`exLF_prod_le`).

Finally, why does `exLF_growth` produce $C_G=\max(C_P,6)=9\ge1$? The interface `PolynomialGrowth` (`PositivityBound.lean:25–28`) asserts only $\exists C,\ \forall M,\chi\ne1,s,\ |L(s,\chi)|\le CM(1+|s|)$, without packaging $C\ge1$ in its statement (at $s=1$, $|L(1,\chi)|>0$ already forces $C>0$, though not $C\ge1$). When `exLF_growth` unpacks `lfunction_polynomial_growth` as $\langle C_0,hC_0\rangle$, taking $\max(C_0,6)$ simultaneously dominates the non-principal linear constant $C_0$ (upgraded to quadratic via $1+|s|\le(1+|s|)^2$), dominates the principal quadratic constant $6$, and proves $1\le\max(C_0,6)$ in one line from $1\le6$. Because the proof of `lfunction_polynomial_growth` supplies $C_0=9$, the non-principal branch determines the maximum: $C_G=\max(9,6)=9$.

#### 4.10.9.2 Two worked calculations: modulus $4$ and modulus $5$ [Expository]

**Non-principal character $\chi_{-4}$ modulo $4$.** Take $M=4$, so `[NeZero 4]` holds ($4\ge1$), and let $\chi_{-4}$ be the unique non-principal character modulo $4$: $\chi_{-4}(1)=1$, $\chi_{-4}(3)=-1$ and $\chi_{-4}(2k)=0$. Since $\chi_{-4}(3)=-1\ne1=\chi_0(3)$, the premise $\chi_{-4}\ne1$ holds, and $f_{\chi_{-4}}(s)=L(s,\chi_{-4})$ for all $s\in\mathbb C$. Over one period $\sum_{a=0}^3\chi_{-4}(a)=0+1+0-1=0$, and the partial sums $A(K)=\sum_{n=1}^K\chi_{-4}(n)$ cycle with period $4$ through $1,1,0,0$. Thus $\max_{K\ge0}|A(K)|=1$, well inside the archive's universal modulus bound $B=M+1=5$ (`norm_character_sum_Icc_le`). Applying `l_function_partial_sum` at truncation $N=1$ splits off $\chi_{-4}(1)\cdot1^{-s}=1$ of modulus $1$ and bounds the remainder on $\operatorname{Re}s>0$ by $2B\cdot1^{-\operatorname{Re}s}(1+|s|/\operatorname{Re}s)=10(1+|s|/\operatorname{Re}s)$, giving $|L(s,\chi_{-4})|\le1+10(1+|s|/\operatorname{Re}s)$.

- *Interior point $s=1$ ($\operatorname{Re}s=1\ge1/2$, $|s|=1$).* Alternating grouping gives Leibniz's series $L(1,\chi_{-4})=1-1/3+1/5-\dots=\pi/4\approx0.785398$. Every step of Theorem 4.10.16 and Theorem 4.10.18 can be checked in rational arithmetic: the tail after $N=1$ has $|L(1,\chi_{-4})-1|=1-\pi/4\approx0.214602\le10(1+1/1)=20$; adding $|\chi_{-4}(1)|=1$ gives $21$; replacing $1/\operatorname{Re}s=1$ by the half-plane worst case $2$ gives $1+10(1+2)=31$; using $1\le4(1+1)=8$ and $2(4+1)(1+2)=30\le8\cdot4(1+1)=64$ gives $31\le8+64=9\cdot4\cdot(1+1)=72$ (`lfunction_polynomial_growth`); and multiplying by $1+|1|=2\ge1$ gives $72\le9\cdot4\cdot(1+1)^2=144$ (`exLF_growth`).
- *Boundary point $s=1/2+2i$ ($\operatorname{Re}s=1/2$, $|s|=\sqrt{17}/2\approx2.061553$).* On the boundary line $\operatorname{Re}s=1/2$, the step $|s|/\operatorname{Re}s\le2|s|$ is an **equality**: $|s|/\operatorname{Re}s=\sqrt{17}$. From the Hurwitz decomposition $L(s,\chi_{-4})=4^{-s}(\zeta(s,1/4)-\zeta(s,3/4))$ one finds $|L(1/2+2i,\chi_{-4})|\approx1.151078$ and $|L(1/2+2i,\chi_{-4})-1|\approx0.408952\le10(1+\sqrt{17})\approx51.231056$. Both intermediate bounds coincide at $1+10(1+\sqrt{17})=11+10\sqrt{17}\approx52.231056$, followed by
$$
11+10\sqrt{17}\le9\cdot4\Big(1+\frac{\sqrt{17}}{2}\Big)=36+18\sqrt{17}\approx110.215901\le9\cdot4\Big(1+\frac{\sqrt{17}}{2}\Big)^2=189+36\sqrt{17}\approx337.431803 .
$$

**Principal character $\chi_0$ modulo $5$ and `exLF` near $s=1$.** Take $M=5$, so `[NeZero 5]` holds ($5\ge1$) and $M.\mathrm{primeFactors}=\{5\}$. Here $\chi=\chi_0=1$ violates $\chi\ne1$; indeed partial sums $A(K)=K-\lfloor K/5\rfloor$ grow as $\frac45K$, and $L(s,\chi_0)=(1-5^{-s})\zeta(s)$ has residue $4/5$ at $s=1$. The modified function $f_{\chi_0}=\operatorname{exLF}(\chi_0,\cdot)$ is defined by
$$
f_{\chi_0}(s)=(s-1)(1-5^{-s})\zeta(s)\quad(s\ne1),\qquad f_{\chi_0}(1)=1-5^{-1}=\frac{4}{5}=0.8 .
$$
On $\operatorname{Re}s\ge1/2$, the single prime $p=5\ge2$ satisfies $|5^{-s}|=5^{-\operatorname{Re}s}\le5^{-1/2}=1/\sqrt5<1$, so $|1-5^{-s}|\le1+5^{-\operatorname{Re}s}\le2\le5=\prod_{p\in\{5\}}p\le M$, confirming every inequality in Lemma 4.10.17 (`exLF_prod_le`).

- *At the pole $s=1$ (`s = 1` branch).* Raw $\zeta(1)$ is Mathlib's junk value rather than a limit, and $\lim_{s\to1}|L(s,\chi_0)|=+\infty$, so `exLF_growth` branches on $s=1$ before touching $\zeta$. By `Function.update_self`, $f_{\chi_0}(1)=1-5^{-1}=4/5$, and `exLF_prod_le` at $s=1$ bounds $|f_{\chi_0}(1)|=0.8\le5=M\le6\cdot5\cdot(1+1)^2=120\le9\cdot5\cdot(1+1)^2=180$.
- *Near the pole, at the §4.10.8 disc centre $s=101/100$ ($s\ne1$, $|s-1|=1/100$, $\operatorname{Re}s=101/100\ge1/2$).* Here $\zeta(101/100)\approx100.577943$ and the unmodified $L$-value is already large: $L(101/100,\chi_0)=(1-5^{-101/100})\zeta(101/100)\approx0.803193\times100.577943\approx80.783511$. Watch how Lemma 4.10.15 and Theorem 4.10.18 cancel the $1/(s-1)=100$ spike:
  1. The power-difference series has $|D_z(101/100)|=|101/100-(1/100)\zeta(101/100)|\approx0.004221$, bounded by $|s-1|\,|s|(1+1/\operatorname{Re}s)=\frac1{100}\cdot\frac{101}{100}\big(1+\frac{100}{101}\big)=\frac{201}{10000}=0.0201$.
  2. Dividing $|s-D_z(s)|$ by $|s-1|=1/100$ gives `growthBound`: $|\zeta(101/100)|\approx100.577943\le1+100+\frac{201}{100}=103.01$.
  3. Multiplying back by $|s-1|=1/100$ inside `exLF_growth` cancels $100\cdot(1/100)=1$:
     $$
     |(s-1)\zeta(s)|\approx1.005779\le\frac{1}{100}+1+\frac{201}{10000}=1.0301\le2.01+1+2.01\cdot3.03=9.1003\le6(2.01)^2=24.2406 .
     $$
  4. Multiplying by $|1-5^{-101/100}|\approx0.803193\le5$ yields $|f_{\chi_0}(101/100)|\approx0.807835\le6\cdot5\cdot(2.01)^2=121.203\le9\cdot5\cdot(2.01)^2=181.8045$, smoothly matching $f_{\chi_0}(1)=0.8$ as $s\to1$.
- *Boundary point $s=1/2+i$ ($\operatorname{Re}s=1/2$, $|s|=|s-1|=\sqrt5/2\approx1.118034$).* Here $1/\operatorname{Re}s=2$ is again sharp, so $|s-1|\,|s|(1+1/\operatorname{Re}s)=(\sqrt5/2)^2\cdot3=15/4=3.75$, which bounds $|D_z(1/2+i)|\approx0.517279$. Next $|\zeta(1/2+i)|\approx0.736305\le1+2/\sqrt5+3\sqrt5/2\approx5.248529$, hence $|(s-1)\zeta(s)|\approx0.823215\le19/4+\sqrt5/2\approx5.868034\le6(1+\sqrt5/2)^2=27/2+6\sqrt5\approx26.916408$. With $|1-5^{-1/2-i}|\approx1.111105\le1+1/\sqrt5\approx1.447214\le5$, we obtain $|f_{\chi_0}(1/2+i)|\approx0.914677\le30(1+\sqrt5/2)^2\approx134.582039\le45(1+\sqrt5/2)^2\approx201.873059$.

#### 4.10.9.3 Definitions and inherited inputs

For $s\in\mathbb C$ and $n\in\mathbb N$, using Mathlib's principal-branch complex power $(m:\mathbb C)^w$, define (`DzDifferentiableOn.lean:11–15`)
$$
d_z(s,n)=(n+1)^{1-s}-(n+2)^{1-s}-(s-1)(n+2)^{-s},\qquad D_z(s)=\sum_{n=0}^{\infty}d_z(s,n).
$$
Recall three archive interfaces and definitions:

- `ZetaGrowth` (`SmallHeightLogDeriv.lean:66–69`): for all $s\in\mathbb C$ with $\operatorname{Re}s>0$ and $s\ne1$, $|\zeta(s)|\le1+1/|s-1|+|s|(1+1/\operatorname{Re}s)$.
- `PolynomialGrowth` (`PositivityBound.lean:25–28`): $\exists C\in\mathbb R$ such that for every $M\in\mathbb N$ with `[NeZero M]`, every $\chi\bmod M$ with $\chi\ne1$, and every $s\in\mathbb C$ with $\operatorname{Re}s\ge1/2$, $|L(s,\chi)|\le CM(1+|s|)$.
- $f_\chi=\operatorname{exLF}(\chi,\cdot)$ (`PNTExplDefs.lean:12–13`, §4.10.8.3): equal to Mathlib's `DirichletCharacter.LFunctionTrivChar₁ M` when $\chi=1$ — namely `Function.update` of $s\mapsto(s-1)L(s,\chi_0)$ at $s=1$ by $\prod_{p\in M.\mathrm{primeFactors}}(1-p^{-1})$ — and equal to $L(\cdot,\chi)$ when $\chi\ne1$. Similarly, Mathlib's `riemannZeta₁` (`ZetaAsymp.lean:536`) is `Function.update` of $s\mapsto(s-1)\zeta(s)$ at $s=1$ by $1$.

Two ingredients from §4.7 have already been read at `R3` and are used here without repeating their proofs:

- (C1) **Character-sum bound (`norm_character_sum_Icc_le`, `LGrowth.lean:39–51`, read in §4.7).** For every $M\ge1$, every non-principal character $\chi$ modulo $M$, and every $a,b\in\mathbb N$, $\big|\sum_{n=a}^b\chi(n)\big|\le M+1$.
- (C2) **Abel partial-sum approximation (`l_function_partial_sum`, `LPartialSum.lean:136–169`, via `LFunction_eq_G`, `LFunctionEqGOfOneLt.lean:228`, read in §4.7).** Let $\chi\ne1$ be a character modulo $M\ge1$, and let $B\ge0$ satisfy $\big|\sum_{n=1}^K\chi(n)\big|\le B$ for all $K\in\mathbb N$. Then for every $s\in\mathbb C$ with $\operatorname{Re}s>0$ and every $N\ge1$,
$$
\Big|L(s,\chi)-\sum_{n=1}^{N}\chi(n)n^{-s}\Big|\le2B\,N^{-\operatorname{Re}s}\Big(1+\frac{|s|}{\operatorname{Re}s}\Big).
$$

From Mathlib at the pinned commit `0df444a` we use at statement level `[Lean]`: the Dirichlet-series identity $\zeta(s)=\sum_{n=0}^\infty(n+1)^{-s}$ on $\operatorname{Re}s>1$ (`riemannZeta_eq_tsum_one_div_nat_add_one_cpow`), the entireness of `riemannZeta₁` (`differentiable_riemannZeta₁`), the identity theorem for analytic functions on preconnected open sets (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) together with convexity-implies-preconnectedness and open-set analyticity of complex-differentiable functions, locally uniform series differentiation (`differentiableOn_tsum_of_summable_norm`), the principal-character factorization $L(s,\chi_0)=\big(\prod_{p\in M.\mathrm{primeFactors}}(1-p^{-s})\big)\zeta(s)$ for $s\ne1$ (`LFunctionTrivChar_eq_mul_riemannZeta`), and the divisibility $\prod_{p\in M.\mathrm{primeFactors}}p\mid M$ (`Nat.prod_primeFactors_dvd`).

#### 4.10.9.4 Lemmas, theorems, and downstream consumers

**Lemma 4.10.15 (zeta power-difference continuation and `growthBound`) [Lean, read].** For every $s\in\mathbb C$ with $\operatorname{Re}s>0$ and every $n\in\mathbb N$,
$$
|d_z(s,n)|\le|s-1|\,|s|\,(n+1)^{-\operatorname{Re}s-1}.
$$
The series $D_z(s)=\sum_{n=0}^\infty d_z(s,n)$ converges absolutely and defines a complex-differentiable function on $\{\operatorname{Re}s>0\}$ satisfying $\operatorname{riemannZeta}_1(s)=s-D_z(s)$ throughout $\{\operatorname{Re}s>0\}$ — in particular $(s-1)\zeta(s)=s-D_z(s)$ for $s\ne1$ — together with
$$
|D_z(s)|\le|s-1|\,|s|\Big(1+\frac{1}{\operatorname{Re}s}\Big)\qquad(\operatorname{Re}s>0),
$$
and therefore `ZetaGrowth` holds:
$$
|\zeta(s)|\le1+\frac{1}{|s-1|}+|s|\Big(1+\frac{1}{\operatorname{Re}s}\Big)\qquad(\operatorname{Re}s>0,\ s\ne1).
$$

**Theorem 4.10.16 (non-principal polynomial growth, `lfunction_polynomial_growth`) [Lean, read], given (C1) and (C2).** Let $M\in\mathbb N$ satisfy `[NeZero M]` ($M\ge1$), let $\chi$ be a non-principal Dirichlet character modulo $M$ ($\chi\ne1$), and let $s\in\mathbb C$ satisfy $\operatorname{Re}s\ge1/2$. Then
$$
|L(s,\chi)|\le1+2(M+1)\Big(1+\frac{|s|}{\operatorname{Re}s}\Big)\le9\,M\,(1+|s|).
$$
Consequently `PolynomialGrowth` holds with explicit witness $C_P=9$.

**Lemma 4.10.17 (bad-prime Euler product bound, `exLF_prod_le` and `dhl_prod_le`) [Lean, read].** Let $M\in\mathbb N$ satisfy `[NeZero M]` ($M\ge1$), and let $s\in\mathbb C$ satisfy $\operatorname{Re}s\ge0$ (`exLF_prod_le` assumes $\operatorname{Re}s\ge1/2$). Then
$$
\Big|\prod_{p\in M.\mathrm{primeFactors}}(1-p^{-s})\Big|\le\prod_{p\in M.\mathrm{primeFactors}}p\le M .
$$

**Theorem 4.10.18 (uniform polynomial growth of `exLF`, `exLF_growth`) [Lean, read], given Lemma 4.10.15, Theorem 4.10.16, and Lemma 4.10.17.** Let $C_0$ be any witness for `PolynomialGrowth` and set $C_G=\max(C_0,6)\ge1$ (for the archive's witness $C_0=C_P=9$, $C_G=9$). For every $M\in\mathbb N$ with `[NeZero M]`, every Dirichlet character $\chi$ modulo $M$, and every $s\in\mathbb C$ with $\operatorname{Re}s\ge1/2$,
$$
|f_\chi(s)|\le C_G\,M\,(1+|s|)^2 .
$$
Specifically, the archive's proof establishes $|f_\chi(s)|\le9M(1+|s|)\le9M(1+|s|)^2$ when $\chi\ne1$ and $|f_{\chi_0}(s)|\le6M(1+|s|)^2$ (sharpened to $4M(1+|s|)^2$ in `dhl_triv_growth`) when $\chi=1$.

**Corollary 4.10.19 (supply to the Perron, rectangle, `TailBox`, and explicit-formula consumers) [Lean, read].** Substituting the witnesses $C_P=9$ and $C_G=9$ into the Chapter 4 consumers discharges their polynomial-growth hypotheses as follows:

1. *`TailBox` and shifted-Perron contour (`landau_lemma_lfunction_zeros`, `tail_box_negLD`, `tail_contour` in §§4.8.4–4.8.5, §4.8.7, §4.8.8).* Theorem 4.10.16 supplies $|L(w,\chi)|\le9N(1+|w|)$ to Theorem 4.8.8.4 (`LandauLemmaLfunctionZeros.lean:53`, `TailBox.lean:58`), fixing
   $$
   B_C=1+\frac{\log(42(9+1))}{\log2}=1+\frac{\log420}{\log2}\approx9.714246 .
   $$
   Together with `inverseBound` and `l_log_deriv_right`, this produces the box constant $K_B$ bounding $-L'/L$ along the left and horizontal edges of the zero-free rectangle $\mathcal B(Q)$ across which `rectangle_contour_shift_character` shifts `perron_formula_character` (§4.8.7) inside `tail_contour` (§§4.8.4–4.8.5).
2. *Local expansion, rectangle identity and smoothed/differenced explicit formula (`ex_local`, `ex_box`, `ex_negLD_bound`, `exm_core` in §§4.10.6–4.10.8).* Theorem 4.10.18 supplies named input (G) of Proposition 4.10.10 (`PNTExplLocL.lean:94`) with $C_G=9$, fixing
   $$
   C_{\mathrm{loc}}=180(\log(10100\cdot9)+3)=180(\log90900+3)\approx2595.1528 .
   $$
   Downstream in §4.10.7, `ex_box` sets $C_4=180C_{\mathrm{loc}}\approx4.671275\times10^5$, `ex_choose` selects gaps of size $d$ that guarantee the boundary-avoidance hypothesis of the exact rectangle identity `ex_rect_Fchi` (Theorem 4.10.13) when combined with `perron_formula_character`, and `ex_negLD_bound` sets $C_2=2C_{\mathrm{loc}}+100/7+C_3>5204.5912$ for the four contour budgets of `exm_core` (`smoothed_explicit_formula`), which `differenced_explicit_formula` (§4.10.6) evaluates twice at $T=M^{12}$, $\delta=M^{-5}$.
3. *Local Deuring–Heilbronn supplier (`deuring_heilbronn_local`, `PNTDHLocal.lean:167–180`).* Unpacks $C_0=9$ from Theorem 4.10.16 for $\psi\ne1$ (where $52C_0=468\le10400$) and calls `dhl_triv_growth` ($4M(1+|s|)^2$, `PNTDHLocalA.lean:31–64`) for $\psi=1$ on discs of radius $12/25$ centred at $26/25+it$, yielding `DHLocalAt` with constant $150(\log(\max(10400,52C_0))+2)=150(\log10400+2)\approx1687.48$.

#### 4.10.9.5 Proofs

**Proof of Lemma 4.10.15.** *Integral form of $d_z(s,n)$.* Fix $s\in\mathbb C$ with $\sigma=\operatorname{Re}s>0$ and $n\in\mathbb N$. When $s=1$, both sides of
$$
d_z(s,n)=(s-1)\int_{n+1}^{n+2}\big(x^{-s}-(n+2)^{-s}\big)\,dx
$$
vanish (`d_eq`, `NormCpowSubLePoint.lean:59–79`). When $s\ne1$, $1-s\ne0$; on $[n+1,n+2]$ every $x>0$ avoids the slit $(-\infty,0]$ of the principal logarithm, so $x\mapsto x^{1-s}/(1-s)$ has complex derivative $x^{-s}$ (`hasStrictDerivAt_cpow_const`), and the fundamental theorem of calculus gives $\int_{n+1}^{n+2}x^{-s}\,dx=((n+2)^{1-s}-(n+1)^{1-s})/(1-s)=((n+1)^{1-s}-(n+2)^{1-s})/(s-1)$. Subtracting $\int_{n+1}^{n+2}(n+2)^{-s}\,dx=(n+2)^{-s}$ and multiplying by $s-1$ gives the displayed integral.

*Pointwise majorant and holomorphy of $D_z$.* For $x\in[n+1,n+2]$, the map $t\mapsto t^{-s}$ on $[x,n+2]\subset(0,\infty)$ has derivative $-s\,t^{-s-1}$, so
$$
\big|x^{-s}-(n+2)^{-s}\big|=\Big|-s\int_x^{n+2}t^{-s-1}\,dt\Big|\le|s|\,(n+2-x)\sup_{t\in[x,n+2]}t^{-\sigma-1}\le|s|\,(n+1)^{-\sigma-1}
$$
because $n+2-x\le1$, $-\sigma-1<0$, and $t\ge x\ge n+1\ge1$ (`norm_cpow_sub_le_point`, `:22–44`). Integrating over $[n+1,n+2]$ of length $1$ and multiplying by $|s-1|$ yields $|d_z(s,n)|\le|s-1|\,|s|\,(n+1)^{-\sigma-1}$ (`norm_dz_le`, `DzDifferentiableOn.lean:17–22`). Each term $s\mapsto d_z(s,n)$ is entire off the slit, hence complex differentiable on $\{\operatorname{Re}s>0\}$. Around any $s_0$ with $\sigma_0=\operatorname{Re}s_0>0$, take the open neighbourhood $U=\{w:\operatorname{Re}w>\sigma_0/2\}\cap B(s_0,1)\subset\{\operatorname{Re}s>0\}$. For $w\in U$, $|w|\le|s_0|+1$, $|w-1|\le|s_0|+2$, and $(n+1)^{-\operatorname{Re}w-1}\le(n+1)^{-\sigma_0/2-1}$ because $n+1\ge1$. Since $\sigma_0/2+1>1$, the real $p$-series $\sum_{n=0}^\infty(n+1)^{-\sigma_0/2-1}$ converges (`summable_shift`, `:24–29`), so Weierstrass's $M$-test (`differentiableOn_tsum_of_summable_norm`) makes $D_z$ complex differentiable on $U$, hence on $\{\operatorname{Re}s>0\}$ (`Dz_differentiableOn`, `:31–76`).

*Identification with $(s-1)\zeta(s)$.* Induction on $N\ge0$ telescopes the partial sums (`partial_dz`, `RiemannZetaOneEqOneSubOfRePos.lean:11–22`):
$$
\sum_{n=0}^{N-1}d_z(s,n)=1-(N+1)^{1-s}-(s-1)\sum_{n=0}^{N-1}(n+2)^{-s}.
$$
When $\operatorname{Re}s>1$, $1-\operatorname{Re}s<0$, so $|(N+1)^{1-s}|=(N+1)^{1-\operatorname{Re}s}\to0$ as $N\to\infty$; meanwhile $\sum_{n=0}^\infty(n+1)^{-s}=\zeta(s)$ splits off its $n=0$ term $1$ to give $\sum_{n=0}^\infty(n+2)^{-s}=\zeta(s)-1$. Passing to the limit $N\to\infty$ gives $D_z(s)=1-(s-1)(\zeta(s)-1)=s-(s-1)\zeta(s)$, or $\operatorname{riemannZeta}_1(s)=s-D_z(s)$ on $\{\operatorname{Re}s>1\}$ (`one_lt_identity`, `:23–66`). Both $\operatorname{riemannZeta}_1(s)$ and $s-D_z(s)$ are complex differentiable, hence analytic, on the open half-plane $\{\operatorname{Re}s>0\}$; that half-plane is convex (hence preconnected), contains $s=2$, and the two functions agree on the open ball $B(2,1)\subset\{\operatorname{Re}s>1\}$. The identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) therefore equates $\operatorname{riemannZeta}_1(s)=s-D_z(s)$ on all of $\{\operatorname{Re}s>0\}$ (`riemannZetaOne_eq_one_sub_of_re_pos`, `:68–88`). For $s\ne1$, `Function.update_of_ne` rewrites the left side as $(s-1)\zeta(s)$.

*Summing the majorant and dividing by $|s-1|$.* Fix $\sigma=\operatorname{Re}s>0$. For every real $x\ge1$, applying $1-u^{-1}\le\log u$ (`one_sub_inv_le_log_of_pos`) at $u=(x+1)/x>0$ gives $\frac{1}{x+1}=1-\frac{x}{x+1}\le\log\frac{x+1}{x}$. Multiplying by $\sigma>0$ and using $1+y\le e^y$ gives
$$
1+\frac{\sigma}{x+1}\le1+\sigma\log\frac{x+1}{x}\le\exp\Big(\sigma\log\frac{x+1}{x}\Big)=\Big(\frac{x+1}{x}\Big)^\sigma .
$$
Multiplying through by $x^\sigma(x+1)>0$ gives $x^\sigma(x+1)+\sigma x^\sigma\le(x+1)^{\sigma+1}$, and dividing by $\sigma x^\sigma(x+1)^{\sigma+1}>0$ yields the telescoping step (`hkey`, `ZetaGrowth.lean:15–39`)
$$
(x+1)^{-\sigma-1}\le\frac{x^{-\sigma}-(x+1)^{-\sigma}}{\sigma}.
$$
Setting $x=n+1$ ($n=0,\dots,N-1$) and summing gives $\sum_{n=0}^{N-1}(n+2)^{-\sigma-1}\le(1-(N+1)^{-\sigma})/\sigma\le1/\sigma$. Letting $N\to\infty$ and restoring the $n=0$ term $1^{-\sigma-1}=1$ gives $\sum_{n=0}^\infty(n+1)^{-\sigma-1}=1+\sum_{n=0}^\infty(n+2)^{-\sigma-1}\le1+1/\sigma$, whence $|D_z(s)|\le\sum_{n=0}^\infty|d_z(s,n)|\le|s-1|\,|s|(1+1/\sigma)$ (`norm_Dz_le`, `:11–76`). Finally, when $s\ne1$, $|s-1|>0$ and $|s|=|(s-1)+1|\le|s-1|+1$, so
$$
|(s-1)\zeta(s)|=|s-D_z(s)|\le(|s-1|+1)+|s-1|\,|s|\Big(1+\frac{1}{\sigma}\Big).
$$
Dividing both sides by $|s-1|>0$ gives $|\zeta(s)|\le1+1/|s-1|+|s|(1+1/\sigma)$ (`growthBound`, `:78–96`). $\square$

**Proof of Theorem 4.10.16.** From `[NeZero M]` we have $M\ge1$ (`NeZero.one_le`). By (C1) applied to $[1,K]$, the non-principal character $\chi\ne1$ satisfies $\big|\sum_{n=1}^K\chi(n)\big|\le M+1$ for all $K\in\mathbb N$. Since $\operatorname{Re}s\ge1/2>0$, (C2) applied at $N=1$ with $B=M+1$ gives
$$
\big|L(s,\chi)-\chi(1)\cdot1^{-s}\big|\le2(M+1)\cdot1^{-\operatorname{Re}s}\Big(1+\frac{|s|}{\operatorname{Re}s}\Big)=2(M+1)\Big(1+\frac{|s|}{\operatorname{Re}s}\Big).
$$
Since $|\chi(1)\cdot1^{-s}|=|\chi(1)|\le1$, the triangle inequality gives $|L(s,\chi)|\le1+2(M+1)(1+|s|/\operatorname{Re}s)$, the first inequality of the theorem (`hL` at `LGrowth.lean:58–66`). Next $\operatorname{Re}s\ge1/2$ gives $1/\operatorname{Re}s\le2$, hence $|s|/\operatorname{Re}s\le2|s|$. Because $M\ge1$ and $|s|\ge0$, we have $M+1\le2M$, $1+2|s|\le2(1+|s|)$, and $1\le M(1+|s|)$. Combining these gives
$$
1+2(M+1)(1+2|s|)\le M(1+|s|)+2(2M)\cdot2(1+|s|)=(1+8)\,M\,(1+|s|)=9\,M\,(1+|s|)
$$
(`LGrowth.lean:67–71`). Thus $C_P=9$ witnesses `PolynomialGrowth`. $\square$

**Proof of Lemma 4.10.17.** Let $p\in M.\mathrm{primeFactors}$. Then $p$ is prime, so $p\ge2$ and $p>0$. For $\operatorname{Re}s\ge0$, $|p^{-s}|=p^{-\operatorname{Re}s}\le1$ because $p\ge1$ and $-\operatorname{Re}s\le0$ (`Real.rpow_le_one_of_one_le_of_nonpos`). The triangle inequality gives $|1-p^{-s}|\le1+|p^{-s}|\le2\le p$. Taking the product over the finite set $M.\mathrm{primeFactors}$ preserves nonnegativity and gives
$$
\Big|\prod_{p\in M.\mathrm{primeFactors}}(1-p^{-s})\Big|=\prod_{p\in M.\mathrm{primeFactors}}|1-p^{-s}|\le\prod_{p\in M.\mathrm{primeFactors}}p .
$$
The squarefree radical $\prod_{p\in M.\mathrm{primeFactors}}p$ divides $M$ (`Nat.prod_primeFactors_dvd`), and `[NeZero M]` gives $M>0$ (`NeZero.pos M`), so divisibility implies $\prod_{p\in M.\mathrm{primeFactors}}p\le M$ (`Nat.le_of_dvd`, `PNTExplLF.lean:106–127` and `PNTDHLocalA.lean:12–30`). $\square$

**Proof of Theorem 4.10.18.** Unpack $\langle C_0,hC_0\rangle$ from Theorem 4.10.16 and put $C_G=\max(C_0,6)$ (`PNTExplLF.lean:131–133`). Clearly $C_G\ge6\ge1$. Fix $M$ with `[NeZero M]` ($M\ge1$), $\chi\bmod M$, and $s$ with $\operatorname{Re}s\ge1/2$. Since $|s|\ge0$, $1+|s|\ge1$, so $1+|s|\le(1+|s|)^2$.

- *Non-principal case ($\chi\ne1$).* Here $f_\chi(s)=L(s,\chi)$. By $hC_0$, $C_0\le C_G$, and $1+|s|\le(1+|s|)^2$, we obtain $|f_\chi(s)|\le C_0M(1+|s|)\le C_GM(1+|s|)\le C_GM(1+|s|)^2$ (`:176–184`).
- *Principal case at $s=1$ ($\chi=1$, $s=1$).* Unfolding `exLF` and `LFunctionTrivChar₁` at $s=1$ via `Function.update_self` gives $f_{\chi_0}(1)=\prod_{p\in M.\mathrm{primeFactors}}(1-p^{-1})=\prod_{p\in M.\mathrm{primeFactors}}(1-p^{-1_{\mathbb C}})$. Lemma 4.10.17 at $s=1$ bounds $|f_{\chi_0}(1)|\le M\le6M(1+|1|)^2=24M\le C_GM(1+|1|)^2$ (`:138–149`).
- *Principal case away from $1$ ($\chi=1$, $s\ne1$).* By `Function.update_of_ne` and `LFunctionTrivChar_eq_mul_riemannZeta`,
  $$
  f_{\chi_0}(s)=(s-1)\Big(\prod_{p\in M.\mathrm{primeFactors}}(1-p^{-s})\Big)\zeta(s).
  $$
  Since $\operatorname{Re}s\ge1/2>0$ and $s\ne1$, Lemma 4.10.15 applies and $1/\operatorname{Re}s\le2$; also $|s-1|\le1+|s|$ and $|s-1|>0$. Multiplying Lemma 4.10.15 by $|s-1|$ cancels $1/|s-1|$:
  $$
  \begin{aligned}
  |s-1|\,|\zeta(s)| &\le |s-1|+1+|s-1|\,|s|\Big(1+\frac{1}{\operatorname{Re}s}\Big) \\
  &\le (1+|s|)+1+(1+|s|)\cdot3|s| \\
  &= 2+4|s|+3|s|^2 \le 6(1+|s|)^2,
  \end{aligned}
  $$
  since $6(1+|s|)^2-(2+4|s|+3|s|^2)=4+8|s|+3|s|^2\ge0$ (`hA`, `:163–169`; in `dhl_triv_growth`, `PNTDHLocalA.lean:55–60`, the same polynomial $2+4|s|+3|s|^2$ is bounded by $4(1+|s|)^2=4+8|s|+4|s|^2$). Multiplying by Lemma 4.10.17 ($\le M$) gives $|f_{\chi_0}(s)|\le6M(1+|s|)^2\le C_GM(1+|s|)^2$ (`:170–175`).

With $C_0=C_P=9$ from Theorem 4.10.16, $C_G=\max(9,6)=9$. $\square$

**Proof of Corollary 4.10.19.** In Theorem 4.8.8.4 (`LandauLemmaLfunctionZeros.lean:53`), `lfunction_polynomial_growth` supplies $C=9>0$, so $|C|+1=10$ and $B_C=1+\log(42\cdot10)/\log2=1+\log420/\log2$. In Proposition 4.10.10 (`PNTExplLocL.lean:94`), `exLF_growth` supplies $C_G=9$, so $10100C_G=90900$ and $C_{\mathrm{loc}}=180(\log90900+3)$, which flows directly into `PNTExplBox.lean:121` ($C_4=180C_{\mathrm{loc}}$) and `PNTExplNeg.lean:33` ($C_2=2C_{\mathrm{loc}}+100/7+C_3$). In `PNTDHLocal.lean:170–179`, `deuring_heilbronn_local` unpacks $C_0=9$ from `lfunction_polynomial_growth` and sets $K=\max(10400,52C_0)=\max(10400,468)=10400$, calling `dhl_triv` (backed by `dhl_triv_growth`) for $\psi=1$ and `dhl_nontriv` for $\psi\ne1$. $\square$

#### 4.10.9.6 Failure examples and remarks

**Deleting $\operatorname{Re}s\ge1/2$ [Expository].** Both branches fail once $s$ leaves the right half-plane.

- *Non-principal archimedean blow-up.* Take $M=4$ and $\chi_{-4}$. At negative even integers $s=-2k$ ($k\ge1$), Hurwitz's Bernoulli/Euler formula gives $L(-2k,\chi_{-4})=(-1)^kE_{2k}/2$, where the Euler numbers satisfy $|E_{2k}|\sim4\sqrt{k/\pi}(4k/(\pi e))^{2k}$. Already at $s=-10$ ($k=5$, $E_{10}=-50521$),
  $$
  |L(-10,\chi_{-4})|=\frac{50521}{2}=25260.5 ,
  $$
  exceeding both $9\cdot4\cdot(1+10)=396$ (Theorem 4.10.16) and $9\cdot4\cdot(1+10)^2=4356$ (Theorem 4.10.18). Vertically, the functional equation and Stirling's formula give $|L(\sigma+it,\chi_{-4})|\asymp|t|^{1/2-\sigma}$ along any fixed line $\operatorname{Re}s=\sigma<0$ as $|t|\to\infty$: for $\sigma<-1/2$ this outgrows $(1+|s|)$ for every constant $C_P$, and for $\sigma<-3/2$ it outgrows $(1+|s|)^2$ for every constant $C_G$. Even inside the strip $0<\operatorname{Re}s<1/2$, the $1/\operatorname{Re}s$ factor in Lemma 4.10.15 and Theorem 4.10.16 diverges as $\operatorname{Re}s\to0^+$.
- *Bad-prime Euler-factor blow-up.* In Lemma 4.10.17 at $M=5$ and $s=-2$ ($\operatorname{Re}s<0$), the single Euler factor has $|1-5^2|=24>5=M$. More generally, at $s=-\sigma<0$ for squarefree $M$, $\prod_{p\mid M}(p^\sigma-1)$ grows like $M^\sigma$, destroying linear dependence on $M$ whenever $\sigma>1$.

**Deleting $\chi\ne1$ or the $(s-1)$ `exLF` factor [Expository].** Take $M=5$ (`[NeZero 5]`), $\chi=\chi_0$, and $s=1+\varepsilon$ with $\varepsilon>0$, so $\operatorname{Re}s>1\ge1/2$ holds. Without the $(s-1)$ factor of `exLF`, $L(1+\varepsilon,\chi_0)=(1-5^{-1-\varepsilon})\zeta(1+\varepsilon)\sim\frac{4}{5\varepsilon}$ as $\varepsilon\to0^+$, whereas $CM(1+|1+\varepsilon|)\to10C$ and $CM(1+|1+\varepsilon|)^2\to20C$. Already at $s=1.001$ ($\varepsilon=10^{-3}$),
$$
L(1.001,\chi_0)\approx800.783645 > 9\cdot5\cdot(2.001)^2\approx180.180045 > 9\cdot5\cdot2.001=90.045 ,
$$
and letting $\varepsilon\to0^+$ defeats every finite constant $C$ on $\operatorname{Re}s\ge1/2$.

**Deleting `[NeZero M]` ($M=0$) [Expository].** At $M=0$ the right-hand sides $C_PM(1+|s|)$ and $C_GM(1+|s|)^2$ vanish identically. Every layer of the proof breaks at $M=0$:

- In Lemma 4.10.17 (`exLF_prod_le`), Mathlib defines `Nat.primeFactors 0 = ∅` (`Factorization/Basic.lean:45`), so the empty product equals $1$ and $|1|=1>0=M$. The exact line that fails is `Nat.le_of_dvd (NeZero.pos M) (Nat.prod_primeFactors_dvd M)`: $1\mid0$ is true, yet $1\le0$ is false without $M>0$.
- In Mathlib's `ZMod.LFunction` (`ZMod.lean:67,83`), `[NeZero M]` is a typeclass prerequisite because `ZMod 0 = ℤ` is infinite rather than periodic modulo a positive integer; if one evaluates the naive Dirichlet series $\sum_{n=1}^\infty\chi(n)n^{-s}$ for either multiplicative character of $\mathbb Z$ (supported on $\mathbb Z^\times\cap\mathbb N_{\ge1}=\{1\}$, with $\chi(1)=1$ and $\chi(n)=0$ for $n\ge2$), it equals $1$ for all $s\in\mathbb C$, again violating $1\le0$.

**Why coarse exponents cost nothing downstream.** Replacing $(1+|s|)$ by $(1+|s|)^2$ in `exLF_growth`, or bounding $|A(K)|\le M+1$ instead of Pólya–Vinogradov's $\sqrt M\log M$, or bounding $\prod_{p\mid M}|1-p^{-s}|\le M$ instead of $2^{\omega(M)}$, only changes polynomial exponents of $M$ and $|t|+2$ inside the upper bound $B$ on the disc. Every consumer in Corollary 4.10.19 immediately applies $\log B$, turning $M^a(|t|+2)^b$ into $a\log M+b\log(|t|+2)\le\max(a,b)\log(M(|t|+2))$ and folding all polynomial exponents into a fixed scalar factor. Likewise, `dhl_triv_growth` (`PNTDHLocalA.lean:55–60`) sharpens the principal coefficient from $6$ to $4$, whereas `exLF_growth` writes $6$; once combined with $C_P=9$, $\max(9,6)=\max(9,4)=9$ is unchanged.

**Classical comparison [Paper].** Classical analytic number theory proves these bounds by the same two mechanisms with slightly sharper Calculus-based majorants. For $\zeta(s)$, Tao's 254A Notes 2 [[Tao2014, §2, eq. (21)](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/)] and Montgomery–Vaughan [[MontgomeryVaughan2007, Theorem 1.12]] write Euler–Maclaurin continuation on $\operatorname{Re}s>0$ as $\zeta(s)=\frac{s}{s-1}-s\int_1^\infty\{x\}x^{-s-1}\,dx$, obtaining $|\zeta(s)-\frac{s}{s-1}|\le|s|/\operatorname{Re}s$. In the archive, $-\int_{n+1}^{n+2}(x-(n+1))s\,x^{-s-1}\,dx$ is rewritten by parts as $(n+1)^{1-s}-(n+2)^{1-s}-(s-1)(n+2)^{-s}=d_z(s,n)$, avoiding fractional-part measurability at the cost of one factor $(s-1)$ that cancels upon division when $s\ne1$. For non-principal $L(s,\chi)$, Davenport [[Davenport2000, §4 and Ch. 12]] and Tao [[Tao2014, Exercises 44–45](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/)] pair Abel summation on $\operatorname{Re}s\ge1/2$ with either the trivial character-sum bound $M$ or Pólya–Vinogradov $\sqrt M\log M$ (giving $|L(s,\chi)|\ll\sqrt M\log M\,(1+|t|)$); the Phragmén–Lindelöf convexity bound $|L(1/2+it,\chi)|\ll_\varepsilon(M(|t|+2))^{1/4+\varepsilon}$ [[MontgomeryVaughan2007, §10.1]] requires the functional equation and Gamma asymptotics, neither of which the archive's elementary disc route needs.

#### 4.10.9.7 Source map and reading boundary

Archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Short `PNT*` paths are relative to `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/` and other archive paths to `src/Formalism/`. All 22 archive files tabulated below were extracted from `lean.tar.gz` and verified byte-identical to the read-only copy.

| Layer and role | Location | Status |
|---|---|---|
| Unified growth `exLF_growth` | `PNTExplLF.lean:129–184` | Local R3 [Lean, read] |
| Bad-prime Euler-product bound `exLF_prod_le` (and `dhl_prod_le`, `dhl_triv_growth`) | `PNTExplLF.lean:106–127`; `PNTDHLocalA.lean:12–64` | Local R3 [Lean, read] |
| Non-principal growth `lfunction_polynomial_growth` | `LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:53–71` (interface `PolynomialGrowth` at `LFunctionBounds/PositivityBound.lean:25–28`) | Local R3 [Lean, read] |
| Zeta power-difference continuation and `growthBound` | `ZeroFreeRegion/ZetaLogDerivativeBounds/NormCpowSubLePoint.lean:11–79` (`norm_cpow_sub_le_point`, `d_eq`); `DzDifferentiableOn.lean:11–76` (`dz`, `Dz`, `norm_dz_le`, `Dz_differentiableOn`); `RiemannZetaOneEqOneSubOfRePos.lean:11–88` (`partial_dz`, `one_lt_identity`, `riemannZetaOne_eq_one_sub_of_re_pos`); `ZetaGrowth.lean:11–96` (`norm_Dz_le`, `growthBound`; interface `ZetaGrowth` at `ZeroFreeRegion/SmallHeightLogDeriv.lean:66–69`) | Local R3 [Lean, read] |
| Inherited non-principal partial-sum suppliers | `LGrowth.lean:10–51` (`norm_character_sum_Icc_le`); `LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean:136–169` (`l_function_partial_sum`); `LFunctionEqGOfOneLt.lean:228` (`LFunction_eq_G`) | Inherited [Lean, read] from §4.7 |
| Downstream consumers | `LandauZeroFreeBounds/ExceptionalZeroBounds/LandauLemmaLfunctionZeros.lean:9–91` and `TailBox.lean:13–119` (§4.8.8); `PNTExplLocL.lean:86–146` (§4.10.8); `PNTExplBox.lean:121`, `PNTExplNeg.lean:27–102`, `PNTExplMainB.lean:138–168`, `PNTExplMain.lean:15–97` (§4.10.7); `PNTDHLocal.lean:77–180` (`dhl_triv`, `deuring_heilbronn_local`, call sites read) | Inherited [Lean, read] (§§4.8.8, 4.10.7–4.10.8) and call sites read |
| Pinned Mathlib inputs (`0df444a`) | `NumberTheory/LSeries/DirichletContinuation.lean:61,169,174,338,348`; `NumberTheory/LSeries/ZMod.lean:67,83`; `NumberTheory/LSeries/RiemannZeta.lean`; `NumberTheory/Harmonic/ZetaAsymp.lean:536,561`; `Data/Nat/Factorization/Basic.lean:45,350`; calculus/analyticity API (`hasStrictDerivAt_cpow_const`, `differentiableOn_tsum_of_summable_norm`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `one_sub_inv_le_log_of_pos`) | Statement level [Lean] |
| Retained deeper analytic suppliers | `ZeroSum` (`PNTZSumL`) with `LogDensityM` (`PNTDens`) and `DeuringHeilbronnMB` (`PNTDHB`); `twist_bound`, `zFRDirichlet`, `excBound`/`siegelLower` | Retained R2 [Lean] |

Reading `exLF_growth`, `lfunction_polynomial_growth` and `growthBound` closes the last `R2` supplier of `ex_local` (§4.10.8) and the polynomial-growth supplier of `TailBox` (§4.8.8). Section 4.10.10 reads the Laurent remainder. This leaves the deeper inputs tabulated in the final row at their previous reading levels. Local R3 records human-assisted source reading of the pinned archive, not a Lean kernel check. See the [source ledger](../sources/SOURCES.md#chapter-4-4109-uniform-polynomial-growth).

### 4.10.10 The pole-subtracted zeta logarithmic derivative

#### 4.10.10.1 Motivation

The smoothed explicit formula needs a bound for the numerator $-L'/L$ on an entire vertical line. As the line approaches $1$ from the right, the budget must accommodate the principal character's pole. The archive first removes the pole of $\zeta'/\zeta$ on a neighborhood of $1$. It then uses positivity of the von Mangoldt coefficients to transfer a real-axis estimate to all heights. The same supply is spent on the right side of the zero-free box in §4.8.8.

#### 4.10.10.2 Two worked calculations [Expository]

**A real point close to the pole.** Take $s=1+h$, $h=1/1000$. The regular part $A$ defined below satisfies $|A|\le3$ and $|A'|\le4$ on $|s-1|\le1/4$, as proved in §4.10.10.5. Integrating $A'$ along the real segment gives $|A(1+h)-\gamma|\le4h$. The pole-subtracted value is
$$
R(1+h)=\frac{A(1+h)+h A'(1+h)}{1+h A(1+h)}.
$$
The denominator has modulus at least $1-3h$. Integral comparison for harmonic sums gives $H_4-\log5\le\gamma\le H_4-\log4$ with $H_4=25/12$. Since $\log(5/4)<1/4$, the lower bound exceeds $H_4-\log4-1/4$. In $\log 2=2\sum_{j\ge0}3^{-(2j+1)}/(2j+1)$ the first two terms exceed $69/100$ and the remaining tail is bounded by $2/(5\cdot3^5(1-1/9))$, giving $\log2<70/100$. Thus $13/30<\gamma<211/300<1$. Subtracting $\gamma$ from the quotient gives
$$
|R(1+h)-\gamma|\le\frac{(4+4+3)h}{1-3h}=\frac{11}{997}<\frac{3}{250}.
$$
Consequently $0.42<R(1+h)<0.72$ and $999.28<-\zeta'(1+h)/\zeta(1+h)<999.58$. The decimal endpoints here and below are rational bounds. The $1000$ in the uncorrected expression comes from the pole alone.

**A point of nonzero height.** At $s=5+i$, write $S=-\zeta'/\zeta$. Its $n=2$ term is $\ell(\cos\ell-i\sin\ell)/32$ with $\ell=\log2$. The alternating Taylor bounds $1-\ell^2/2\le\cos\ell\le1-\ell^2/2+\ell^4/24$ and $\ell-\ell^3/6\le\sin\ell\le\ell-\ell^3/6+\ell^5/120$ give $0.75<\cos\ell<0.80$ and $0.63<\sin\ell<0.65$. Both sine polynomials are increasing on $[0.69,0.70]$, so their respective endpoint values suffice. The remaining terms have total modulus bounded by a decreasing-integrand comparison:
$$
\sum_{n\ge3}\frac{\log n}{n^5}
\le\int_2^\infty\frac{\log x}{x^5}\,dx
=\frac{\log2/4+1/16}{16}<0.015.
$$
The real part of the first term lies between $0.69\cdot0.75/32$ and $0.70\cdot0.80/32$, and its imaginary part between $-0.70\cdot0.65/32$ and $-0.69\cdot0.63/32$. With the tail these give $0.001<\Re S(5+i)<0.033$ and $-0.030<\Im S(5+i)<0.002$. Since $1/(4+i)=(4-i)/17$, we obtain
$$
0.202<\Re R(5+i)<0.235,\qquad -0.061<\Im R(5+i)<-0.028.
$$
The horizontal distance to $\Re s=1$ is $4$ and the distance to the pole is $\sqrt{17}$. The uniform bound for the uncorrected quotient uses the horizontal distance. The phase of the $n=2$ term illustrates what the vertical-line majorant discards.

#### 4.10.10.3 Definitions

Set $A(s)=\zeta(s)-1/(s-1)$ off $1$ and $A(1)=\gamma$. The pole-removed function $F(s)=1+(s-1)A(s)$ satisfies $F(1)=1$ and equals $(s-1)\zeta(s)$ off $1$. Write
$$
R(s)=\frac{\zeta'(s)}{\zeta(s)}+\frac{1}{s-1}
$$
when $s\ne1$ and $\zeta(s)\ne0$. For real $\sigma>1$ write $\lambda(\sigma)=\sum_{n\ge1}\Lambda(n)n^{-\sigma}$. The archive's `lamF` uses the sum of the norms of these terms, equal to this sum by nonnegativity.

#### 4.10.10.4 Lemma and theorem

**Lemma 4.10.20 (local pole subtraction) [Lean, read].** On a punctured neighborhood of $1$, $R=F'/F$ and $R(s)=\gamma+O(|s-1|)$. The corrected quotient extends holomorphically across $1$. In particular it is bounded near $1$. The proof below gives $|R|\le6$ for $0<|s-1|\le1/8$ [Expository].

**Theorem 4.10.21 (right-half-plane supply) [Lean, read].** There is an absolute $C_R\ge0$ such that for $\sigma=\Re s>1$ and any Dirichlet character of positive modulus,
$$
\left|\frac{\zeta'(s)}{\zeta(s)}\right|\le\frac1{\sigma-1}+C_R,
\qquad
\left|-\frac{L'(s,\chi)}{L(s,\chi)}\right|\le\frac1{\sigma-1}+C_R.
$$
One may use $C_R=22>0$ for both inequalities [Expository]. On $\Re s\ge1+d$ with $d>0$ the inequalities give a uniform bound $1/d+22$, and the triangle inequality gives $|R(s)|\le2/d+22$ there. The distance condition is a horizontal clearance into the right half-plane.

#### 4.10.10.5 Proof

**Production near $1$.** In pinned Mathlib, `riemannZeta₀` is $A$ and `riemannZeta₁` is $F$. The proof of differentiability of $A$ combines differentiability off $1$ with continuity at $1$ from the inherited punctured limit $\gamma$. The removable singularity theorem gives the entire regular part. The formula for $F$ gives $F'(1)=\gamma$ and $F(1)=1$. Continuity makes $F$ nonzero on some disc about $1$. Differentiating $\zeta(s)=F(s)/(s-1)$ away from $1$ gives $\zeta'(s)=F'(s)/(s-1)-F(s)/(s-1)^2$. Dividing by $\zeta(s)$ on the punctured disc gives
$$
\frac{\zeta'(s)}{\zeta(s)}=-\frac1{s-1}+\frac{F'(s)}{F(s)}.
$$
The quotient $F'/F$ is differentiable at $1$ with value $\gamma$, so subtracting that value gives $O(|s-1|)$ on the full neighborhood. Mathlib restricts this estimate to the punctured neighborhood and rewrites it using the displayed identity. It then uses $s-1=o(1)$ to infer $R-\gamma=o(1)$, weakens this to $O(1)$ and adds the constant back. This is the production of `log_deriv_riemannZeta_add_inv_sub_bounded`. Its `.bound` supplies a real $B$ and a punctured neighborhood where $|R|\le B$. The archive extracts an open ball of radius $\varepsilon>0$ from that neighborhood.

**Transfer to the unbounded half-plane.** In $\Re s>1$ the absolutely convergent Dirichlet series for zeta times the series for the Möbius function is $1$, by Dirichlet convolution. The twist has the corresponding inverse with coefficients $\chi(n)\mu(n)$. The pinned von Mangoldt proof uses $\Lambda*1=\log$ in Dirichlet convolution, given by prime factorization. Multiplying the series for $\Lambda$ by $\zeta$ gives the series for $-\zeta'$ by termwise differentiation. Division uses nonvanishing. For the twist, complete multiplicativity gives the same convolution with factors of $\chi$. Equality of the series and continued functions on the open half-plane also identifies their derivatives there.

For $s=\sigma+it$ with $\sigma>1$, the triangle inequality, $|n^{-it}|=1$ and $|\chi(n)|\le1$ bound both quotients by $\lambda(\sigma)$. On the real axis $\lambda(\sigma)=-\zeta'(\sigma)/\zeta(\sigma)>0$ because the term for $2$ is positive. The sum decreases with $\sigma$ by termwise comparison. For $1<\sigma<1+\varepsilon/2$, the real point $\sigma$ is in the punctured disc, so $\lambda(\sigma)\le1/(\sigma-1)+B$. For $\sigma\ge1+\varepsilon/2$ monotonicity gives $\lambda(\sigma)\le\lambda(1+\varepsilon/2)$. The archive chooses $C_R=\max(\max(B,0),\lambda(1+\varepsilon/2))>0$. The compact estimate can be taken on a smaller closed disc using the continuous extension of $R$. The unbounded part uses monotonicity and the vertical-line comparison, so no compactness claim about an infinite strip is needed.

**A quantitative witness [Expository].** In $\Re s>1$, integrating the counting function gives $\zeta(s)=s\int_1^\infty\lfloor x\rfloor x^{-s-1}\,dx$. Substitute $\lfloor x\rfloor=x-\{x\}$ to obtain
$$
A(s)=1-s\int_1^\infty\{x\}x^{-s-1}\,dx.
$$
The integral and its derivative converge locally uniformly for $\Re s>0$, by domination by $x^{-1-\sigma_0}(1+\log x)$ when $\Re s\ge\sigma_0>0$. Analytic continuation gives the identity there, including at $1$. On $|s-1|\le1/4$ one has $\sigma\ge3/4$ and $|s|\le5/4$. Integrating the bounds with $\{x\}\le1$ gives $|A|\le1+(5/4)(4/3)=8/3<3$ and $|A'|\le4/3+(5/4)(4/3)^2=32/9<4$. On the closed disc of radius $1/8$, $|F|\ge1-3/8=5/8$ and $|F'|\le3+4/8=7/2$. Thus $|F'/F|\le28/5<6$. Take $(B,\varepsilon)=(6,1/8)$. At $\sigma=1+1/16$, the local estimate gives $\lambda(1+1/16)\le16+6=22$. The maximum from the proof is at most $22$, so $22$ serves directly as a witness.

**Corollary 4.10.22 (consumer constants) [Expository].** Use $C_3=22$ for `ex_tail_bound` in `ExplicitS`. On $w=\sigma_0+it$ the numerator costs $1/(\sigma_0-1)+22$. The factors $|w|$ and $|w-1|$ are each at least $|t|$. Integrating the two tails of $t^{-2}$ contributes $2(1/(\sigma_0-1)+22)y^{\sigma_0}/T'$ in the unnormalized integral. At $\sigma_0=1+1/\log y$ this gives the $\log y+C_3$ term in `exm_core`. Independently, `ex_negLD_bound` spends the same witness at $\Re s\ge107/100$, where the pole budget is at most $100/7$. Its other branch spends twice the inherited local constant from §§4.10.8–4.10.9 after division by the zero clearance. Therefore one may choose
$$
C_2=360(\log90900+3)+100/7+22<5230.
$$
Indeed the terms $0$ through $32$ of the exponential series at $571/50$ sum to more than $90900$, so $\log90900<571/50$. Both $C_2$ and $C_3$ may be enlarged in the residual majorant. These choices witness the existential estimates, for which the archive uses qualitative Big-O extraction.

In `TailBox`, the branch $\Re s\ge11/10$ spends $10+C_R=32$, absorbed as $(32/\log2)\log Q$ for $Q\ge2$. The other branch uses the local expansion and zero clearance from §4.8.8. With the inherited growth witness $9$, the box budget admits
$$
K=3(1+\log420/\log2)\left(\frac{1440}{11}+\frac1{\delta\log2}\right)+\frac{32}{\log2}.
$$
The same $22$ thus supplies a separate consumer, which retains its clearance hypothesis $\delta>0$.

#### 4.10.10.6 Failure examples and total-function conventions

If a holomorphic $f$ has a zero $\rho$ of order $m\ge1$, write $f(s)=(s-\rho)^m u(s)$ with $u(\rho)\ne0$. Then $f'/f=m/(s-\rho)+u'/u$. Dropping zero-freeness from a compact-domain argument allows this genuine pole even when the evaluation points avoid the zero. For zeta, take the known trivial zero $\rho=-2$. Both $u'/u$ and $1/(s-1)$ are bounded in a small disc there. Along $s=-2+h$ as $h\downarrow0$, $|R(s)|$ tends to infinity even though $\zeta(s)\ne0$ at those points and $|s-1|>2$. This refutes replacing the right-half-plane hypothesis by distance from $1$ alone, including a bound with $1/|s-1|$ on the right side. Within $\Re s>1$ the zero-free property already follows from the series inverse. Extending the original bound with the signed denominator $1/(\sigma-1)$ to the real left of $1$ makes its right side negative sufficiently near $1$.

Lean assigns `riemannZeta 1` the value $(\gamma-\log(4\pi))/2$ at the pin. Zeta has no derivative at $1$ in the analytic sense, and `deriv` returns zero at a point of nondifferentiability. Field inverse returns zero at zero. Thus the raw Lean expression for $R$ evaluates to zero at $1$, while its analytic extension $F'/F$ takes the value $\gamma$. At a zero of zeta the raw quotient likewise evaluates to zero, while the punctured logarithmic derivative has a pole.

#### 4.10.10.7 Source map and reading boundary

A2 is the fixed archive with joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Archive paths below are relative to `src/Formalism/`. The Mathlib pin is `0df444a360eaa60ab8c11dca51a86af692955474`. [Source ledger](../sources/SOURCES.md#chapter-4-41010-pole-subtraction-and-the-right-half-plane)

| Role | File and lines | Reading |
|---|---|---|
| Regular parts, differentiation and final asymptotic | Mathlib `NumberTheory/Harmonic/ZetaAsymp.lean:531–589,620–647` | Local R3 [Lean, read] |
| Nonvanishing and positive series intermediary | Mathlib `NumberTheory/LSeries/Dirichlet.lean:296–329,372–389,395–442` | Direct proof bodies read, underlying Dirichlet-series API used by statement |
| Real-axis split and twist transfer | `ZeroFreeRegion/SmallHeightLogDeriv.lean:25–27`, `ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivRight.lean:11–42`, `NormLogDerivLeLamF.lean:11–50` in the same directory, `LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean:88–126` | [Lean, read], archive bodies also used in §4.8.8 |
| Consumer calls under `GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/` | `PNTExplNeg.lean:27–54`, `PNTExplEdge.lean:113–148`, `PNTExplMainB.lean:31–53`, `PNTExplMain.lean:19–23,79–85`, `TailBox.lean:35–48,104–119` | Inherited local proofs, call sites checked |
| Earlier inputs | Laurent constant `tendsto_riemannZeta_sub_one_div`, Mathlib `ZetaAsymp.lean:342–350`. Perron, local rectangles and growth in §§4.8.7–4.8.8 and §§4.10.7–4.10.9 | Inherited |
| Deeper inputs | `PNTDHLocal` (`deuring_heilbronn_local`), `PNTZSumL` (`ZeroSum`), `PNTDens` (`LogDensityM`), `PNTDHB` (`DeuringHeilbronnMB`), `twist_bound`, `zFRDirichlet`, `excBound` and `siegelLower` | Previous scope retained, full production bodies outside this reading |

The right-half-plane branch now has its Laurent producer exposed, completing the local reading of the custom estimates used by the smoothed explicit formula. Local R3 denotes source reading. The numerical witnesses and enclosures are textbook calculations.

Riemann opens his 1859 memoir with Euler's product and Dirichlet series in $\Re s>1$. Tao's *254A Notes 2* gives the von Mangoldt identity in the complex domain and uses $(s-1)\zeta(s)$ in Proposition 19. [Riemann 1859, p. 671](https://www.maths.tcd.ie/pub/HistMath/People/Riemann/Zeta/Zeta.pdf) · [Tao 2014](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/)

### 4.10.11 Finite-height contours and weighted zero sums

#### Motivation

A truncated explicit formula uses two kinds of height cutoff. Its contour must miss every pole, whereas its zero count is most useful with closed intervals, so that zeros at nominal height $T$ are included. The production proof moves the contour out to a separated height $H\in[T,T+1]$. The resulting finite list can then be estimated by density bounds that apply only to separated ordinates. We will prove how to choose the contour and how to convert a separated count into a count with multiplicity. The logarithmic-derivative bounds and growth estimates of §§4.10.8–4.10.10 enter as named inputs.

#### Two model calculations [Expository]

Take $\kappa=1/20$, so the left-edge interval is $[76/80,77/80]$, let $b=39/40=78/80$, and take $y=\exp(2\pi)$. Our polynomials stand in for the entire functions used to remove the principal pole. Their contour integrands are $-f'(s)y^s/(f(s)s(s-1))$, so there is also a kernel pole at $1$. In both models the right edge is $1+1/\log y$. The finite sums below are the zero terms in the normalized contour identity, after division by $y$. For any integer $n$,
$y^{b+in-1}=y^{-1/40}$, and $(b+in)(b+in-1)=-(1600n^2+39)/1600+in(38/40)$.

**A. Nominal height $2$, both ordinates interior.** Let $f(s)=(s-b-i)^2(s-b+i)$. Both zeros lie in the closed counting box of height $5$. There are $N_0=2$ distinct zeros, so the common guaranteed gap from the construction below is $\kappa/(8(N_0+1))=1/480$. Choose the left edge $\sigma=76/80$ and $H=2$. The actual coordinate gaps are $1/40$ and $1$ respectively. The floor intervals containing the zeros are $[1,2)$ and $[-1,0)$, both odd. Both representatives can be used in a single separated sample since their ordinates differ by $2$. The mass is $2+1=3$. Any closed unit window has mass at most $3$, attained at centre $0$ where both endpoints count. With $p=1639$ and $q=1520$, the normalized sum is
$1600y^{-1/40}(2/(-p+iq)+1/(-p-iq))=1600y^{-1/40}(-3p-iq)/(p^2+q^2)$. The kernel-pole contribution after normalization is $-f'(1)/f(1)=-(3/40+i)/(1+1/1600)$, from adding $-2/(1/40-i)$ and $-1/(1/40+i)$. The normalized counterclockwise contour therefore gives this kernel contribution minus the displayed zero sum.

**B. Nominal height $4$, a double zero on the proposed top edge.** Let $f(s)=(s-b-4i)^2(s-b-3i)$. Now the closed counting box has height $7$ and $N_0=2$ again. Choose $\sigma=77/80$ and $H=9/2$; the actual gaps are $1/80$ and $1/2$, at least $1/480$. The roots occupy $[3,4)$ and $[4,5)$, of opposite parities. Their unweighted count is $2$ and mass is $1+2=3$. The closed unit window centred at $3$ includes both roots, while a half-open window $[2,4)$ has only mass $1$. The real majorant weights $m y^{\Re\rho-1}$ have total masses $3y^{-1/40}$ at the wider cuts and $y^{-1/40}$ at the lower cut in B. The two denominators multiplied by $1600$ are $-14439+4560i$ and $-25639+6080i$, so the normalized sum is
$1600y^{-1/40}(1/(-14439+4560i)+2/(-25639+6080i))$. The normalized kernel-pole contribution is $-1/(1/40-3i)-2/(1/40-4i)$, independent of the height. If the contour is moved to $H=7/2$, the sum loses precisely $3200y^{-1/40}/(-25639+6080i)$. At $H=4$ the pole itself prevents the ordinary contour identity; the two one-sided limits of normalized rectangle integrals differ by the negative of that same term. These examples use exactly computable model poles and make no assertion about the locations of Dirichlet zeros.

#### Definitions and named inputs

Let $M\ge3$, $\chi$ be a character modulo $M$, and $L_\chi=L(s,\chi)$. Write $\epsilon_\chi=1$ for the principal character and $0$ otherwise. Let $f_\chi$ be the entire function agreeing with $(s-1)^{\epsilon_\chi}L_\chi(s)$ away from $1$, with the analytic value at $1$. In the archive this is *exLF*. It is nonzero at $1$ and has exactly the zeros of *IsLZero*, which excludes the principal pole by definition. Write $m_\chi(\rho)$ for its positive analytic order at a zero (*exOrd*). The local factorization $f_\chi(s)=(s-\rho)^{m_\chi(\rho)}g(s)$ with $g(\rho)\ne0$ gives $f'_\chi/f_\chi=m_\chi(\rho)/(s-\rho)+g'/g$. Use $D_\chi=-L'_\chi/L_\chi$ off the special points and $K_\chi=-f'_\chi(1)/f_\chi(1)$. For $y>0$ use $y^s=\exp(s\log y)$. Let $S_\chi(y)=\sum_{n\le y}\chi(n)\Lambda(n)(y/n-1)$ and $\psi_\chi(y)=\sum_{n\le y}\chi(n)\Lambda(n)$. The term at $n=y$ is zero in $S_\chi$ and included in $\psi_\chi$ when $y$ is an integer.

We use three earlier inputs. The first is the closed box *ex_box*: for $U\ge0$ the zeros with $\Re\rho\ge9/10$ and $|\Im\rho|\le U$ form a finite set of cardinality at most $C_4(U+1)\log(M(U+2))$, and the sum of orders in its closed unit window centred at $t$ is at most $C_4\log(M(|t|+2))$. The second comprises nonvanishing in $\Re s\ge1$ off the principal pole, and *ex_negLD_bound* from §4.10.7, with the analytic inputs of §§4.10.8–4.10.10. In $19/20\le\Re s\le3$, $s\ne1$, require distance $d\in(0,1/20]$ from zeros with $\Re\rho\ge9/10$ and $|\rho-s|\le1/5$. The bound for $|D_\chi(s)|$ is $C_2\log(M(|\Im s|+2))/d+\epsilon_\chi/|s-1|$. The third is Perron inversion for the kernel $y^s/(s(s-1))$ with vertical integral normalized by $1/(2\pi i)$ equal to $S_\chi(y)$, and the right-line bound $|D_\chi(c+it)|\le 1/(c-1)+C_R$, with the earlier witness $C_R=22$. The polynomial-growth supply used in the local estimates is inherited from §4.10.9.

#### The contour and the list it produces

**Lemma 4.10.23 (coordinate gaps) [Lean, read].** For an interval $[a,b]$ of positive length and a finite forbidden set of $n$ real coordinates, there is a point at distance at least $(b-a)/(2(n+1))$ from every forbidden coordinate.

**Proof.** Put $h=(b-a)/(2(n+1))$. The $n+1$ test points $a+(2j+1)h$, $0\le j\le n$, belong to the interval. The open intervals of radius $h$ about them are disjoint. Each forbidden coordinate blocks at most one test point, so one test point survives. Using open intervals is what yields the weak lower bound, including exact equality at the gap. This is the pigeonhole argument of *ex_pick*. [A2, PNTExplPick.lean:11–41](../sources/SOURCES.md#chapter-4-41011-finite-height-contours-and-weighted-zero-sums)

<a id="p13-finite-height-explicit-formula"></a>

**Theorem 4.10.24 (finite-height explicit formula with a separated contour, conditional on the three inputs).** For $0<\kappa\le1/20$ and $T\ge2$ there are $\sigma\in[1-\kappa,1-3\kappa/4]$, $H\in[T,T+1]$ and $d>0$, chosen independently of $y$, such that
$d\le1/20$ and $d\ge\kappa/[8(4C_4+1)(T+1)\log(M(T+2))]$.
Let $Z_\chi$ consist of the zeros with $\Re\rho>\sigma$ and $|\Im\rho|<H$. It contains every zero with $\Re\rho\ge1-3\kappa/4$ and $|\Im\rho|\le T$. With $N=2C_2\log(MT)/d$, for every $y\ge2$,
$\displaystyle \left|\frac{S_\chi(y)}{y}-K_\chi-\epsilon_\chi(\log y-1)+\sum_{\rho\in Z_\chi}\frac{m_\chi(\rho)y^{\rho-1}}{\rho(\rho-1)}\right|
 \le\frac{1}{2\pi y}\left[
 \frac{2(\log y+22)ey}{H}+
 \frac{2H(N+4/(3\kappa))y^\sigma}{\sigma(1-\sigma)}+
 \frac{6(N+1)ey}{H^2}\right]$.
The list has the closed unit-window bound from *ex_box*, with its own analytic orders.

**Proof.** Count distinct zeros in the closed box of height $T+3$, say $N_0$ of them. Apply Lemma 4.10.23 to their real parts and absolute ordinates on the two specified intervals. The interval lengths are $\kappa/4$ and $1$, and each coordinate image has size at most $N_0$. Take $d=\kappa/(8(N_0+1))$. Ordinates above $T+3$ already have distance greater than $2$ from $H$. The box bound gives $N_0+1\le(4C_4+1)(T+1)\log(M(T+2))$, since $T+4\le2(T+1)$, $\log(M(T+5))\le2\log(M(T+2))$, and $(T+1)\log(M(T+2))\ge1$. In particular the strict contour filters include the stated closed inner box: equality with an edge would violate a positive gap. The unit-window bound follows by taking a subset of the box of height $T+1$ and keeping the orders. A zero on the lower bound $\Re\rho=9/10$ is harmless because $\sigma\ge19/20$.

For the actual contour put $c=1+1/\log y$. The left gap controls each zero used by the local estimate there: the disc in that estimate has radius $1/5$, so at $|t|\le H$ such a zero has $|\Im\rho|\le T+3$. On the horizontal edges use $\bigl||\Im\rho|-H\bigr|\le|\Im\rho-t|$ for $|t|=H$. The local contribution to the bound on these three edges is $N$, using $\log(M(T+3))\le2\log(MT)$. Restoring the principal term $1/(s-1)$ adds at most $4/(3\kappa)$ on the left, since $1-\sigma\ge3\kappa/4$, and at most $1$ on the horizontal edges, since $H\ge2$.

Now integrate $D_\chi(s)y^s/(s(s-1))$ counterclockwise around $[\sigma,c]\times[-H,H]$. At each zero the residue is $-m_\chi(\rho)y^\rho/(\rho(\rho-1))$. At $1$, the regular term $K_\chi$ times the kernel contributes $yK_\chi$, and the principal pole contributes $\epsilon_\chi$ times the derivative of $y^s/s$ at $1$, namely $\epsilon_\chi y(\log y-1)$. The point $0$ is outside the rectangle. Subtract the residue identity from the full right-line inversion. The two right tails have total integral norm at most $2(\log y+22)ey/H$, integrating $1/t^2$ and using $y^c=ey$. On the left, $|s(s-1)|\ge\sigma(1-\sigma)$ and the edge length is $2H$. On each horizontal side the denominator has norm at least $H^2$, the power has modulus at most $ey$, and the span is at most $3$ because $\log y\ge1/2$. Division by $2\pi y$ gives all three terms. This is the contour step in *exm_core*. It uses a finite residue sum with each distinct zero entered once at its analytic order. [A2, PNTExplPick.lean:43–110 and PNTExplMainB.lean:31–149](../sources/SOURCES.md#chapter-4-41011-finite-height-contours-and-weighted-zero-sums)

#### The weight from the sharp formula

The sharp formula of §4.10.6 uses the same list at $y$ and $(1+\alpha)y$, where $0<\alpha\le1/2$ is an arithmetic differencing parameter independent of the contour gap $d$. The finite sum can be moved through the interval integral: for each $\rho$, the difference of $u^{\rho-1}/(\rho(\rho-1))$ at the two points equals $\int_y^{(1+\alpha)y}u^{\rho-2}/\rho\,du$. Every summand is continuous on that positive real interval, so finite linearity applies. In particular the weight after removing the exceptional main term is governed by $y^{\Re\rho-1}$. Indeed $|y^\rho/\rho|\le2y\,y^{\Re\rho-1}$ for $\Re\rho\ge1/2$. If the normalized smoothed errors are bounded by $E$ at both endpoints, the inherited differencing bound for the sharp residual is $4yE/\alpha+20\alpha y\sum m_\chi(\rho)y^{\Re\rho-1}+4(\alpha y+1)\log(2y)$. This error uses full multiplicities. The exceptional main term is subtracted in the later zero-sum estimate, not from the unit-window count or the differencing error. [A2, PNTSharp.lean:69–156 and PNTBAsm.lean:38–81](../sources/SOURCES.md#chapter-4-41011-finite-height-contours-and-weighted-zero-sums)

#### From local counts to the weighted sum

**Lemma 4.10.25 (separated samples and total mass) [Lean, read].** Suppose a finite family of lists $V_\chi$, with nonnegative weights $m_\chi$, has the following two properties. Each closed unit window centred at a point of its own list has mass at most $K$. Every sample of distinct pairs $(\chi,\rho)$ in which same-character ordinates differ by at least $1$ has cardinality at most $R$. Then the total mass is at most $2RK$.

**Proof.** For each $\chi$, partition by the integer $k=\lfloor\Im\rho\rfloor$ and choose a representative of each nonempty cell. All points in that cell are within distance $1$ in ordinate of its representative. The mass bound at the representative therefore pays for the entire cell. Among the even cells, and separately among the odd cells, same-character representatives are separated: if $k'\ge k+2$, the first ordinate is strictly less than $k+1$ and the second is at least $k+2$. The map from occupied cells labelled by character to pairs of character and representative is injective, because taking the floor recovers the cell. Thus there are at most $R$ cells of each parity, across all characters. Summing the cell masses proves the result. Parity is needed because adjacent cells can contain ordinates arbitrarily close to one another. A bound on distinct points alone cannot control mass: one point of order $m$ has separated cardinality one for every $m$. [A2, PNTZSum.lean:112–238,441–486](../sources/SOURCES.md#chapter-4-41011-finite-height-contours-and-weighted-zero-sums)

<a id="p13-layered-weighted-zero-bound"></a>

**Theorem 4.10.26 (conditional finite-height weighted estimate).** Set $8\mid M$, $M>0$, $A_1\ge1$, $T=M^{A_1}$, $\ell=\log M$, $L=\log(M(T+3))$, and $Y=\log y$. Use Theorem 4.10.24 for each character, with common $\kappa\le1/20$ and individual edges. Let $w=L(1-\Re\rho)$ and $C_1=C_4$, or any larger common window constant. Assume these two further inputs.

- At height $T+3$, any separated sample of pairs with $1/2\le\Re\rho\le1$ and $w\le v$ has cardinality at most $C e^{av} L^B$, where $C\ge1$, $a\ge1$, $B\ge0$.
- A zero-free region with $0<c_Z\le1/20$ leaves at most one exceptional pair among all characters in $\Re\rho\ge1-c_Z/\log(M(|\Im\rho|+2))$. That pair, if present, has a simple real zero. The archive's selection $e=\mathrm{eOf}(M)$ chooses that pair whenever it exists. If the narrow region contains no such pair, $e$ chooses a fallback exceptional pair if one exists and is empty otherwise. Write $e_\chi(\rho)=\mathrm{excW}(e,\chi,\rho)$ for the indicator of the selected pair. For every selected zero outside the region assume $w\ge c_2\log(1/\theta)$, with $c_2>0$ and $0<\theta\le1$.

Put $c=c_Z/(4(A_1+2))$ and $K_0=(A_1+2)(a+1+2/c_2)+(B+1)/c$. If $Y\ge K_0\ell\log(\ell+2)$, then
$\displaystyle\sum_\chi\sum_{\rho\in Z_\chi}(m_\chi(\rho)-e_\chi(\rho))y^{\Re\rho-1}\le 4C_1 C e^a(A_1+2)^{B+1}\theta e^{-cY/\ell}$.
If the narrow-region exceptional pair belongs to the selected list, its coefficient cancels exactly.

**Proof.** For zeros outside the region, $w\ge c_Z$ because $|\Im\rho|<H\le T+1$. All selected zeros satisfy $\Re\rho\in(1-\kappa,1)$, so $w\le L$. The narrow-region contribution vanishes by simplicity. Outside the region, dropping the indicator subtraction can only increase the sum. In the remaining list, use layers $j<w\le j+1$ for $0\le j<\lceil L\rceil$. This assigns integer values of $w$ to the preceding layer, exactly the convention $\lceil w\rceil-1$. In layer $j$ the window bound at a representative is at most $C_1 L$. Apply the separated density bound at $v=j+1$, then Lemma 4.10.25. The layer mass is at most $2C_1 C e^{a(j+1)}L^{B+1}$.

For the decay of each term, put $g=\log(\ell+2)$, $r=2/c_2$, $s=4(B+1)/c_Z$, and $\mu=Y/((A_1+2)\ell)$. Then $L\le(A_1+2)\ell$, $\mu\ge(a+1+r+s)g$ and $g\ge 2\log 2>4/3$. The following three inequalities use at most three quarters of $w\mu$.
$(a+\log2)j\le(3/4)wg(a+1)$, $\log(1/\theta)\le(3/4)wgr$, and $(B+1)g\le(3/4)wgs$.
The first follows from $j<w$ and $(3/4)g(a+1)\ge a+1>a+\log 2$ for $a\ge1$. The second uses $wr\ge2\log(1/\theta)$ and the third uses $ws\ge4(B+1)$. The last quarter gives $w\mu/4\ge cY/\ell$. Adding and exponentiating, using $\log L\le\log(A_1+2)+g$ and $wY/L\ge w\mu$, gives
$L^{B+1}e^{-wY/L}\le(A_1+2)^{B+1}e^{-(a+\log2)j}\theta e^{-cY/\ell}$.
Multiply by the layer mass divided by $L^{B+1}$ and sum. The remaining finite geometric series is at most $2$. The archive permits the slightly larger $e^{a+a c_Z/2}$ in place of $e^a$. This is the normalized density and repulsion step of *zeroSum_core*. [A2, PNTZSum.lean:13–110,240–572](../sources/SOURCES.md#chapter-4-41011-finite-height-contours-and-weighted-zero-sums)

#### How the archive supplies the two estimates

On the repulsion side, *dhl_core* uses the Cauchy package at radius $12/25$ around $26/25+it$, with ratio bound $KX^2$ for $X=M(|t|+2)$. The zero disc is closed of radius $4/25$ and the evaluation disc has radius $1/25$. The count starts with $\log(KX^2)/\log2$, while the $k$th normalized derivative error starts with $72\log(KX^2)/(12/25)$ times $25^k$. Since $K\ge1$ and $\log X\ge1$, $\log(KX^2)\le(\log K+2)\log X$. Using $\log 2\ge1/2$ bounds both costs by the common constant $150(\log K+2)$, with the factor $25^k$ on the derivative error. For the Cauchy estimate write the regular part as $G=f'/f-\sum_\rho m(\rho)/(s-\rho)$. The supplied bound is $72\log(KX^2)/(12/25)$ on the open disc of radius $(12/25)/6$ after filling in the removable values. Cauchy's estimate on radius $(12/25)/12$ about the evaluation point gives the same bound times $k!25^k$ for $G^{(k)}$. The estimate at the edge of the evaluation disc follows by taking smaller radii and passing to the limit. Applying $(-1)^k/k!$ to the negative logarithmic derivative cancels the $k!$ and leaves the zero sum with denominators $(s-\rho)^{k+1}$. This explains the derivative error used by the four-disc argument.

The character split in *deuring_heilbronn_local* takes $K=\max(10400,52C_P)$ from the inherited growth witness $C_P$. On the principal branch the center lower bound for the regularized function is $(1/25)(1/26)$ and its value at $1$ is the nonzero product $\prod_{p\mid M}(1-1/p)$. Differentiating its log derivative subtracts exactly $1/(s-1)^{k+1}$ in the normalized formula. On the nonprincipal branch the center bound is $1/26$ and there is no principal term. On the growth disc, $\Re z\ge14/25>1/2$ and $1+|z|\le2(|t|+2)$. Thus the principal growth bound supplies $16M(|t|+2)^2\le KX^2/650$, and the nonprincipal one supplies $2C_P X\le KX^2/26$. Both bounds are at most $KX^2$ times the corresponding central value in modulus. This closes the hypotheses of *dhl_core*. The consumer *deuring_heilbronn_inequality* requests these discs for $1,\chi_1,\chi,\chi\chi_1$ at ordinates $0,0,\Im\rho,\Im\rho$. It bounds shifted reciprocal power sums by adding the four local errors and removes the exceptional displacement from the prescribed multisets. The Turán completion supplies the named input `DeuringHeilbronnMB` with loss exponent $3$. The §4.10.12 draft treats that completion. Section 4.10.13 gives the prime-moment producer it uses. [Turán source note](../sources/SOURCES.md#chapter-4-41012-the-turan-finish) In contrast, the unit-window weights in Theorem 4.10.26 come from *smoothed_explicit_formula* and *ex_box*. The local DH package supplies the repulsion parameter, not that unit-window bound. [A2, PNTDHLocalB.lean:27–128, PNTDHLocal.lean:16–180, PNTDHIneqF.lean:12–95 and PNTDHB.lean:13–14](../sources/SOURCES.md#chapter-4-41011-finite-height-contours-and-weighted-zero-sums)

<a id="p13-zero-sum-lossy"></a>

Here is the last constant conversion in *zero_sum_bound_lossy*. Write the lossy repulsion constants as $c_0,c_1,c_2>0$ and the logarithmic loss as the integer $n\ge0$. Choose $\kappa=\min(c_0,1/20)$ and $\eta_0=\min(c_Z/2,c_1/(A_1+2))$. Use the progression estimate's $\eta=\mathrm{etaOf}(M)$. It equals $1$ if $e=\mathrm{eOf}(M)$ is empty and $\min(1,(1-\beta_1)\ell)$ if $e$ selects a real zero $\beta_1$. If $\eta_0\le\eta L^n$, take $\theta=1$. Otherwise there must be an exceptional pair and $u=1-\beta_1>0$ satisfies $u\ell L^n<\eta_0$. Since $L\ge1$, we have $u\ell<\eta_0\le c_Z/2$. Since $\log(2M)=\ell+\log 2<2\ell$, it follows that $u<c_Z/\log(2M)$. Thus $\beta_1$ lies in the narrow region, and every selected zero outside it differs from the exceptional pair. Also $uL<c_1$ and $uL^n<c_1$, by $L\le(A_1+2)\ell$, $\eta_0\le c_1/(A_1+2)$ and $\ell\ge2$. Take $\theta=uL^n/c_1<1$. The lossy repulsion input at height $T+3$ says precisely $w\ge c_2\log(c_1/(uL^n))$ at every selected zero outside the region. Also $\eta_0\theta\le \eta L^n$ by $\eta_0\le c_1$ and $u\le u\ell$ in this branch. This gives the required $\theta$ in either case. If $Y\ge(K_0+2n/c)\ell\log(\ell+2)$, then $\ell^n e^{-(c/2)Y/\ell}\le1$ by taking logarithms. Substitute $\theta\le \eta (A_1+2)^n\ell^n/\eta_0$ in the archive version of Theorem 4.10.26 and use half the exponential to absorb $\ell^n$. The resulting bound is $A\,\eta\,\exp(-(c/2)Y/\ell)$ with $A=4C_1 C e^{a+a c_Z/2}(A_1+2)^{B+1+n}/\eta_0$. The archive allows any real window constant $C_1$ and uses $|C_1|$ in this formula. The strip width $\kappa$ is chosen first. Once $C_1$ and $A_1$ are given, $c/2$, $A$ and the threshold $K_0+2n/c$ are fixed before the modulus, lists and $y$. The far-range consumer chooses $A_1=12$, uses the same finite lists and analytic orders for the sharp formula and the weighted estimate, and pays at most $22y$ times the weighted sum after combining the norm bound $2y$ per unit of weight with the differencing coefficient $20\alpha y$. The exceptional pair contributes a separate term, including the case where its zero lies left of the contour. The consumer combines these with the numerical bound of §4.10.5. [A2, PNTZSumL.lean:12–193 and PNTBAsm.lean:15–81](../sources/SOURCES.md#chapter-4-41011-finite-height-contours-and-weighted-zero-sums)

#### Boundary and special-point conventions

The contour identity in Theorem 4.10.24 requires separated edges. A prescribed edge through a zero fails this condition. A logarithmic derivative with a zero of order $m$ has a simple pole of residue $-m$ after the minus sign; its norm on a nearby edge can grow like $m/d$. Changing only a value at the pole does not remove this blowup. For the nominal closed truncation, choose an admissible $H\ge T$ and keep zeros at $T$. If an exact cutoff at a boundary zero is required in the sum, use a displaced contour and transfer every crossed residue explicitly. For a strict cutoff at $T$, subtract the selected terms with $T\le|\Im\rho|<H$ from the sum, adding their absolute sum to the residual budget when only an upper bound for their contribution is available. For a closed cutoff, use $T<|\Im\rho|<H$ for that correction. A boundary zero on a vertical edge is treated by transporting its full residue as the edge moves. The theorem uses an ordinary contour integral. A principal-value or indented contour is a different statement and would need its own prescription and estimates.

The totalized quotient at a zero in Lean, where division by zero returns zero, is a point value distinct from the meromorphic expression around it. At $1$ use the analytic value of $f_\chi$ to compute $K_\chi$ and restore the principal pole separately. The kernel's factor $s$ has no effect here because $\sigma>0$. A fixed $y$ equal to a prime power belongs to the right-continuous convention for $\psi_\chi$, whereas the smoothing removes its endpoint contribution. The arithmetic differencing error accounts for that convention independently of the contour endpoints.

For *TailBox* the hypotheses are different: $\chi$ is nonprincipal, the zero-free box excludes zeros strictly to the right of $1-1/400$, and the left edge is to its right by a gap $d_B>0$. Every zero in the local disc used there is below the allowed height and is horizontally separated by at least $d_B$. Thus local terms are paid for by the mass bound times $1/d_B$, while the residue list for the Perron shift in §4.8.7 is empty. The inherited numerator budget is
$3(1+\log420/\log2)(1440/11+1/(d_B\log2))+32/\log2$,
multiplying $\log Q$. This uses the earlier growth witness and $C_R=22$. An empty residue list in that rectangle places no restriction on the lists of Theorem 4.10.24 in a wider or taller region. [A2, TailBox.lean:26–119](../sources/SOURCES.md#chapter-4-41011-finite-height-contours-and-weighted-zero-sums)

#### Reading boundary

Local R3 [Lean, read] applies to the coordinate selection, the floor and parity count, the finite layers and exponential absorption, and the local DH specialization and packaging described above. Theorems 4.10.24 and 4.10.26 are conditional textbook formulations with the hypotheses explicitly exposed. The archive uses closed box counts, strict contour membership and then a finite interchange of sums. The coordinate selection and rectangle estimate were already read in §4.10.7. The factor-of-two multiplicity proof and its use in the weighted sum are new to this chapter. The integral exchange above is the corresponding finite-linearity calculation. The full analytic density proof, the power-sum repulsion completion and the zero-free-region theorem remain named [Lean] inputs. The model calculations and boundary transfer are textbook deductions. Tao's *254A Notes 2*, Proposition 16 and Theorem 21, give the classical comparison of local counts and choosing a contour height before taking residues. [Tao 2014](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/#vnmef) · [Pinned sources](../sources/SOURCES.md#chapter-4-41011-finite-height-contours-and-weighted-zero-sums)

<a id="p13-turan-finish"></a>

### 4.10.12 The Turán finish of Deuring–Heilbronn repulsion

#### Motivation

Put the evaluation point directly to the right of a suspected zero $\rho$. In the local logarithmic derivative, that zero contributes a positive real reciprocal displacement. The other displacements carry complex phases, so even a large individual contribution may disappear in a particular derivative. A block of consecutive reciprocal powers gives the proof room to find a derivative where cancellation is incomplete. The exceptional zero makes the upper bound for that derivative small. Repulsion follows when the two bounds cannot coexist.

#### Two hand calculations [Expository]

**A. A whole part of a block can vanish.** Use the unit list $1,i,-1,-i$ and take $m=1$. Write $p_j$ for the sum of the $j$th powers. For $j=2$ the four terms are $1,-1,1,-1$. For $j=3$ they are $1,-i,-1,i$. For $j=4$ they are all $1$, and for $j=5$ the original list returns. Thus $(p_2,p_3,p_4,p_5)=(0,0,4,0)$. The Turán lower bound for this block is $(4/(1600\cdot5))^4=1/2000^4$. To see the rational-function mechanism, set $x=z\zeta$ for each entry $z$. The common denominator of $\sum_z x^2/(1-x)$ is $1-\zeta^4$. For $|\zeta|<1$ the numerator is $4\zeta^4$, by the power sums just computed and periodicity. The identity of rational functions holds elsewhere as well. For $|\zeta|>1$ each term has constant Laurent coefficient $-1$, so the sum has mean $-4$ on a circle there. The mean makes the extension of cancellation to the full block impossible.

**B. A retained real displacement can cancel even inside the reciprocal disc.** Take a positive scale $\eta$ and use the displacement list $2\eta$ four times, then $\eta(1-i),\eta(1+i),10\eta$. The normalized reciprocal list consists of $1/2$ four times, $(1+i)/2,(1-i)/2$, and $1/10$. The squared moduli of these three types are $1/4,1/2,1/100$, bounded by their real parts $1/2,1/2,1/10$. With a model cutoff $\varepsilon=1/8$, six entries remain and the first-moment mass of the full list is $S=31/10$, so $6\varepsilon^2=3/32\le S$. Take $m=2$, giving the interval $3$ through $8$. At $j=3$ the two complex cubes are $(-1+i)/4$ and $(-1-i)/4$. Their sum $-1/2$ cancels the four real cubes, leaving only $1/1000$ in the full sum. At $j=4$ the two complex fourth powers are each $-1/4$ and the four real fourth powers sum to $1/4$. The retained sum is $-1/4$, and the full sum is $-2499/10000$. The discarded term is $1/10000\le \varepsilon^2 S=31/640$. The maximum retained modulus is $1/\sqrt{2}$, so the fourth-power sum of the list divided by this maximum is $-1$. The bound on that normalized sum is $(6/(1600\cdot8))^6=(3/6400)^6$. The proof below uses its own smaller cutoff and chooses a block from the repulsion parameter. These are exact finite models.

#### Definitions and analytic inputs

Let $M$ be a natural modulus, $T$ a real height, and $L=\log(MT)$, $\ell=\log(3M)$. Use $L(s,\psi)$ for a Dirichlet $L$-function, and use $\mathbf{1}$ for the principal character modulo $M$. The predicate *IsLZero* requires $L(\rho,\psi)=0$ and, for the principal character, $\rho\ne1$. Write $\lambda=1-\beta_1$, $\delta=1-\Re\rho$, and $\gamma=\Im\rho$. For an evaluation scale $\eta>0$ define $s_t=1+\eta+it$. Set $D_j(\psi;s)=(-1)^{j-1}(-L'/L)^{(j-1)}(s)/(j-1)!$ for integers $j\ge1$ and $P_j=\Re(D_j(\mathbf{1};s_0)+D_j(\chi_1;s_0))$. The $\eta$ here is an evaluation scale. The zero-sum consumer's *etaOf* is a separate quantity.

We use the disc formula of §4.10.11 in the following form. There is one $C_L>0$ for every natural $M\ge3$, every character $\psi$ modulo $M$, and every real $t$. The zero list contains exactly the *IsLZero* points in the closed disc of radius $4/25$ about $26/25+it$, with positive integer weights as in *DHLocal*. Its zeros have real part below $1$. With those weights fixed, for all $j\ge1$ and all $s$ in the closed concentric disc of radius $1/25$ with $\Re s>1$, the normalized derivative equals the principal pole term minus the reciprocal power sum, up to an error of modulus at most $C_L\log(M(|t|+2))25^{j-1}$. The preceding section gives the disc Cauchy estimate and uses repulsion in the weighted zero sum. [§4.10.11](#41011-finite-height-contours-and-weighted-zero-sums)

We also use two uniform analytic inputs. The zero-free region has some $c_Z>0$ and at most one pair (character, zero) in $\Re z\ge 1-c_Z/\log(M(|\Im z|+2))$ at a given modulus. Here $c_Z$ is the witness in *region_gap*, which may differ from the narrowed constant in *eOf*. The exceptional-zero lower bound at exponent $1/2$ supplies $c_S>0$ with $\lambda\ge c_S/\sqrt M$ for the real zero of any nonprincipal $\chi_1$ with $\chi_1^2=\mathbf{1}$ at issue here. These inputs retain their previous reading levels. [A2, PNTDHSt.lean:34, PNTDHFinish.lean:22 and SiegelWalfiszAPOfSiegelLower.lean:32](../sources/SOURCES.md#chapter-4-41012-the-turan-finish)

#### Lemma 4.10.27. Turán's finite block [Lean, read]

For every $n\ge1$ and $m\ge0$ in the natural numbers and every complex list $z_1,\ldots,z_n$ with $\max_i|z_i|=1$, there is an integer $m+1\le j\le m+n$ such that $|\sum_i z_i^j|\ge (n/(1600(m+n)))^n$. Repetition and zero entries are allowed.

**Proof.** First, for any list of $n$ real points $t_i$, any real $c$ and $r>0$, there is $q\in[c-r,c+r]$ with $\prod_i|q-t_i|\ge (r/25)^n$. Induct on $n$, with empty product $1$. The open intervals of radius $2r/5$ about $c-4r/5,c,c+4r/5$ are disjoint. Select a center whose interval contains $k\le n/3$ indices. Apply induction to these points on the interval of radius $r/5$ about that center. The new point lies in the original interval and its distances to the other $n-k$ points are at least $r/5$. Thus the product is at least $(r/125)^k(r/5)^{n-k}=(r/25)^n5^{n-2k}\ge(r/25)^n$.

Write $b=m+n$, $r=n/(6b)$, and apply the distance bound to $t_i=|z_i|$ about $1-2r$. It gives $q\in[1-3r,1-r]$ and $P=\prod_i|q-|z_i||\ge(r/25)^n$. Put $h=\lfloor b/n\rfloor$, so $m+1\le hn\le b$. Bernoulli's inequality gives $q^h\ge1-3rh\ge1/2$, hence $q^{m+1}P\ge(n/(300b))^n$.

For the generating function $F(v)=\sum_i(z_i v)^{m+1}/(1-z_i v)$ put $Q(v)=\prod_i(1-z_i v)=\sum_d q_dv^d$. The polynomial $Q(v)F(v)/v^{m+1}$ has degree at most $n-1$. Its coefficient at degree $d<n$ is $\sum_{a=0}^d q_a p_{m+1+d-a}$, as seen by expanding at $v=0$. Also $\sum_a|q_a|\le\prod_i(1+|z_i|)\le2^n$. If the block has $|p_j|\le B=(n/(1600b))^n$ throughout, then on $|v|=q^{-1}$ the numerator has modulus at most $q^{-m-1-n}n2^nB$. The reverse triangle inequality gives $|Q(v)|\ge q^{-n}P$. Thus $|F(v)|\le n2^nB/(q^{m+1}P)\le n(3/8)^n<1$. The last strict inequality follows from $(8/3)^n\ge1+5n/3>n$.

On this circle write $x=z_i v$. For $|x|<1$, $x^{m+1}/(1-x)$ expands in strictly positive powers of $x$ and has mean zero. For $|x|>1$ it expands as $-\sum_{d\ge0}x^{m-d}$ and has mean $-1$. The expansions converge uniformly on the circle. Equivalently, averaging over the $H$th roots of unity for $H>m+1$ gives $y_i^H/(1-y_i^H)$ for $y_i=z_i/q$, and taking $H\to\infty$ gives the same mean. At least one $|z_i|=1>q$, so the mean has modulus at least $1$, a contradiction. [A2, Turan2Main.lean:11,29, ExistsFarFromPoints.lean:20,48,92,119, HDSucc.lean:28, RootNorm.lean:30,84,112 and TuranPowerSumBound.lean:12](../sources/SOURCES.md#chapter-4-41012-the-turan-finish)

#### Lemma 4.10.28. The surviving displacement and its upper bounds [Lean, read]

Assume $M\ge3$, $T\ge2$, $\chi_1^2=\mathbf{1}$, $\chi_1\ne\mathbf{1}$, $L(\beta_1,\chi_1)=0$, $19/20\le\beta_1<1$, and *IsLZero* for $\chi,\rho$ with $\Re\rho\ge22/25$, $|\gamma|\le T$, and $(\chi,\rho)\ne(\chi_1,\beta_1)$. For each real $0<\eta\le2/25$ there is one finite displacement list $(w_i)_{i=1}^N$ with $\Re w_i\ge\eta$ and some $w_i=\eta+\delta$. With $C_F=8C_L+1$, this list satisfies
- $\Re\sum_i w_i^{-1}\le 2\lambda/\eta^2+25C_FL$,
- $|\sum_i w_i^{-j}|\le P_j+2j\lambda/\eta^{j+1}+C_FL25^j$ for every integer $j\ge1$.

**Proof.** In the absolutely convergent half-plane, $D_j$ has coefficients $\psi(n)\Lambda(n)(\log n)^{j-1}/(j-1)!$. On units modulo $M$, $1+\chi_1(n)$ is either $0$ or $2$ and $|\chi(n)n^{-i\gamma}|=1$. Off the units all character coefficients in this comparison vanish. Termwise domination and absolute convergence give $|D_j(\chi;s_\gamma)+D_j(\chi\chi_1;s_\gamma)|\le P_j$. In particular the real part of the sum of all four derivatives at $(s_0,s_0,s_\gamma,s_\gamma)$ is nonnegative. The modulus domination gives the all-powers bound and its real-part consequence gives the first-moment bound.

Apply the four disc expansions at these ordinates in character order $\mathbf{1},\chi_1,\chi,\chi\chi_1$. At zero ordinate delete one copy of $s_0-\beta_1$ from the second list. At $\gamma$ delete one copy of $s_\gamma-\beta_1$ in the list for $\chi_1$ when that character occurs and $\beta_1$ belongs to the disc. The four lists count copies, including copies with the same displacement. In the shifted lists the tested zero lies in the disc since $22/25\le\Re\rho<1$. Its displacement is real because the height is matched. The excluded pair condition ensures it survives the deletion in its own list. The shifted lists together form $w$. Every real part exceeds or equals $\eta$ by the real-part condition on disc zeros.

At ordinate $0$ the principal pole pairs with the erased reciprocal. For $\Re a,\Re b\ge\eta$ and $b-a=\lambda$ the identity for the difference of $j$th powers, applied to $a^{-1},b^{-1}$, bounds $|a^{-j}-b^{-j}|\le j\lambda/\eta^{j+1}$. Use it for $a=s_0-1,b=s_0-\beta_1$ and for the corresponding shifted pair. In the shifted discs there is at most one principal pole, and its partner character is then $\chi_1$. If the partner zero is outside the disc, the horizontal distance from its center is at most $9/100$. The inequality $(9/100)^2+(1/8)^2<(4/25)^2$ forces $|\gamma|\ge1/8$. The unpaired shifted pole then costs at most $8^j$. If neither shifted character is principal, both of those pole and deletion terms vanish. Each disc error is at most $2C_LL25^{j-1}$, since $|\gamma|+2\le 2T$ and $MT\ge6$. The four-disc real-part inequality follows by moving the derivative sum to the other side and using its nonnegative real part. At $j=1$ the two remaining unshifted zero lists have nonnegative real reciprocal sums and can be dropped. For the all-powers modulus use just the shifted expansions and the modulus domination. In both estimates $8^j$ is absorbed by $L25^j$, since $L\ge1$. [A2, PNTDHDom.lean:14,50,108, PNTDHPos.lean:149, PNTDHIneqF.lean:12 and PNTDHIneqFA.lean:9,46,97,109,176](../sources/SOURCES.md#chapter-4-41012-the-turan-finish)

The prime-sum supply *DHPrime* gives one $C_P>0$ before choosing $M\ge3$, $\chi_1$, $\beta_1$, $1<\sigma\le2$, or the integer derivative order $k\ge0$. Its character and real zero hypotheses are $\chi_1^2=\mathbf{1}$, $\chi_1\ne\mathbf{1}$, $L(\beta_1,\chi_1)=0$ and $1-1/\ell\le\beta_1<1$. At $\sigma=1+\eta$ and $k=j-1$ it gives
$P_j\le C_P\lambda\ell^2(j+1)^2/\eta^{j+1}+(C_P\ell)^j/(j-1)!+C_P(j+1)\ell^2/(M\eta^j)$.
The direct packaging uses a cutoff $v_0=\lceil8\log M\rceil$ in $\log n$. The small part is paid by Mertens' bound and $v_0\le9\ell$. In the large part the divisor sum of $\chi_1$ is nonnegative and dominates $(1+\chi_1(n))\Lambda(n)/(2\log n)$ for $n>1$. Indeed the divisor sum is multiplicative, its prime-power factors are $1$ at bad primes, alternating $0,1$ at negative primes, and $a+1$ at a positive prime power of exponent $a$. On the logarithmic block $(e^v,e^{v+1}]$ the hyperbola bound for its mass weighted by $1/n$ is $|L(1,\chi_1)|+C_H M(v+1)e^{-v/2}$. The large-part summation in *dhpr_large* gives the two contributions bounded by $4e^2|L(1,\chi_1)|(k+2)(k+1)k!/\eta^{k+2}$ and $40e C_HM e^{-v_0/4}(k+1)k!/\eta^{k+1}$ before division by $k!$. The hyperbola and block moment estimates are the inputs from §4.10.13. [Prime-moment proof](#p13-dh-prime) The $L$-value bound $|L(1,\chi_1)|\le C_D\lambda\ell^2$ supplies **two** logarithms, while $M e^{-v_0/4}\le M^{-1}$ pays for the tail. To see the two logarithms in the direct supply, take a real $\sigma\in[1-1/\ell,1]$. On the circle of radius $1/(2\ell)$ about $\sigma$ the real part is at least $1-3/(2\ell)\ge1/4$ and the modulus is at most $2$. In the inherited Abel continuation, the sum through $M$ has modulus at most $e^{3/2}(1+\ell)$ by $n^{1-\Re s}\le e^{3/2}$ and the harmonic sum estimate. The boundary term is at most $e^{3/2}$ and the tail at most $8e^{3/2}$ by the character partial-sum bound $M+1$ and $|s|/\Re s\le8$. This is below the archive's $38e^{3/2}\ell$. Apply the usual first-derivative Cauchy estimate on that circle to obtain $|L'(\sigma,\chi_1)|\le76e^{3/2}\ell^2$. Integrating along $[\beta_1,1]$ gives the claimed $L$-value inequality since $L(\beta_1,\chi_1)=0$. The two logarithms arise from the harmonic sum and the inverse radius. With Mertens witness $C_{\rm Mer}$ the archive takes $C_P=\max(30C_D,18C_{\rm Mer}+9,110C_H)$. [A2, DHFinish2Of.lean:38,44, PNTDHPrime.lean:12,55,109,151 and PNTDHPrimeA.lean:191 and ExceptionalZeroBounds/LDerivNearOne.lean:101,128](../sources/SOURCES.md#chapter-4-41012-the-turan-finish)

#### Theorem 4.10.29. Finite-height repulsion with logarithmic loss [Lean, read]

Assume the named analytic supplies above, including *DHPrime*. There are positive real constants $c_0,c_1,c_2$ and an integer $B=3$, chosen before all the following data. For every natural $M\ge3$, all characters $\chi_1,\chi$ modulo $M$, real $\beta_1,T$ with $T\ge2$, and complex $\rho$, suppose
- $\chi_1^2=\mathbf{1}$, $\chi_1\ne\mathbf{1}$ and $L(\beta_1,\chi_1)=0$,
- $1-c_1/\log(MT)<\beta_1<1$,
- *IsLZero* holds for $\chi,\rho$, $\Re\rho\ge1-c_0$, $|\Im\rho|\le T$, and $(\chi,\rho)\ne(\chi_1,\beta_1)$.

Then $1-\Re\rho\ge c_2\log(c_1/((1-\beta_1)\log(MT)^B))/\log(MT)$.

**Proof.** Keep the archive's general Turán constants $C_T>0$, $a\ge1$ an integer, with the interval ending at $m+an$ and exponent $an$ in Lemma 4.10.27. Their actual witnesses are $(1600,1)$. Use the constants in the table below. In particular $R>16$, $\varepsilon=1/R$ and $2\tau\log R=1$.

Since $\log(2M)\le L$ and $c_1\le c_Z/4$, the exceptional zero is in the narrow region of the uniqueness input. The pair inequality puts the tested zero outside it. Comparing $\log(M(|\gamma|+2))\le2L$ gives $\delta\ge c_Z/(2L)>0$. Choose $\eta=\delta\le c_0$. Then $\Re\rho\ge22/25$, $\eta\le2/25$ and $\beta_1\ge19/20$, as $c_0\le1/25$, $L\ge1$, and $c_1\le1/20$. Since $3M\le(MT)^2$ we have $\ell\le2L$ and $c_1/L\le1/\ell$. This checks both lemmas' real-zero thresholds and the prime-sum abscissa $1<1+\eta\le2$. Also
$\ell^2/M\le32/\sqrt M\le32\lambda/c_S$.
For the first inequality, $\log x\le (4/e)x^{1/4}$ by maximizing $\log x/x^{1/4}$ for $x>0$. At $x=3M$ the squared coefficient is $16\sqrt3/e^2<32$.

Put $K=\log(c_1/(\lambda L^3))$. Suppose $\eta L<c_2K$. The base gap and the third restriction on $c_2$ in the table imply $K>K_0$: if $K\le K_0$ then $c_2K\le c_Z/2$. In particular $K>0$, $\lambda L^3=c_1e^{-K}$ and $\lambda/\eta\le 2\lambda L/c_Z\le1/2$.

With the list from Lemma 4.10.28 put $u_i=\eta/w_i$. Then $|u_i|^2\le\Re u_i$ and some $u_i=1/2$. The first inequality follows by multiplying by $|w_i|^2$, and the second uses $w_i=2\eta$. Put $S=\sum_i\Re u_i$. From the first-moment bound and $25C_Fc_2\le\kappa$ we have $S\le2\lambda/\eta+25C_F\eta L\le1+\kappa K$. Retain only $|u_i|\ge\varepsilon$. If $n$ indices remain then $1\le n$ and $n\varepsilon^2\le S$. Divide the retained list by its maximum modulus, which is at least $1/2$. With $m=\lceil\tau K\rceil\ge1$, Turán supplies $m+1\le j\le m+an$, and undoing the division gives
$(1/2)^j(n/(C_T(m+n)))^{an}\le|\sum_i u_i^j|+\varepsilon^{j-2}S$.
In fact the discarded $j$th powers have total modulus at most $\varepsilon^{j-2}\sum_i|u_i|^2\le\varepsilon^{j-2}S$, using $j\ge2$.

The choices $\kappa=\tau\varepsilon^2/(a(D+1))$ and $D=\log\max(C_T,1)$ give $an\le a/\varepsilon^2+\tau K$ and $anD\le aD/\varepsilon^2+\tau K$. Hence $\tau K<j\le 2\tau K+j_0$. For the lower bound, $\log(1+m/n)\le m/n$ gives $(n/(C_T(m+n)))^{an}\ge e^{-am-anD}$. Since $m<j$ and $\tau K<j$, the normalized lower bound is at least $1/(E(R/8)^j)$. The upper end of the interval controls the exceptional term. Since $2\tau\log R=1$, it guarantees $e^{-K}\le R^{j_0}/R^j$. These two uses explain why one starts near $\tau K$ and budgets the length of the block by the retained mass.

Multiply the bounds of Lemma 4.10.28 and *DHPrime* by $\eta^j$. The five terms of the resulting upper bound for $|\sum_i u_i^j|$ pay as follows.

| Term after multiplication | Upper bound and reason |
|---|---|
| $C_P\lambda\ell^2(j+1)^2/\eta$ | $(8C_P/c_Z)(j+1)^2\lambda L^3$, from $\ell\le2L$ and $1/\eta\le2L/c_Z$ |
| $(C_P\ell\eta)^j/(j-1)!$ | $j/R^j$, from $j!\ge(j/e)^j$ and $e C_P\ell\eta R\le2e C_P c_2 R K\le\tau K<j$ |
| $C_P(j+1)\ell^2/M$ | $(32C_P/c_S)(j+1)^2\lambda L^3$, from the exceptional lower bound |
| $2j\lambda/\eta$ | $(4/c_Z)(j+1)^2\lambda L^3$, from the base gap and $L\ge1$ |
| $C_FL(25\eta)^j$ | $Rj/R^j$, from $25\eta\le1/R$ and $25C_F\eta L\le\kappa K<j$ |

The factorial bound follows by comparison of $\sum_{b=1}^j\log b$ with $\int_1^j\log x\thinspace dx$. The discarded tail is at most $R^2(j+1)^2/R^j$ because $S\le1+\kappa K\le1+j$. Using $\lambda L^3=c_1e^{-K}$ and the upper end of the block now gives
$1/(E(R/8)^j)\le G(j+1)^2/R^j$.
Consequently $8^j\le EG(j+1)^2$, yet $EG=\tau K_0<\tau K<j$ and $8^j\ge(j+1)^3$ since $2^j\ge j+1$. This contradiction proves the theorem. The first row of the budget produces $B=3$: the two logarithms of the $L(1,\chi_1)$ estimate are multiplied by the one logarithm used to bound $1/\eta$. The two ends of the Turán interval pay the decaying factorial and exponential terms at this scale. [A2, DeuringHeilbronnFinishTuran.lean:14, NormUSum.lean:20, UbTerms.lean:9,34,52,84, ExistsPowerSumLowerBound.lean:9,109,140,173 and TwentyFiveMulSmallConstant.lean:9](../sources/SOURCES.md#chapter-4-41012-the-turan-finish)

#### Constants and quantifiers

| Constant or variable | Choice and scope |
|---|---|
| $C_T,a$ | $1600,1$ before every $m\ge0$, $n\ge1$ and list of maximum modulus $1$ |
| $C_L,C_F$ | $C_L$ from the uniform disc expansion, $C_F=8C_L+1$ before all $M,T,\chi_1,\chi,\beta_1,\rho,\eta$ |
| $C_P$ | Uniform *DHPrime* constant before all $M,\chi_1,\beta_1,\sigma,k$ in its stated ranges |
| $c_Z,c_S$ | Uniform uniqueness witness and exceptional lower-bound witness at exponent $1/2$ |
| $D,R,\varepsilon,\tau,\kappa$ | $D=\log\max(C_T,1)$, $R=16e^{a+1}$, $\varepsilon=R^{-1}$, $\tau=1/(2\log R)$, $\kappa=\tau\varepsilon^2/(a(D+1))$ |
| $c_0,c_1$ | $c_0=1/(25R)$, $c_1=\min(c_Z/4,1/20)$ |
| $E,j_0$ | $E=e^{aD/\varepsilon^2}$, $j_0=1+a/\varepsilon^2$ |
| $G,K_0$ | $G=(8C_P/c_Z+4/c_Z+32C_P/c_S)c_1R^{j_0}+1+R+R^2$, $K_0=EG/\tau$ |
| $c_2,B$ | $c_2=\min(\kappa/(25C_F),\tau/(2e C_P R),c_Z/(2(\lvert K_0\rvert+1)))$, $B=3$ |
| Data and displacements | One modulus instance with $M\ge3$, same-modulus characters, real $T\ge2$ and real $\beta_1$, complex $\rho$ as in the theorem. For a legal $\eta$, one list before every integer $j\ge1$. The real displacement is retained at $\eta=\delta$. |
| Block | Per tested zero in the contradiction branch, $m=\lceil\tau K\rceil$ and $n$ is the number of retained indices. The integer $j$ belongs to $[m+1,m+an]$. |

#### Remarks on the hypotheses and the consumer

**Deleting the dominant displacement.** The unit-modulus premise in Lemma 4.10.27 cannot be dropped, even for a nonzero list. For $n=1,m=0,z_1=1/3200$ the only allowed power is $1$, with modulus below $1/1600$. At the reciprocal-disc stage, any fixed $\varepsilon>0$ and any $0<t<\min(\varepsilon,1/2)$ give $u_1=t$, $w_1=\eta/t$ and $|u_1|^2\le\Re u_1$. The retained list is empty and $S=t$ can be arbitrarily small. This is failure of the lower-bound interface when the surviving large entry is deleted. The character domination is a separate hypothesis: with an order-four character taking value $i$ at a unit and $\chi=\mathbf{1}$, the scalar comparison $|1+i|\le\Re(1+i)$ fails. This explains the role of the quadratic condition in the termwise proof.

**Return to the progression estimate.** *PNTDHB* supplies *DeuringHeilbronnMB* with the constants above. *PNTFinal* feeds this witness and *LogDensityM* to *zero_sum_bound_lossy*. At the consumer's enlarged height the theorem applies to the same competing pairs used in the finite zero sum. At the wrapper height $M^{A_1}+3$ (with $A_1=12$ in the far-range call), the narrow-region test in §4.10.11 ensures that a selected fallback pair cannot be accidentally excluded from the out-of-region estimate. The wrapper takes $n=B=3$ in the absorption cost and delivers $A\thinspace \mathrm{etaOf}(M)e^{-(c/2)Y/\log M}$. This factor of *etaOf* is passed with the same zero lists to the far-range assembly of *PsiRel*. [A2, PNTDHBSt.lean:11, PNTDHB.lean:13, PNTFinal.lean:18, PNTZSumL.lean:78,129, PNTBAsm.lean:139](../sources/SOURCES.md#chapter-4-41012-the-turan-finish)

**Reading scope and attribution.** The unit-coefficient block, shifted domination, retained displacement and numerical contradiction are local proof-body readings. The prime-moment packaging uses named hyperbola, block-moment, Mertens and $L(1,\chi_1)$ supplies. Density, Siegel's lower bound and the analytic proof of region uniqueness stay at their inherited levels. The classical comparison is Thorner and Zaman's power-sum proof of repulsion for Hecke $L$-functions. The specific finite block, numerical constants and finite-height contract above are sourced to A2. The two finite models and the scope examples are textbook calculations. The mathematical text inherits the original same-source preliminary review within its stated conditional scope. [Pinned sources and classical comparison](../sources/SOURCES.md#chapter-4-41012-the-turan-finish)

### 4.10.13 Hyperbola splitting and prime moments for Deuring–Heilbronn

#### Motivation

The Turán completion in [§4.10.12](#p13-turan-finish) deduces finite-height Deuring–Heilbronn repulsion with logarithmic exponent $B=3$ from the prime-moment interface *DHPrime*. Why does the archive's local-disc proof require a prime-moment upper bound at all, and how does an exceptional zero $\beta_1$ of a quadratic character $\chi_1$ make that bound small?

In the quadratic case of the global zero expansion in Thorner and Zaman, the normalized derivative $D_j(\psi;s)=(-1)^{j-1}(-L'/L)^{(j-1)}(s)/(j-1)!$ is expanded over all nontrivial and trivial zeros at once; nonnegativity of $(1+\chi_1(n))\Lambda(n)$ then moves the entire prime series to the nonnegative left-hand side and leaves only pole differences on the right. The archive uses local disc expansions. The surviving-displacement lemma of [§4.10.12](#p13-turan-finish) applies the local Borel–Carathéodory disc expansion *DHLocal* of §4.10.11 on two shifted discs at height $\gamma$, leaving the real-axis prime moment $P_j=\Re(D_j(\mathbf{1};1+\eta)+D_j(\chi_1;1+\eta))$ on the right-hand side of the all-powers modulus inequality $|\sum_i w_i^{-j}|\le P_j+2j\lambda/\eta^{j+1}+C_FL25^j$. At $\eta=\delta=1-\Re\rho$, an uncancelled main pole of order $\eta^{-(j+1)}$ in $P_j$ would overwhelm the Turán lower bound; *DHPrime* must therefore multiply the leading $\eta^{-(j+1)}$ term by $\lambda=1-\beta_1$. Here $\eta=\sigma-1$ is the abscissa increment and $\ell=\log(3M)$ is the prime-moment logarithm. Section 4.10.11 uses $\eta=\mathrm{etaOf}(M)$ and $\ell=\log M$ for the weighted zero sum. The modulus $M$ is the same throughout. [Turán source note](../sources/SOURCES.md#chapter-4-41012-the-turan-finish)

The production proof accomplishes this in three stages, working entirely on the real segment $\sigma=1+\eta\in(1,2]$ with derivative index $k=j-1\ge0$:

1. **Arithmetic domination and logarithmic cutoff.** Set $v_0=\lceil 8\log M\rceil$. On the initial segment $1\le n\le\lfloor e^{v_0}\rfloor$, the factor $n^{-\sigma}\le n^{-1}$ and Mertens' bound $\sum_{n\le y}\Lambda(n)/n\le C_{\mathrm{Mer}}\log y$ pay $2C_{\mathrm{Mer}}v_0^{k+1}$ without mentioning $\beta_1$; in the Turán finish, division by $k!$ turns this finite prefix into an exponentially small factorial term. Above $\lfloor e^{v_0}\rfloor$, quadratic positivity $\chi_1^2=\mathbf{1}$ makes the Dirichlet convolution $r_{\chi_1}(n)=\Re\sum_{d\mid n}\chi_1(d)$ nonnegative at every integer and forces $\Lambda(n)\,\mathrm{dhprC}(\chi_1,n)\le 2(\log n)\,r_{\chi_1}(n)$, vanishing off prime powers and checked by parity on prime powers.
2. **Dirichlet's hyperbola method with overlap cancellation and differencing.** Write $c_F(\chi_1,N)=\sum_{n=1}^N (\sum_{d\mid n}\chi_1(d))/n=\sum_{ab\le N} a^{-1}\chi_1(b)/b$ and split at $U=\lfloor\sqrt N\rfloor$. On the first wing $1\le b\le U$, Euler–Mascheroni bracketing of the harmonic sum $H_{\lfloor N/b\rfloor}$ extracts $(\log N+\gamma)c_S(\chi_1,U)-c_T(\chi_1,U)$. The character tail then replaces $c_S(\chi_1,U)$ by $L(1,\chi_1)$ at a controlled cost. On the complementary wing $U<b\le\lfloor N/a\rfloor$, each active row equals $c_S(\chi_1,\lfloor N/a\rfloor)-c_S(\chi_1,U)$: **subtracting the overlap partial sum $c_S(\chi_1,U)$** cancels the convergent limit $L(1,\chi_1)$ row by row down to $O(M/U)$, so the entire second wing becomes $O(M(\log N+1)/\sqrt N)$. Differencing between $N_0=\lfloor y\rfloor$ and $N_1=\lfloor x\rfloor$ cancels $\gamma L(1,\chi_1)$ identically and controls $c_T(\chi_1,U_1)-c_T(\chi_1,U_0)$ by discrete Abel summation.
3. **Non-uniform integer blocks and split-rate moment aggregation.** Partitioning $(\lfloor e^{v_0}\rfloor,\lfloor e^V\rfloor]$ into the disjoint integer blocks $I_v=(\lfloor e^v\rfloor,\lfloor e^{v+1}\rfloor]$ freezes $(v+1)^{k+1}e^{-\eta v}$ on each block regardless of its integer length $\lfloor e^{v+1}\rfloor-\lfloor e^v\rfloor$. Summing the $|L(1,\chi_1)|$ main piece splits the decay rate as $\eta=(k+1)\delta+\delta$, absorbing $(v+1)^{k+1}$ into $(k+1)!$ at cost $\eta^{-(k+2)}$ and substituting $|L(1,\chi_1)|\le C_D\lambda\ell^2$. On the hyperbola remainder, $(v+1)e^{-v/2}$ already decays geometrically like $e^{-v/4}$, so factoring out $\sup_v (v+1)^{k+1}e^{-\eta v}\le e(k+1)k!/\eta^{k+1}$ saves one power of $(k+2)/\eta$ while $M e^{-v_0/4}\le M^{-1}$ pays the modulus factor.

#### Two hand calculations [Expository]

**A. Hyperbola boundary points, overlap subtraction, and differencing.** Take modulus $M=4$ and the nonprincipal quadratic character $\chi_{-4}$ defined by $\chi_{-4}(1)=1$, $\chi_{-4}(3)=-1$, and $\chi_{-4}(2m)=0$. Choose real endpoints $y=9$ and $x=31/2$, so $N_0=\lfloor y\rfloor=9$ with $U_0=\lfloor\sqrt 9\rfloor=3$ and $N_1=\lfloor x\rfloor=15$ with $U_1=\lfloor\sqrt{15}\rfloor=3$. Here $c_S(\chi_{-4},3)=1+0-1/3=2/3$, while $r_{\chi_{-4}}(n)=\sum_{d\mid n}\chi_{-4}(d)$ takes values $(1,1,0,1,2,0,0,1,1,2,0,0,2,0,0)$ for $n=1,\ldots,15$.

At $N_0=9$, three lattice pairs $(a,b)$ with $\chi_{-4}(b)\ne0$ sit directly on the hyperbola boundary $ab=9$: $(9,1)$ and the cut-line corner $(3,3)$ belong to Wing I ($1\le b\le 3$), contributing $+1/9$ and $-1/9$, whereas $(1,9)$ belongs to Wing II ($b>3$), contributing $+1/9$. At row $a=3$ of Wing II, $\lfloor 9/3\rfloor=3\le U_0$, so the half-open slice $(3,\lfloor 9/3\rfloor]$ is empty and the corner $(3,3)$ is counted exactly once. With $H_9=7129/2520$ and $H_3=11/6$, Wing I equals $1\cdot H_9+0\cdot H_4-(1/3)H_3=621/280$. The active rows of Wing II are $1\le a\le V_0=\lfloor 9/4\rfloor=2$: at $a=1$, $c_S(\chi_{-4},9)-c_S(\chi_{-4},3)=1/5-1/7+1/9=53/315$; at $a=2$, $c_S(\chi_{-4},4)-c_S(\chi_{-4},3)=0$. Adding the two disjoint wings gives $621/280+53/315=859/360=c_F(\chi_{-4},9)$. Equivalently, the unsubtracted two-wing sum $\sum_{b=1}^3 (\chi_{-4}(b)/b)H_{\lfloor 9/b\rfloor}+\sum_{a=1}^2 a^{-1}c_S(\chi_{-4},\lfloor 9/a\rfloor)=621/280+368/315=1219/360$ double-counts the $2\times 3$ overlap rectangle $\{1\le a\le 2,\ 1\le b\le 3\}$ of exact weight $H_2 c_S(\chi_{-4},3)=(3/2)(2/3)=1$, and $1219/360-1=859/360$.

At $N_1=15$, four odd-divisor pairs sit on the hyperbola boundary $ab=15$: $(15,1)$ ($+1/15$) and $(5,3)$ ($-1/15$) lie in Wing I ($1\le b\le 3$), while $(3,5)$ ($+1/15$, on row $a=3$ where $\lfloor 15/3\rfloor=5>3$) and $(1,15)$ ($-1/15$, on row $a=1$) lie in Wing II ($b>3$). With $H_{15}=1195757/360360$ and $H_5=137/60$, Wing I equals $H_{15}-(1/3)H_5=102387/40040$. The active Wing II rows are $1\le a\le V_1=\lfloor 15/4\rfloor=3$, giving $(c_S(\chi_{-4},15)-2/3)+(1/2)(c_S(\chi_{-4},7)-2/3)+(1/3)(c_S(\chi_{-4},5)-2/3)=7303/45045+3/140+1/15=8236/45045$. Their sum is $102387/40040+8236/45045=12823/4680=c_F(\chi_{-4},15)$, which matches the unsubtracted two-wing sum $6181/1560$ minus the $3\times 3$ overlap rectangle $H_3 c_S(\chi_{-4},3)=(11/6)(2/3)=11/9$. Differencing yields
$\sum_{n\in(9,15]} r_{\chi_{-4}}(n)/n = c_F(\chi_{-4},15)-c_F(\chi_{-4},9) = 12823/4680 - 859/360 = 23/65$,
matching the two nonzero terms $r_{\chi_{-4}}(10)/10+r_{\chi_{-4}}(13)/13=2/10+2/13=23/65$. This finite rational calculation verifies the exact lattice partition, boundary assignment, and overlap subtraction; it does not substitute for the analytic Euler–Mascheroni and Abel bounds behind $C_H=400$.

**B. Non-uniform integer logarithmic blocks and prime-power domination.** Take modulus $M=7$ and the quadratic character $\chi_{-7}$ with $\chi_{-7}(n)=+1$ for $n\equiv 1,2,4\pmod 7$, $\chi_{-7}(n)=-1$ for $n\equiv 3,5,6\pmod 7$, and $\chi_{-7}(7m)=0$. With model cutoffs $v_0=1$ and $V=3$, the integer floor endpoints $(\lfloor e^0\rfloor,\lfloor e^1\rfloor,\lfloor e^2\rfloor,\lfloor e^3\rfloor)=(1,2,7,20)$ split $(0,20]$ into three disjoint intervals of **non-uniform integer lengths** $2$, $5$, and $13$: $I_{\mathrm{small}}=(0,2]=\{1,2\}$, $I_1=(2,7]=\{3,4,5,6,7\}$, and $I_2=(7,20]=\{8,\ldots,20\}$, with $2+5+13=20$.

Every branch of the coefficient inequality $\Lambda(n)\,\mathrm{dhprC}(\chi_{-7},n)\le 2(\log n)\,r_{\chi_{-7}}(n)$ appears in $(0,20]$:
- On $I_{\mathrm{small}}$ (length $2$), $n=2$ is split ($\chi_{-7}(2)=+1$), so $\mathrm{dhprC}(\chi_{-7},2)=2$ and the prefix sum at $k=1,\sigma=3/2$ is $(\log 2)^2/\sqrt 2>0$.
- On $I_1$ (length $5$), $n=4=2^2$ has $\mathrm{dhprC}(\chi_{-7},4)=2$ and $r_{\chi_{-7}}(4)=3$; $n=3,5$ are inert primes with $\mathrm{dhprC}=r=0$; $n=6$ has $\Lambda(6)=r_{\chi_{-7}}(6)=0$; and $n=7$ is the ramified prime dividing $M$, where $\mathrm{dhprC}(\chi_{-7},7)=0$ while $r_{\chi_{-7}}(7)=1>0$. The exact rational divisor mass on $I_1$ is $B_1=3/4+1/7=25/28$.
- On $I_2$ (length $13$), $n=9=3^2$ is an even power of an inert prime ($\chi_{-7}(3)=-1$), where $\mathrm{dhprC}(\chi_{-7},9)=2$ and $r_{\chi_{-7}}(9)=1-1+1=1$, saturating the prime-power inequality $\mathrm{dhprC}(\chi_1,p^a)\le 2r_{\chi_1}(p^a)$ with equality ($2=2\cdot 1$); $n=11$ is split ($\mathrm{dhprC}=r=2$); $n=8=2^3$ and $n=16=2^4$ have $r=4$ and $r=5$; $n=14,18$ are composites with $\Lambda=0$ and $r=2$; and **$n=15=3\cdot 5$** is a product of two distinct inert primes, so $\chi_{-7}(15)=(-1)(-1)=+1$ and $\mathrm{dhprC}(\chi_{-7},15)=2>0=2r_{\chi_{-7}}(15)$. Thus $\mathrm{dhprC}(\chi_1,n)\le 2r_{\chi_1}(n)$ is **false** for general composites, and the proof must branch on $\Lambda(n)=0$ before restricting to prime powers: at $n=15$, $\Lambda(15)=0$ makes both sides of $\Lambda(15)\,\mathrm{dhprC}(\chi_{-7},15)\le 2(\log 15)\,r_{\chi_{-7}}(15)$ zero. Summing $r_{\chi_{-7}}(n)/n$ over $I_2$ gives $B_2=4/8+1/9+2/11+2/14+5/16+2/18=15073/11088$.

At $k=1$ and $\sigma=3/2$ ($\eta=1/2$), the exact prime-power block sums are $(\log 2)^2/2$ on $I_1$ (from $n=4$) and $(3/8)(\log 2)^2+(4/27)(\log 3)^2+\frac{2}{11\sqrt{11}}(\log 11)^2+(1/8)(\log 2)^2$ on $I_2$ (from $n=8,9,11,16$), bounded respectively by Lemma 4.10.33(3)'s block majorants $2(1+1)^2 e^{-1/2}B_1=(50/7)e^{-1/2}$ and $2(2+1)^2 e^{-1}B_2=(15073/616)e^{-1}$. The model takes $v_0=1,V=3$ to inspect non-uniform block lengths directly; in Theorem 4.10.35 at $M=7$, the actual cutoff is $v_0=\lceil 8\log 7\rceil=16$ and $V=v_0+N\to\infty$. Again, finite blocks illustrate the discrete partition and prime-power domination, not the analytic tail or $L(1,\chi_1)$ estimates.

#### Definitions and inherited inputs

For an integer modulus $q\ge1$ (`[NeZero q]`), a Dirichlet character $\chi$ modulo $q$, and $U,N,k\in\mathbb{N}$, define the harmonic and character partial sums
$H_k = \sum_{a\in(0,k]} a^{-1}$,
$c_S(\chi,U) = \sum_{b\in(0,U]} \chi(b)/b$,
$c_T(\chi,U) = \sum_{b\in(0,U]} \chi(b)(\log b)/b$,
$c_F(\chi,N) = \sum_{n\in(0,N]} (\sum_{d\mid n}\chi(d))/n$,
together with the real divisor convolution $r_\chi(n)=\Re(\mathrm{zetaMul}\,\chi\,n)=\Re\sum_{d\mid n}\chi(d)$. For a modulus $M\ge1$, a character $\chi_1$ modulo $M$, an integer derivative order $k\ge0$, and real $\sigma$, define
$\mathrm{dhprC}(\chi_1,n) = \Re\mathbf{1}(n) + \Re\chi_1(n)$,
$\mathrm{dhprF}(\chi_1,k,\sigma,n) = (\log n)^k (\Lambda(n)/n^\sigma)\,\mathrm{dhprC}(\chi_1,n)$,
with $\Lambda(0)=r_\chi(0)=\mathrm{dhprF}(\chi_1,k,\sigma,0)=0$ in the archive's convention, and write $I_v=(\lfloor e^v\rfloor,\lfloor e^{v+1}\rfloor]$ (`Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v+1)⌋₊`), $\ell=\log(3M)$, $\lambda=1-\beta_1$, and $\eta=\sigma-1$.

In `DHFinish2Of.lean:38–57`, *DHHyper* asserts $\exists C_H>0$ such that for all $M\ge3$, $\chi_1\bmod M$ with $\chi_1^2=\mathbf{1}$ and $\chi_1\ne\mathbf{1}$, and reals $1\le y\le x$,
$\sum_{n\in(\lfloor y\rfloor,\lfloor x\rfloor]} r_{\chi_1}(n)/n \le |L(1,\chi_1)|\log(x/y) + C_H M(\log y+1)/\sqrt y$;
*DHPrime* asserts $\exists C_P>0$ such that for all $M\ge3$, $\chi_1\bmod M$ with $\chi_1^2=\mathbf{1}$ and $\chi_1\ne\mathbf{1}$, real $\beta_1$ with $L(\beta_1,\chi_1)=0$ and $1-1/\ell\le\beta_1<1$, real $1<\sigma\le2$, and integer $k\ge0$,
$\Re((-1)^k((-L'/L)^{(k)}(\sigma,\mathbf{1})+(-L'/L)^{(k)}(\sigma,\chi_1)))/k! \le C_P\lambda\ell^2(k+2)^2/(\sigma-1)^{k+2} + (C_P\ell)^{k+1}/k! + C_P(k+2)\ell^2/(M(\sigma-1)^{k+1})$;
and `DHPrimeOf` is the implication `DHHyper -> DHPrime`.

We use the following inherited and library inputs without re-proving earlier sections:
- **Character sums and Dirichlet-series tails (inherited local R3 from §4.7 and §4.10.9).** For $\chi\ne\mathbf{1}$ modulo $q\ge1$, $|\sum_{n\in(0,m]}\chi(n)|\le q+1$ (`charSum_le`, wrapping `LGrowth.lean:39`), and `l_function_partial_sum` (`LPartialSum.lean:136`) at $s=1$ gives $|L(1,\chi)-c_S(\chi,N)|\le 4(q+1)/N$ for all $N\ge1$ (`cS_approx`, `PNTDHHyperB.lean:16`).
- **Harmonic, quadratic-convolution, and Chebyshev facts in pinned Mathlib (`0df444a`).** Euler–Mascheroni bracketing gives $H_K-\log(K+1)<\gamma<H_K-\log K$ for $K\ge1$ and $1/2<\gamma<2/3$ (`EulerMascheroni.lean:156–172`, inherited R3). Integral comparison gives $H_N\le 1+\log N$ (`Harmonic/Bounds.lean:33`, read below), multiplicativity gives $r_{\chi_1}(n)\ge0$ when $\chi_1^2=\mathbf{1}$ (`Nonvanishing.lean:90–113`, read and proved inline below), and `Chebyshev.psi_le_const_mul_self` (`Chebyshev.lean:457`) supplies $\sum_{n=1}^N \Lambda(n)\le(\log 4+4)N$ as a library input. [Proof and natural-number specialization in §4.10.14](#p13-chebyshev-tailmertens)
- **Real-axis derivative series and $L(1,\chi_1)$ bound (inherited from [§4.10.12](#p13-turan-finish), same-source reviewed).** For $\sigma>1$, `dhpr_hasSum` (`PNTDHPrimeA.lean:18`, from `PNTDHPos.lean:49`) equates $\sum_{n=0}^\infty \mathrm{dhprF}(\chi_1,k,\sigma,n)$ with $\Re((-1)^k((-L'/L)^{(k)}(\sigma,\mathbf{1})+(-L'/L)^{(k)}(\sigma,\chi_1)))$, and `lfunction_one_le_of_siegel_zero` (`PNTDHPrimeA.lean:191`) supplies $C_D\ge0$ with $|L(1,\chi_1)|\le C_D\ell^2(1-\beta_1)$ whenever $\chi_1\ne\mathbf{1}$, $L(\beta_1,\chi_1)=0$, and $1-1/\ell\le\beta_1<1$. Turán's finite block, the four-disc explicit formula, and the five-term finish of [§4.10.12](#p13-turan-finish) enter as named inputs; deep zero density (`PNTDens.lean:19`), region uniqueness (`NoZeroComplex.lean:32`), and Siegel's lower bound (`SiegelWalfiszAPOfSiegelLower.lean:32`) remain at their inherited named scopes. [A2, DHFinish2Of.lean:38–58, PNTDHHyperA.lean:13–20, PNTDHHyperB.lean:11–31, PNTDHPrimeA.lean:15–50,191](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)

#### Lemma 4.10.30. Hyperbola identity and single-prefix asymptotic [Lean, read]

Let $q\ge1$ be an integer, $\chi$ a Dirichlet character modulo $q$, and $1\le U\le N$ integers.
1. Exact hyperbola decomposition:
   $c_F(\chi,N) = \sum_{b\in(0,U]} (\chi(b)/b)\,H_{\lfloor N/b\rfloor} + \sum_{a\in(0,N]} a^{-1}\sum_{b\in(U,\lfloor N/a\rfloor]} \chi(b)/b$.
2. If $\chi\ne\mathbf{1}$ and $U^2\le N$, then
   $|c_F(\chi,N) - ((\log N+\gamma)c_S(\chi,U) - c_T(\chi,U))| \le 2U/N + 8(q+1)(1+\log N)/U$,
   and specializing to $U=\lfloor\sqrt N\rfloor$ gives
   $|c_F(\chi,N) - ((\log N+\gamma)L(1,\chi) - c_T(\chi,\lfloor\sqrt N\rfloor))| \le 26(q+1)(\log N+1)/\sqrt N$.

**Proof.** In $c_F(\chi,N)=\sum_{n=1}^N\sum_{d\mid n}\chi(d)/n$, a pair $(n,d)$ satisfies $1\le n\le N$ and $d\mid n$ if and only if $1\le d\le N$ and $n=da$ with $1\le a\le\lfloor N/d\rfloor$. Swapping the sums and writing $(da)^{-1}=d^{-1}a^{-1}$ yields $c_F(\chi,N)=\sum_{b=1}^N (\chi(b)/b)H_{\lfloor N/b\rfloor}$ (`cF_eq`). Split $(0,N]=(0,U]\sqcup(U,N]$. On $(U,N]$, the condition $b\in(U,N]$ and $a\in(0,\lfloor N/b\rfloor]$ is equivalent to $ab\le N$, $b>U$, and $a\ge1$, hence to $a\in(0,N]$ and $b\in(U,\lfloor N/a\rfloor]$. Interchanging the finite sums proves (1) (`cF_split`).

Now assume $\chi\ne\mathbf{1}$ and $U^2\le N$. For $1\le b\le U$, $b^2\le U^2\le N$ implies $K=\lfloor N/b\rfloor\ge1$ and $Kb\le N<(K+1)b$. Euler–Mascheroni bracketing gives $0<H_K-\log K-\gamma<\log(K+1)-\log K=\log(1+1/K)\le 1/K$, while taking logarithms of $Kb\le N<(K+1)b$ gives $-1/K\le -\log(1+1/K)<\log K+\log b-\log N\le 0$. Adding the two two-sided estimates gives $|H_K-(\log N+\gamma-\log b)|\le 1/K$. Because $K\ge1$, $2Kb\ge(K+1)b>N$, so $1/K\le 2b/N$ (`term_bound`). Multiplying by $|\chi(b)|/b\le 1/b$ cancels $b$ and leaves $2/N$ per index, or $2U/N$ in sum over $b\in(0,U]$.

On the second wing, fix $a\in(0,N]$. If $\lfloor N/a\rfloor\le U$, the interval $(U,\lfloor N/a\rfloor]$ is empty and its sum is $0$. If $\lfloor N/a\rfloor>U$, consecutive splitting rewrites the inner sum as the difference $c_S(\chi,\lfloor N/a\rfloor)-c_S(\chi,U)=(L(1,\chi)-c_S(\chi,U))-(L(1,\chi)-c_S(\chi,\lfloor N/a\rfloor))$. By `cS_approx` and $\lfloor N/a\rfloor\ge U$, both tails have modulus at most $4(q+1)/U$, so the row sum has modulus at most $8(q+1)/U$. Summing $a^{-1}(8(q+1)/U)$ over $a\in(0,N]$ gives $H_N\cdot 8(q+1)/U$. Since $\int_k^{k+1} x^{-1}\,dx\ge(k+1)^{-1}$ for $k\ge1$, $H_N\le 1+\int_1^N x^{-1}\,dx=1+\log N$ (`harmonic_le_one_add_log`), proving the first inequality of (2) (`cF_main`).

For $N\ge1$, put $U=\lfloor\sqrt N\rfloor\ge1$, so $U^2\le N<(U+1)^2$. Thus $U\le\sqrt N<U+1\le 2U$, giving $U/N\le 1/\sqrt N$ and $1/U\le 2/\sqrt N$. Replacing $c_S(\chi,U)$ by $L(1,\chi)$ inside $(\log N+\gamma)c_S(\chi,U)$ adds at most $(\log N+\gamma)\cdot 4(q+1)/U\le 8(q+1)(\log N+1)/\sqrt N$ since $0\le\gamma\le 1$. Together with $2U/N\le 2/\sqrt N\le 2(q+1)(\log N+1)/\sqrt N$ and $8(q+1)(1+\log N)/U\le 16(q+1)(\log N+1)/\sqrt N$, the three coefficients sum to $2+16+8=26$ (`cF_approx`). [A2, PNTDHHyperA.lean:21–91 and PNTDHHyperC.lean:21–198](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)

#### Lemma 4.10.31. Log-weighted Abel tail and interval difference [Lean, read]

Let $q\ge1$ be an integer and $\chi\ne\mathbf{1}$ a Dirichlet character modulo $q$.
1. For all integers $1\le U\le V$, $|c_T(\chi,V)-c_T(\chi,U)|\le 4(q+1)(1+\log(U+1))/(U+1)$.
2. For all reals $1\le a\le b$, $(\log b+1)/\sqrt b\le 2(\log a+1)/\sqrt a$.
3. For all integers $1\le N_0\le N_1$,
   $\Re(c_F(\chi,N_1)-c_F(\chi,N_0)) \le |L(1,\chi)|(\log N_1-\log N_0) + 86(q+1)(\log N_0+1)/\sqrt{N_0}$.

**Proof.** For any sequence $c_n\in\mathbb{C}$ with partial sums $A_m=\sum_{n\in(0,m]} c_n$ bounded by $|A_m|\le B$, and any real weight $w_n$ satisfying $w_{U+1}\ge0$ and $0\le w_{n+1}\le w_n$ for all $n>U$, induction on $V\ge U$ verifies the discrete Abel identity
$\sum_{n\in(U,V]} c_n w_n = A_V w_{V+1} - A_U w_{U+1} + \sum_{n\in(U,V]} A_n(w_n-w_{n+1})$.
Taking norms and telescoping $\sum_{n\in(U,V]}(w_n-w_{n+1})=w_{U+1}-w_{V+1}$ bounds the modulus by $B w_{V+1}+B w_{U+1}+B(w_{U+1}-w_{V+1})=2B w_{U+1}$ (`abel_bound`).

Apply this to $c_n=\chi(n)$ with $B=q+1$ and $w_n=(\log n)/n$. Because $x\mapsto(\log x)/x$ has derivative $(1-\log x)/x^2\le0$ on $[e,\infty)$ and $e<2.72<3$, the sequence $w_n$ is nonnegative and nonincreasing for $n\ge3$ (`lw_anti`), though not from $n=2$ since $(\log 2)/2<(\log 3)/3$. When $U\ge2$, every $n>U$ satisfies $n\ge3$, so `abel_bound` gives $|c_T(\chi,V)-c_T(\chi,U)|\le 2(q+1)w_{U+1}\le 4(q+1)(1+\log(U+1))/(U+1)$ (`cT_diff2`). When $U=1$, the case $V=1$ is trivial, and for $V\ge2$ splitting at $2$ gives $|c_T(\chi,V)-c_T(\chi,1)|\le |c_T(\chi,V)-c_T(\chi,2)|+|\chi(2)|(\log 2)/2\le 2(q+1)(\log 3)/3+1/2$ since $\log 2<1$. Using $\log 3\le 2$ and $1\le(q+1)(1+\log 2)$ bounds $(4/3)(q+1)+1/2$ by $2(q+1)(1+\log 2)=4(q+1)(1+\log 2)/2$, proving (1) (`cT_diff`).

For (2), put $s=\sqrt b/\sqrt a\ge1$, so $\sqrt b=\sqrt a\cdot s$ and $\log b=\log a+2\log s\le\log a+2(s-1)$. Since $\log a\ge0$ and $s\ge1$, $\log b+1\le\log a+2s-1\le 2(\log a+1)s$; dividing by $\sqrt b=\sqrt a\cdot s$ gives (2) (`g_mono`).

For (3), let $U_0=\lfloor\sqrt{N_0}\rfloor\ge1$, $U_1=\lfloor\sqrt{N_1}\rfloor\ge U_0$, $B=q+1$, and $g_0=(\log N_0+1)/\sqrt{N_0}$. Write $R_j=c_F(\chi,N_j)-((\log N_j+\gamma)L(1,\chi)-c_T(\chi,U_j))$ for $j=0,1$. Subtracting cancels $\gamma L(1,\chi)$ identically:
$c_F(\chi,N_1)-c_F(\chi,N_0) = (\log N_1-\log N_0)L(1,\chi) - (c_T(\chi,U_1)-c_T(\chi,U_0)) + R_1 - R_0$.
Since $\log N_1-\log N_0\ge0$, $\Re((\log N_1-\log N_0)L(1,\chi))\le |L(1,\chi)|(\log N_1-\log N_0)$. Lemma 4.10.30(2) and part (2) give $|R_0|\le 26B g_0$ and $|R_1|\le 26B(\log N_1+1)/\sqrt{N_1}\le 52B g_0$. Next, $U_0\le N_0$ and $\log 2<1$ imply $\log(U_0+1)\le\log(2N_0)<1+\log N_0$, while $U_0+1>\sqrt{N_0}$, so $(1+\log(U_0+1))/(U_0+1)\le 2g_0$; part (1) then gives $|c_T(\chi,U_1)-c_T(\chi,U_0)|\le 8B g_0$. Summing $52+26+8=86$ proves (3) (`diff_bound`). [A2, PNTDHHyperB.lean:32–158 and PNTDHHyper.lean:14–111](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)

<a id="p13-dh-hyper"></a>

#### Theorem 4.10.32. Production of *DHHyper* [Lean, read]

With $C_H=400>0$, *DHHyper* holds: for every integer $M\ge3$, every character $\chi_1$ modulo $M$ with $\chi_1^2=\mathbf{1}$ and $\chi_1\ne\mathbf{1}$, and all reals $1\le y\le x$,
$\sum_{n\in(\lfloor y\rfloor,\lfloor x\rfloor]} r_{\chi_1}(n)/n \le |L(1,\chi_1)|\log(x/y) + 400 M(\log y+1)/\sqrt y$.

**Proof.** Set $N_0=\lfloor y\rfloor\ge1$, $N_1=\lfloor x\rfloor\ge N_0$, $B=M+1$, and $Y=(\log y+1)/\sqrt y\ge0$. Because $(0,N_1]=(0,N_0]\sqcup(N_0,N_1]$ and $\Re(z/n)=(\Re z)/n$ for real $n$, the left-hand side equals $\Re(c_F(\chi_1,N_1)-c_F(\chi_1,N_0))$. Apply Lemma 4.10.31(3). First compare integer and real logarithms: $\log N_1\le\log x$, and from $N_0\le y<N_0+1\le 2N_0$ we get $\log y-\log N_0=\log(y/N_0)\le y/N_0-1=(y-N_0)/N_0\le 1/N_0\le 2/y$, whence $\log N_1-\log N_0\le\log(x/y)+2/y$. Second, `cS_approx` at $N=1$ gives $|L(1,\chi_1)-1|\le 4B$, so $|L(1,\chi_1)|\le 1+4B\le 5B$. Since $y\ge1$ implies $\sqrt y\le y$ and $\log y\ge0$, we have $2/y\le 2(\log y+1)/\sqrt y=2Y$, so $|L(1,\chi_1)|\cdot(2/y)\le 10B Y$. Third, $y<N_0+1\le 4N_0$ gives $\sqrt y\le 2\sqrt{N_0}$, and $\log N_0\le\log y$ gives $(\log N_0+1)/\sqrt{N_0}\le 2Y$, whence $86B(\log N_0+1)/\sqrt{N_0}\le 172B Y$. Finally, $M\ge3$ implies $B=M+1\le 2M$, so $(10+172)B Y=182B Y\le 364 M Y\le 400 M Y$ (`deuring_heilbronn_hypergeometric`). [A2, PNTDHHyper.lean:114–190](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)

#### Lemma 4.10.33. Arithmetic domination, Mertens' prefix, and local blocks [Lean, read]

Let $M\ge1$ be an integer, $\chi_1$ a character modulo $M$ with $\chi_1^2=\mathbf{1}$, $k\in\mathbb{N}$, and $\sigma\ge1$.
1. Every $n\in\mathbb{N}$ satisfies $0\le\mathrm{dhprC}(\chi_1,n)\le2$, $r_{\chi_1}(n)\ge0$, $\mathrm{dhprF}(\chi_1,k,\sigma,n)\ge0$, and $\Lambda(n)\,\mathrm{dhprC}(\chi_1,n)\le 2(\log n)\,r_{\chi_1}(n)$.
2. With $C_{\mathrm{Mer}}=(\log 4+4)(1/\log 2+1)\ge0$, every real $y\ge2$ satisfies $\sum_{n=1}^{\lfloor y\rfloor}\Lambda(n)/n\le C_{\mathrm{Mer}}\log y$, and every integer $v_0\ge1$ satisfies $\sum_{n\in(0,\lfloor e^{v_0}\rfloor]} \mathrm{dhprF}(\chi_1,k,\sigma,n)\le 2C_{\mathrm{Mer}}v_0^{k+1}$.
3. For every $v\in\mathbb{N}$ and real $B_v$ with $\sum_{n\in I_v} r_{\chi_1}(n)/n\le B_v$,
   $\sum_{n\in I_v} \mathrm{dhprF}(\chi_1,k,\sigma,n) \le 2(v+1)^{k+1}e^{-(\sigma-1)v} B_v$;
   moreover, for all integers $0\le v_0\le V$, $(\lfloor e^{v_0}\rfloor,\lfloor e^V\rfloor]=\bigsqcup_{v=v_0}^{V-1} I_v$.

**Proof.** If $n\bmod M$ is a unit, $\chi_1(n)^2=1$ forces $\chi_1(n)\in\{1,-1\}$ and $\mathbf{1}(n)=1$, so $\mathrm{dhprC}(\chi_1,n)\in\{0,2\}$; if $n\bmod M$ is not a unit, both characters vanish and $\mathrm{dhprC}(\chi_1,n)=0$ (`dhpr_C_bounds`). Because $1$ and $\chi_1$ are multiplicative, their Dirichlet convolution $\mathrm{zetaMul}\,\chi_1$ is multiplicative with prime-power values $\sum_{i=0}^a \chi_1(p)^i$, equal to $1$ when $p\mid M$, to $a+1$ when $\chi_1(p)=1$, and to $(1+(-1)^a)/2\in\{0,1\}$ when $\chi_1(p)=-1$; thus $r_{\chi_1}(n)\ge0$ (`zetaMul_nonneg`, `dhpr_r_nonneg`). If $\Lambda(n)=0$, $\Lambda(n)\,\mathrm{dhprC}(\chi_1,n)=0\le 2(\log n)\,r_{\chi_1}(n)$. Otherwise $n=p^a$ with $p$ prime and $a\ge1$, where $\Lambda(p^a)=\log p$ and $\log(p^a)=a\log p$. Checking the same three prime cases gives $\mathrm{dhprC}(\chi_1,p^a)\le 2r_{\chi_1}(p^a)$: $0\le 2$ for $p\mid M$, $2\le 2(a+1)$ for $\chi_1(p)=1$, and $1+(-1)^a=2r_{\chi_1}(p^a)$ for $\chi_1(p)=-1$. Multiplying by $\log p\le a\log p$ proves (1) (`dhpr_coef_le`).

For (2), let $c=\log 4+4$, so $\psi(N)=\sum_{n=1}^N \Lambda(n)\le cN$ (`tail_mertens_psi`). We prove $\sum_{n=1}^{N+1}\Lambda(n)/n\le \psi(N+1)/(N+1)+c\log(N+1)$ by induction on $N\in\mathbb{N}$. At $N=0$, $\Lambda(1)=0$. Passing from $M$ to $M+1$, put $B_\psi=\psi(M+1)\le c(M+1)$, so $B_\psi/(M+1)\le(B_\psi+c)/(M+2)$ by cross-multiplying $(M+2)B_\psi\le(M+1)B_\psi+c(M+1)$. Adding $\Lambda(M+2)/(M+2)$ to the induction bound gives $(\psi(M+2)+c)/(M+2)+c\log(M+1)$, and $1/(M+2)=1-(M+1)/(M+2)\le\log((M+2)/(M+1))$ completes the step (`tail_mertens_nat`). For $y\ge2$, write $\lfloor y\rfloor=M+1\ge2$; then $\psi(M+1)/(M+1)\le c\le c(\log y/\log 2)$ and $\log(M+1)\le\log y$, giving $C_{\mathrm{Mer}}\log y$ (`tail_mertens`). On $(0,\lfloor e^{v_0}\rfloor]$ for $v_0\ge1$, $e^{v_0}\ge e\ge2$, $n^{-\sigma}\le n^{-1}$, $\mathrm{dhprC}(\chi_1,n)\le2$, and $\log n\le v_0$, so each term is at most $2v_0^k\Lambda(n)/n$ and summing gives $2C_{\mathrm{Mer}}v_0^{k+1}$ (`dhpr_small`).

For (3), $n\in I_v=(\lfloor e^v\rfloor,\lfloor e^{v+1}\rfloor]$ means $\lfloor e^v\rfloor<n\le\lfloor e^{v+1}\rfloor$, which by the floor universal properties holds if and only if $e^v<n\le e^{v+1}$, hence $n\ge1$ and $v<\log n\le v+1$. Because $\sigma\ge1$, $n^\sigma=n^{\sigma-1}n=e^{(\sigma-1)\log n}n\ge e^{(\sigma-1)v}n$, so $n^{-\sigma}\le e^{-(\sigma-1)v}/n$ (`dhpr_rpow_le`), while $(\log n)^{k+1}\le(v+1)^{k+1}$. Using part (1), $\mathrm{dhprF}(\chi_1,k,\sigma,n)\le 2(\log n)^{k+1}r_{\chi_1}(n)n^{-\sigma}\le 2(v+1)^{k+1}e^{-(\sigma-1)v}r_{\chi_1}(n)/n$; summing over $I_v$ gives the block bound (`dhpr_block`). Since $v\mapsto\lfloor e^v\rfloor$ is monotone nondecreasing (`dhpr_floor_mono`), induction on $V\ge v_0$ splits $(\lfloor e^{v_0}\rfloor,\lfloor e^V\rfloor]$ into consecutive half-open blocks $I_v$ without overlap (`dhpr_blocks`). [A2, PNTDHPrimeA.lean:52–189, TailMertens.lean:9–101, PNTDHPrimeB.lean:208–222 and PNTDHPrimeC.lean:17–114](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)

#### Lemma 4.10.34. Moment weights and geometric aggregation [Lean, read]

Let $0<\eta\le1$, $m,k\in\mathbb{N}$, and $0\le v_0\le V$ be integers.
1. Uniform supremum: $(v+1)^m e^{-\eta v}\le e\,m!/\eta^m$ for every $v\in\mathbb{N}$.
2. Polynomial-exponential sum: $\sum_{v\in[v_0,V)} (v+1)^m e^{-\eta v}\le 2e^2(m+1)m!/\eta^{m+1}$.
3. Hyperbola error tail: $\sum_{v\in[v_0,V)} (v+1)e^{-v/2}\le 20e^{-v_0/4}$.
4. Aggregate large-range moment: if $\sigma=1+\eta$, $A\ge0$, $C_H\ge0$, and every $v\in\mathbb{N}$ satisfies $\sum_{n\in I_v} r_{\chi_1}(n)/n\le A+C_H M(v+1)e^{-v/2}$ for $\chi_1^2=\mathbf{1}$ modulo $M\ge1$, then
   $\sum_{n\in(\lfloor e^{v_0}\rfloor,\lfloor e^V\rfloor]} \mathrm{dhprF}(\chi_1,k,\sigma,n) \le 4e^2 A(k+2)(k+1)k!/\eta^{k+2} + 40e C_H M((k+1)k!/\eta^{k+1})e^{-v_0/4}$.

**Proof.** Three elementary exponential inequalities drive (1)–(3): for $b,t\ge0$, the $m$th Taylor term of $e^{bt}$ gives $(bt)^m e^{-bt}\le m!$ (`dhpr_pow_exp_le`); for $a>0$, $e^{-a}(1+a)\le e^{-a}e^a=1$ rearranges to $a/(1+a)\le 1-e^{-a}$ (`dhpr_one_sub_exp_neg`); and for $m\ge1$, $m+1=m(1+1/m)\le m e^{1/m}$ raised to the $m$th power gives $(m+1)^m\le e m^m$, which also holds at $m=0$ since $1\le e$ (`dhpr_pow_ratio`).

For (1), $\eta\le1$ implies $-\eta v=1-\eta(v+1)-(1-\eta)\le 1-\eta(v+1)$, so $e^{-\eta v}\le e\cdot e^{-\eta(v+1)}$. Multiplying by $\eta^m(v+1)^m$ and applying $(bt)^m e^{-bt}\le m!$ at $b=\eta,t=v+1$ gives $\eta^m(v+1)^m e^{-\eta v}\le e\,m!$ (`dhpr_wsup`).

For (2), set $\delta=\eta/(m+1)>0$, so $\eta=m\delta+\delta$ and $m\delta\le\eta\le1$. First, $\eta^m=(m+1)^m\delta^m\le e(m\delta)^m$. Second, $-\eta v=1-m\delta(v+1)-\delta v-(1-m\delta)\le 1-m\delta(v+1)-\delta v$, so $e^{-\eta v}\le e\cdot e^{-m\delta(v+1)}e^{-\delta v}$. Combining the two and applying $(bt)^m e^{-bt}\le m!$ at $b=m\delta,t=v+1$ yields the pointwise geometric majorant $\eta^m(v+1)^m e^{-\eta v}\le e^2 m! e^{-\delta v}$. Summing over $v\in[v_0,V)\subset[0,V)$ gives $\sum_{v=v_0}^{V-1} e^{-\delta v}\le\sum_{v=0}^{V-1}(e^{-\delta})^v=(1-e^{-\delta V})/(1-e^{-\delta})\le 1/(1-e^{-\delta})$. Using $\delta/(1+\delta)\le 1-e^{-\delta}$, we obtain $\delta\sum_{v=v_0}^{V-1} e^{-\delta v}\le 1+\delta$. Multiplying by $\eta=(m+1)\delta$ and using $\eta\le1\le m+1$ gives $\eta^{m+1}\sum_{v=v_0}^{V-1}(v+1)^m e^{-\eta v}\le e^2 m!(m+1+\eta)\le 2e^2(m+1)m!$ (`dhpr_wsum`).

For (3), $1+v/4\le e^{v/4}$ gives $v+1\le 4(1+v/4)\le 4e^{v/4}$, hence $(v+1)e^{-v/2}\le 4(e^{-1/4})^v$. Factoring out $(e^{-1/4})^{v_0}=e^{-v_0/4}$ leaves $4e^{-v_0/4}\sum_{j=0}^{V-v_0-1}(e^{-1/4})^j\le 4e^{-v_0/4}/(1-e^{-1/4})$. Since $1-e^{-1/4}\ge(1/4)/(1+1/4)=1/5$, the factor is at most $4\cdot 5=20$ (`dhpr_esum`).

For (4), decompose $(\lfloor e^{v_0}\rfloor,\lfloor e^V\rfloor]=\bigsqcup_{v=v_0}^{V-1} I_v$ by Lemma 4.10.33(3) and apply the single-block estimate with $B_v=A+C_H M(v+1)e^{-v/2}$ to each $v$. On the $A$-piece, apply (2) at $m=k+1$, noting $(k+1)!=(k+1)k!$. On the $C_H M$-piece, bound each factor $(v+1)^{k+1}e^{-\eta v}$ uniformly by (1) at $m=k+1$ and sum the remaining $(v+1)e^{-v/2}$ by (3) (`dhpr_large`). [A2, PNTDHPrimeB.lean:9–207 and PNTDHPrimeD.lean:12–68](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)

<a id="p13-dh-prime"></a>

#### Theorem 4.10.35. Production of *DHPrime* and consumer handoff [Lean, read]

Assume *DHHyper* with constant $C_H>0$, Mertens' bound with $C_{\mathrm{Mer}}\ge0$, and the segment $L$-value bound $|L(1,\chi_1)|\le C_D\ell^2(1-\beta_1)$ with $C_D\ge0$. Set
$C_P = \max(\max(30C_D, 18C_{\mathrm{Mer}}+9), 110C_H) > 0$.
Then *DHPrime* holds with constant $C_P$, and `deuring_heilbronn_prime_sum deuring_heilbronn_hypergeometric` supplies *DHPrime* directly to the Turán completion recorded as Theorem 4.10.29 in the draft (`deuring_heilbronn_lossy : DeuringHeilbronnMB`).

**Proof.** Fix $M\ge3$, $\chi_1\bmod M$ with $\chi_1^2=\mathbf{1}$ and $\chi_1\ne\mathbf{1}$, real $\beta_1$ with $L(\beta_1,\chi_1)=0$ and $1-1/\ell\le\beta_1<1$, real $1<\sigma\le2$, and integer $k\ge0$. Put $\eta=\sigma-1\in(0,1]$, $A=|L(1,\chi_1)|\ge0$, and $F=k!>0$. Evaluating *DHHyper* at $y=e^v\ge1$ and $x=e^{v+1}\ge y$ simplifies $\log(e^{v+1}/e^v)=1$, $\log(e^v)=v$, and $\sqrt{e^v}=e^{v/2}$, giving $\sum_{n\in I_v} r_{\chi_1}(n)/n\le A+C_H M(v+1)e^{-v/2}$ for every $v\in\mathbb{N}$ (`dhpr_hyper_simp`).

Choose the integer cutoff $v_0=\lceil 8\log M\rceil$. Since $M\ge3$, $\log M>0$ and $v_0\ge1$. For every $N\in\mathbb{N}$, $v_0+N<e^{v_0+N}$ gives $N\le\lfloor e^{v_0+N}\rfloor$. Because $\mathrm{dhprF}(\chi_1,k,\sigma,0)=0$ and every term is nonnegative by Lemma 4.10.33(1),
$\sum_{n=0}^{N-1} \mathrm{dhprF}(\chi_1,k,\sigma,n) \le \sum_{n\in(0,\lfloor e^{v_0}\rfloor]} \mathrm{dhprF}(\chi_1,k,\sigma,n) + \sum_{n\in(\lfloor e^{v_0}\rfloor,\lfloor e^{v_0+N}\rfloor]} \mathrm{dhprF}(\chi_1,k,\sigma,n)$.
Lemmas 4.10.33(2) and 4.10.34(4) at $V=v_0+N$ bound the right-hand side uniformly in $N$ by
$2C_{\mathrm{Mer}}v_0^{k+1} + 4e^2 A(k+2)(k+1)F/\eta^{k+2} + 40e C_H M((k+1)F/\eta^{k+1})e^{-v_0/4}$ (`dhpr_partial`).
Passing to the limit $N\to\infty$ along `dhpr_hasSum` bounds the unnormalized derivative sum $\Re((-1)^k((-L'/L)^{(k)}(\sigma,\mathbf{1})+(-L'/L)^{(k)}(\sigma,\chi_1)))$ by the same quantity.

Now verify the cutoff and constant inequalities (`dhpr_arith`, `dhpr_main`). Since $3M\ge9>e$ (from $e<2.72$, `Real.exp_one_lt_d9`), $\ell=\log(3M)\ge1$, $\log M\le\ell$, and $v_0<8\log M+1\le 8\ell+\ell=9\ell$. Also $v_0\ge 8\log M$ implies $E:=e^{-v_0/4}\le e^{-2\log M}=M^{-2}$, so $M E\le 1/M$. Using $e\le 2.72$, $e^2\le 7.4$, $k+1\le k+2$, $1\le\ell^2$, and $A\le C_D\ell^2\lambda$:
- **Prefix term:** $2C_{\mathrm{Mer}}v_0^{k+1}\le 2C_{\mathrm{Mer}}(9\ell)^{k+1}=(18C_{\mathrm{Mer}})\cdot 9^k\ell^{k+1}\le C_P\cdot C_P^k\ell^{k+1}=(C_P\ell)^{k+1}$, because $C_P\ge 18C_{\mathrm{Mer}}+9$ forces both $18C_{\mathrm{Mer}}\le C_P$ and $9\le C_P$ (as well as $C_P>0$).
- **Main $L(1,\chi_1)$ term:** $4e^2 A(k+2)(k+1)(F/\eta^{k+2})\le 4\cdot 7.4\,C_D\lambda\ell^2(k+2)^2(F/\eta^{k+2})=29.6\,C_D\lambda\ell^2(k+2)^2(F/\eta^{k+2})\le C_P\lambda\ell^2(k+2)^2 F/\eta^{k+2}$.
- **Hyperbola tail term:** $40e C_H(k+1)(M E)(F/\eta^{k+1})\le 40\cdot 2.72\,C_H(k+2)(1/M)(F/\eta^{k+1})=108.8\,C_H(k+2)F/(M\eta^{k+1})\le C_P\ell^2(k+2)F/(M\eta^{k+1})$ since $108.8\,C_H\le 110C_H\le C_P\le C_P\ell^2$.

Dividing by $F=k!>0$ yields *DHPrime* (`deuring_heilbronn_prime_sum`). In `PNTDHB.lean:13–15`, `deuring_heilbronn_lossy` feeds `deuring_heilbronn_prime_sum deuring_heilbronn_hypergeometric` directly into `deuring_heilbronn_finish_turan`. [A2, PNTDHPrimeC.lean:115–128, PNTDHPrime.lean:12–162 and PNTDHB.lean:13–15](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)

#### Parameters, cutoffs, error quantifiers, and consumer contract

| Symbol or interface | Choice, quantifier scope, and downstream contract |
|---|---|
| $U=\lfloor\sqrt N\rfloor$ | Per integer endpoint $N\ge1$ inside `cF_approx`; balances Wing I harmonic rounding $2U/N\le 2/\sqrt N$ against Wing II character-tail cancellation $8(q+1)(1+\log N)/U\le 16(q+1)(\log N+1)/\sqrt N$ |
| $N_0=\lfloor y\rfloor,\ N_1=\lfloor x\rfloor$ | Per real interval $1\le y\le x$ in *DHHyper*; differencing cancels $\gamma L(1,\chi_1)$, bounds $c_T(\chi_1,U_1)-c_T(\chi_1,U_0)$ by $8(M+1)g_0$, and absorbs floor rounding $\log y-\log N_0\le 2/y$ into $400 M(\log y+1)/\sqrt y$ |
| $C_H=400$ | Absolute *DHHyper* witness (`PNTDHHyper.lean:115`), chosen before all $M\ge3$, $\chi_1\bmod M$, and $1\le y\le x$ |
| $C_{\mathrm{Mer}}=(\log 4+4)(1/\log 2+1)$ | Absolute Mertens witness (`TailMertens.lean:67`), chosen before all $y\ge2$; supplies $\sum_{n\le y}\Lambda(n)/n\le C_{\mathrm{Mer}}\log y$ |
| $v_0=\lceil 8\log M\rceil,\ V=v_0+N$ | Per modulus $M\ge3$ in `dhpr_main` ($1\le v_0\le 9\ell$) and per partial-sum index $N\in\mathbb{N}$ before $N\to\infty$; ensures $M e^{-v_0/4}\le M\cdot M^{-2}=1/M$ while bounding the prefix by $2C_{\mathrm{Mer}}(9\ell)^{k+1}$ |
| $\delta=\eta/(k+2)$ | Per derivative order $k\ge0$ and scale $\eta=\sigma-1\in(0,1]$ inside `dhpr_wsum` ($m=k+1$); splits $e^{-\eta v}=e^{-(k+1)\delta v}e^{-\delta v}$ so $(k+1)!$ absorbs $(v+1)^{k+1}$ and $\sum e^{-\delta v}$ contributes one extra $1/\delta=(k+2)/\eta$ |
| $C_P=\max(30C_D,18C_{\mathrm{Mer}}+9,110C_H)$ | Uniform *DHPrime* witness (`PNTDHPrime.lean:156`), chosen before all $M\ge3$, $\chi_1$, $\beta_1\in[1-1/\ell,1)$, $\sigma\in(1,2]$, and $k\ge0$ |
| Consumer handoff (`PNTDHB.lean:15`) | Specializes *DHPrime* at $\sigma=1+\eta$ ($\eta=\delta=1-\Re\rho\le c_0\le 1/25\le 1$) and $k=j-1$ ($j\ge1$), delivering Rows 1–3 of the five-term budget in Theorem 4.10.29 of [§4.10.12](#p13-turan-finish) and returning $B=3$ in `DeuringHeilbronnMB` to `PNTFinal.lean:18–24` and `PNTZSumL.lean:78,129` |

#### Counterexample and scope remarks

**Counterexample: omitting the hyperbola overlap subtraction.** In Lemma 4.10.30(1), the active Wing II rows are $1\le a\le V(N):=\lfloor N/(U+1)\rfloor$ with $U=\lfloor\sqrt N\rfloor$, where $\lfloor N/a\rfloor>U$ and the inner sum is $c_S(\chi_1,\lfloor N/a\rfloor)-c_S(\chi_1,U)$. Suppose one omits the overlap subtraction $-c_S(\chi_1,U)$ on those active rows (equivalently, adds the vertical strip $1\le b\le U$ and the horizontal strip $1\le a\le V(N)$ without subtracting their intersection $\{1\le a\le V(N),\ 1\le b\le U\}$), forming
$c_F^{\mathrm{unsub}}(\chi_1,N) := \sum_{b=1}^U (\chi_1(b)/b)\,H_{\lfloor N/b\rfloor} + \sum_{a=1}^{V(N)} a^{-1} c_S(\chi_1,\lfloor N/a\rfloor) = c_F(\chi_1,N) + H_{V(N)} c_S(\chi_1,U)$.
In Calculation A ($M=4$, $\chi_1=\chi_{-4}$), this already produces strictly positive rational errors at finite endpoints and after differencing: $+1$ at $N_0=9$, $+11/9$ at $N_1=15$, and $+2/9$ on the interval $(9,15]$ ($337/585$ instead of $23/65$). More fundamentally, omitting the overlap subtraction refutes *DHHyper* **for every candidate constant $C_H\in\mathbb{R}$** and every real nonprincipal quadratic character $\chi_1$ modulo $M\ge3$: by nonvanishing and quadratic convolution positivity (`LFunction_ne_zero_of_one_le_re`, `zetaMul_nonneg`), $L(1,\chi_1)$ is real and strictly positive. For $N\ge9$, $U=\lfloor\sqrt N\rfloor\ge3$ and $(U-1)(U+1)=U^2-1<N$ imply $U-1\le V(N)\le U$, so $H_{V(N)}=\frac{1}{2}\log N+O(1)$ and $c_S(\chi_1,U)=L(1,\chi_1)+O(M/\sqrt N)$ as $N\to\infty$. Hence $H_{V(N)}c_S(\chi_1,U)=\frac{1}{2}L(1,\chi_1)\log N+O_M(1)$. Fixing $y=9$ and letting $x=N\to\infty$,
$\Re(c_F^{\mathrm{unsub}}(\chi_1,N)-c_F^{\mathrm{unsub}}(\chi_1,9)) = \frac{3}{2}L(1,\chi_1)\log(N/9) + O_M(1)$,
whereas for any fixed $C_H\in\mathbb{R}$ the right-hand side of *DHHyper* is $L(1,\chi_1)\log(N/9)+C_H M(\log 9+1)/3$. Because $\frac{3}{2}L(1,\chi_1)>L(1,\chi_1)>0$, the unsubtracted difference strictly exceeds the *DHHyper* bound for all sufficiently large $N$ (and omitting the active-row restriction $\lfloor N/a\rfloor>U$ as well inflates the slope further to $2L(1,\chi_1)\log(N/9)+O_M(1)$).

**Sufficient parameter choices for this proof.** The range $0<\eta=\sigma-1\le1$ gives the uniform shift $e^{-\eta v}\le e\,e^{-\eta(v+1)}$ used in `dhpr_wsup` and `dhpr_wsum`. With this range deleted entirely, the bound in Lemma 4.10.34(1) fails at $\sigma=4$, $\eta=3$, $m=1$ and $v=0$, where it would assert $1\le e/3<1$. For the hyperbola error, $v+1\le 4e^{v/4}$ leaves the rate $e^{-v/4}$. The choice $v_0=\lceil 8\log M\rceil$ therefore gives $M e^{-v_0/4}\le M^{-1}$. In the Turán completion the inherited inequalities $\lambda\ge c_S/\sqrt M$ and $\ell^2/M\le32/\sqrt M$ pay the resulting term. At $v_0=\lceil2\log M\rceil$, this specific error factor grows on the order of $M^{1/2}$.

**Classical comparison and reading scope.** Dirichlet introduced the hyperbola lattice split in 1849 for the divisor sum $\sum_{n\le x} d(n)$ [[Dirichlet 1849](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)], and Tao's *254A Notes 1* develops both the symmetric inclusion–exclusion form and the disjoint two-wing form for $\sum_{n\le x}(1\ast\chi)(n)/\sqrt n$ alongside the first Mertens bound [[Tao 2014, Notes 1, Theorem 13, eqs. (54)–(56) and (80)–(83)](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)]. In the Deuring–Heilbronn literature, Thorner and Zaman avoid a separate prime-moment upper bound by working on the global zero partial-fraction identity where $(1+\psi^\ast(n))\Lambda(n)\ge0$ stays on the left [[Thorner–Zaman, §6.2](../sources/SOURCES.md#chapter-4-41012-the-turan-finish)], whereas Benli, Goel, Twiss, and Zaman study the same nonnegative convolution $a=1\ast\chi_1$ by shifting a Mellin contour across $1-\beta_1$ inside a Selberg-sieve mollifier [[Benli et al. v3, §4, Lemmas 4.1–4.3](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)]. Archive A2 combines local Borel–Carathéodory discs with real-axis hyperbola differencing on logarithmic blocks. Its leading prime moment uses the two logarithms in $|L(1,\chi_1)|\le C_D\lambda\ell^2$. The production proofs of the hyperbola and prime-moment estimates carry their local R3 [Lean, read] scope. The Turán completion, its deeper suppliers and the Chebyshev estimate enter at the reading levels recorded in the source ledger. The deep zero density (`PNTDens.lean:19`), region uniqueness (`NoZeroComplex.lean:32`) and Siegel lower bound (`SiegelWalfiszAPOfSiegelLower.lean:32`) remain named inputs. [Pinned sources and classical comparison](../sources/SOURCES.md#chapter-4-41013-hyperbola-prime-moments)

<a id="p13-chebyshev-tailmertens"></a>

### 4.10.14 The elementary Chebyshev supply for TailMertens

#### Motivation

The logarithmically weighted Mertens bound in the prime-moment argument uses a linear bound on the unweighted prefix of von Mangoldt coefficients. For this purpose the constant must be uniform even at the first few integers. The pinned Mathlib proof bounds the prime contribution by reducing the primorial to roughly half its scale, then recovers the higher prime powers by grouping them by exponent.

#### Two calculations across jumps

Let $P(n)$ denote the product of primes up to $n$. We write sums of logarithms as logarithms of integer products.

**Crossing the cube $2^3$.** At $x=15/2$ the nonzero entries are $2,3,4,5,7$, contributing the logarithm of $2\cdot3\cdot2\cdot5\cdot7=420$. At $x=8$ the new entry contributes $\log 2$, so $\psi(8)=\log840$. At $x=17/2$ the floor is still $8$. The disjoint blocks $(4,8],(2,4],(1,2]$ contain respectively $5,7,8$; $3,4$; and $2$ among the nonzero entries. The block products are $70,6,2$, with product $840$. The prefix up to $1$ contributes zero. Grouping instead by exponent gives $\log210+\log2+\log2$ since the floor cutoffs for exponents $1,2,3$ are $8,2,2$ and $2^4>8$.

The primorial reduction is $8\to7\to4\to3\to2\to1$, with successive ratios $1,35,1,3,2$ and total product $210$. The odd reductions use $35\mid\binom73=35\le4^3$ and $3\mid\binom31=3\le4$. The terminal ratio is $P(2)/P(1)=2$.

**Crossing the square $3^2$.** At $x=17/2$ the nonzero entries $2,3,4,5,7,8$ contribute the logarithm of $2\cdot3\cdot2\cdot5\cdot7\cdot2=840$. At $9$ the new entry contributes $\log 3$, so $\psi(9)=\log2520$. At $x=19/2$ the floor is still $9$. The blocks $(9/2,9],(9/4,9/2],(9/8,9/4]$ contain respectively $5,7,8,9$; $3,4$; and $2$ among the nonzero entries. Their products are $210,6,2$, with product $2520$. The remaining prefix stops at $9/8<2$. The exponent cutoffs are $9,3,2$, giving $\log210+\log6+\log2$, and again $2^4>9$.

Here the primorial reduction is $9\to5\to3\to2\to1$, with ratios $7,5,3,2$ and total product $210$. The odd reductions use $7\mid\binom94=126\le4^4$, $5\mid\binom52=10\le4^2$, and $3\mid\binom31=3\le4$.

#### Definitions and the half-scale lemma

Define $\Lambda(p^k)=\log p$ for a prime $p$ and an integer $k\ge1$, and set $\Lambda(n)=0$ at all other nonnegative integers. For $x\ge0$, let $N=\lfloor x\rfloor$. Write $\psi(x)=\sum_{1\le n\le N}\Lambda(n)$ and $\theta(x)=\sum_{p\le N}\log p$. For an integer $n$, the conditions $n\le N$ and $n\le x$ are equivalent. Hence $\psi(x)=\psi(N)$ and $\theta(x)=\log P(N)$, with the empty product equal to $1$. Both sums vanish on $0\le x<2$ since $\Lambda(1)=0$.

**Lemma (the primorial bound) [Lean, read].** For every integer $n\ge0$, $P(n)\le4^n$. Consequently $\theta(x)\le(\log4)x$ for every real $x\ge0$.

**Proof.** For integers $a\ge b\ge0$, every prime $a<p\le a+b$ divides $(a+b)!$ and divides neither $a!$ nor $b!$. The identity $(a+b)!=\binom{a+b}{a}a!b!$ and primality imply that $p$ divides the binomial coefficient. The distinct primes in that interval are coprime, so their product divides that coefficient. The factorization of the primorial over the two disjoint prime sets thus gives $P(a+b)\le P(a)\binom{a+b}{a}$.

For odd $n=2m+1$ with $m\ge1$, use $a=m+1$, $b=m$. By reflection, the binomial row with top index $2m+1$ has equal sums in its two halves. The binomial theorem gives total $2^{2m+1}$, so each half sums to $4^m$. The central entry $\binom{2m+1}{m+1}=\binom{2m+1}{m}$ is at most $4^m$. Strong induction now gives $P(2m+1)\le P(m+1)4^m\le4^{2m+1}$. In log weight the interval $(m+1,2m+1]$ costs at most $m\log4$. Its lower endpoint is already in the shorter prefix.

For even $n>2$, $n$ is composite, giving $P(n)=P(n-1)\le4^{n-1}\le4^n$. The base values are $P(0)=P(1)=1$ and $P(2)=2$. This supplies every integer case including the adjustment for the even step. Taking logarithms at $N=\lfloor x\rfloor$ gives $\theta(x)\le N\log4\le x\log4$. [Pinned source record](../sources/SOURCES.md#chapter-4-41014-elementary-chebyshev-supply)

#### The prime-power bound

**Theorem (elementary Chebyshev upper bound) [Lean, read].** For every real $x\ge0$, $\psi(x)\le(\log4+4)x$.

**Proof.** For $0\le x<2$ the assertion follows from vanishing. For $x\ge2$ put $K=\lfloor\log x/\log2\rfloor$. Every prime power $p^k\le x$ has $2^k\le x$, hence $1\le k\le K$. At a fixed $k$ the condition is equivalent to $p\le\lfloor x^{1/k}\rfloor$. The upper endpoint is included even when $x=p^k$. Unique factorization makes the map $(p,k)\mapsto p^k$ injective, so
$\psi(x)=\sum_{k=1}^{K}\theta(x^{1/k})$.
Each term counts its primes with weight $\log p$. There are $K-1$ terms after the $k=1$ term, and each is at most $(\log4)\sqrt x$ by the lemma and $1/k\le1/2$. Thus $\psi(x)-\theta(x)\le(K-1)(\log4)\sqrt x\le 2\sqrt x\log x$, by $\log4=2\log2$. The lemma then gives $\psi(x)\le(\log4)x+2\sqrt x\log x$.

For $u\ge1$ the integral of $1/t$ on $[1,u]$ gives $\log u\le u-1\le u$. For $u=\sqrt x$ this yields $\log x\le2\sqrt x$, so the second term costs at most $4x$. The pinned proof makes its outer split at $x=1$ and handles $1\le x<2$ by vanishing inside the estimate for $\psi-\theta$. For $x<0$ Mathlib's natural floor is truncated to zero and the displayed bound fails because its right side is strictly negative. [Pinned source record](../sources/SOURCES.md#chapter-4-41014-elementary-chebyshev-supply)

#### Endpoint failures and the consumer

At $x=8$ omitting higher powers changes $\log840$ to $\log210$, losing exactly $2\log2$ from $4$ and $8$. At $x=9$ using a strict upper cutoff changes $\log2520$ to $\log840$, losing $\log3$. Using open intervals at both ends in the first block decomposition loses $8,4,2$, dropping the product to $105$. Closing both ends counts $4$ and $2$ twice. These are failures of the sum identities that identify the quantity to be bounded.

**Corollary (the call in `tail_mertens_psi`) [Lean, read].** For every $N\in\mathbb N$, including $N=0$, $\sum_{1\le n\le N}\Lambda(n)\le cN$, where $c=\log4+4$.

**Proof.** Specialize to the nonnegative real cast of $N$, whose natural floor is $N$. The archive rewrites the sum on $0,\ldots,N$ and uses $\Lambda(0)=0$ to remove the initial term. This gives `TailMertens.lean:9–24`.

The inherited `tail_mertens_nat` uses the bound on intermediate prefixes, and `tail_mertens` uses it again on the terminal prefix. For every real $y\ge2$ the resulting budget is $\sum_{1\le n\le\lfloor y\rfloor}\Lambda(n)/n\le C_{\mathrm{Mer}}\log y$ with $C_{\mathrm{Mer}}=(\log4+4)(1+1/\log2)$. This is the witness passed at `TailFinal.lean:16` and `PNTDHPrime.lean:155`. The prime-moment proof uses this budget on the initial segment. Its resulting *DHPrime* witness enters the Turán finish. [§4.10.13](#p13-dh-prime) · [§4.10.12](#p13-turan-finish)

**Source note.** Tao's *254A Notes 1*, Proposition 12, proves the all-$x$ order bound with the even row $\binom{2N}{N}$ on $(N,2N]$ and a separate count of proper powers. The exact constant here follows Mathlib's odd-row primorial estimate and exponent grouping. The reading tag applies to this local production chain and the natural-number wrapper. The mathematical text inherits the original same-source preliminary review of the two elementary estimates and the natural-number specialization. [Sources and credits](../sources/SOURCES.md#chapter-4-41014-elementary-chebyshev-supply)

### 4.10.15 The Chebyshev lower bound from least common multiples

#### Motivation

An upper estimate limits how much prime weight a prefix can contain. For a lower estimate we need a large integer whose prime factors, including their multiplicities, fit inside that prefix. The least common multiple of $1,\ldots,n$ supplies that budget. Each entry of the $n$th binomial row fits inside it by divisibility, while the sum of the row is $2^n$.

#### Two worked calculations [Expository]

At $n=8$ the prime powers in the prefix are $2,4,8$ over $2$, and $3,5,7$ over the remaining primes. Their largest powers give $L_8=8\cdot3\cdot5\cdot7=840$. Each power contributes the logarithm of its base, so $\psi(8)=3\log 2+\log 3+\log 5+\log 7=\log 840$. At $n=12$ the lists are $2,4,8$ over $2$, $3,9$ over $3$, and $5,7,11$ over the remaining primes. Thus $L_{12}=8\cdot9\cdot5\cdot7\cdot11=27720$ and $\psi(12)=3\log 2+2\log 3+\log 5+\log 7+\log 11=\log 27720$.

For $n=2m$, the contribution at the power $q=p^i$ to the valuation of the central coefficient is $\lfloor n/q\rfloor-2\lfloor m/q\rfloor$. The following table gives every nontrivial power cutoff, including the cutoffs whose contribution vanishes. Powers beyond the row index contribute zero.

| Row | Prime | Powers $q$ in order | Quotients $\lfloor n/q\rfloor$ | Quotients $\lfloor m/q\rfloor$ | Differences | Valuation available in $L_n$ |
|---|---|---|---|---|---|---|
| $8$ | $2$ | $2,4,8$ | $4,2,1$ | $2,1,0$ | $0,0,1$ | $3$ |
| $8$ | $3$ | $3$ | $2$ | $1$ | $0$ | $1$ |
| $8$ | $5$ | $5$ | $1$ | $0$ | $1$ | $1$ |
| $8$ | $7$ | $7$ | $1$ | $0$ | $1$ | $1$ |
| $12$ | $2$ | $2,4,8$ | $6,3,1$ | $3,1,0$ | $0,1,1$ | $3$ |
| $12$ | $3$ | $3,9$ | $4,1$ | $2,0$ | $0,1$ | $2$ |
| $12$ | $5$ | $5$ | $2$ | $1$ | $0$ | $1$ |
| $12$ | $7$ | $7$ | $1$ | $0$ | $1$ | $1$ |
| $12$ | $11$ | $11$ | $1$ | $0$ | $1$ | $1$ |

It follows that $\binom{8}{4}=2\cdot5\cdot7=70$ with $840/70=12$, and $\binom{12}{6}=2^2\cdot3\cdot7\cdot11=924$ with $27720/924=30$. The row-average budgets are $256\le9\cdot70=630\le9\cdot840=7560$ and $4096\le13\cdot924=12012\le13\cdot27720=360360$. The average, middle entry and LCM therefore give three distinct quantities in each example.

#### Definitions and the LCM identity

Let $n$ be a nonnegative integer and set $L_n=\operatorname{lcm}(1,\ldots,n)$, with $L_0=1$. For a positive integer $a$ and prime $p$, write $v_p(a)$ for the exponent of $p$ in $a$. Let $e_p(n)$ be the number of positive integers $i$ with $p^i\le n$. This is the integer base logarithm given by the Lean expression $p\texttt{.log}\,n$ (an integer base-$p$ logarithm with value zero when $n<p$). Throughout the analytic formulas $\log$ is the real natural logarithm.

Use $\Lambda(p^i)=\log p$ for $i\ge1$ and $\Lambda(m)=0$ elsewhere, including $m=0,1$. For $x\ge0$ use $N=\lfloor x\rfloor$, with $\psi(x)=\sum_{1\le m\le N}\Lambda(m)$, $\theta(x)=\sum_{p\le N}\log p$ and $\pi(N)$ the number of primes up to and including $N$.

**Lemma (prime powers in the LCM) [Lean, read].** For every $n\ge0$ and every prime $p$, $v_p(L_n)=e_p(n)$. In particular
$$
L_n=\prod_{p\le n}p^{e_p(n)},\qquad
\psi(n)=\log L_n=\sum_{p\le n}e_p(n)\log p .
$$

**Proof.** The valuation of the LCM is the maximum of the valuations over the prefix, with empty maximum zero. Indeed the product of the prime powers with these maximum exponents is a common multiple and divides every positive common multiple. If $1\le m\le n$ then $p^{v_p(m)}\mid m$, so $p^{v_p(m)}\le n$. If $p\le n$, the integer $p^{e_p(n)}$ lies in the prefix and attains the asserted valuation. If $p>n$, the valuation is zero throughout. This proves the product formula. The support of $\Lambda$ in the prefix is the disjoint union of the lists $p,p^2,\ldots,p^{e_p(n)}$. Unique factorization separates the bases, and powers within one list are strictly increasing. Each list contributes $e_p(n)\log p$, which is the logarithm of its factor in the product. The empty sum and product handle $n=0,1$. The floor identity extends this to $\psi(x)=\log L_{\lfloor x\rfloor}$ for all $x\ge0$. [Pinned source record](../sources/SOURCES.md#chapter-4-41015-chebyshev-lower-bound-from-lcms)

#### Binomial divisibility and the whole row

**Lemma (one unit of valuation per cutoff) [Lean, read].** For every $n\ge0$ and every integer $0\le k\le n$, $\binom nk\mid L_n$. Consequently $2^n\le(n+1)L_n$.

**Proof.** In $a!$, count one contribution to $v_p$ for each multiple of each $q=p^i$ with $i\ge1$. This gives $v_p(a!)=\sum_{i\ge1}\lfloor a/p^i\rfloor$, with finitely many nonzero terms. Apply the identity $\binom nk\,k!(n-k)!=n!$. If $r$ and $s$ are the respective remainders of $k$ and $n-k$ modulo $q$, the difference of the three factorial quotients for this $q$ is
$$
\left\lfloor \frac{n}{q}\right\rfloor-
\left\lfloor \frac{k}{q}\right\rfloor-
\left\lfloor \frac{n-k}{q}\right\rfloor
=\left\lfloor \frac{r+s}{q}\right\rfloor .
$$
As $0\le r+s\le2q-2$, the difference is zero or one, and it is zero if $q>n$. Thus $v_p(\binom nk)\le e_p(n)$ for every prime $p$. Both integers are positive, so the valuation inequalities imply divisibility. For the row bound, sum $\binom nk\le L_n$ over all $n+1$ indices, using the binomial theorem. The central coefficient is also at least the row average by unimodality, which follows from the ratio $(n-k)/(k+1)$ of successive entries. The pinned proof sums the individual bounds directly and needs no unimodality lemma. [Pinned source record](../sources/SOURCES.md#chapter-4-41015-chebyshev-lower-bound-from-lcms)

#### From the row to the lower bounds

**Theorem (source bounds and their ranges) [Lean, read].** Put $A(n)=n\log2-\log(n+1)$ and $B(x)=(x-1)\log2-\log(x+2)$. The declarations `psi_ge` and `psi_ge'` give
$$
A(n)\le\psi(n)\quad(n\in\mathbb N),\qquad
B(x)\le\psi(x)\quad(x\in\mathbb R, x\ge0).
$$
The declarations `theta_ge` and `theta_ge'` give $A(n)-2\sqrt n\log n\le\theta(n)$ for every $n\in\mathbb N$ and $B(x)-2\sqrt x\log x\le\theta(x)$ for every real $x\ge1$. In the natural-number statement the product involving $\log 0$ is interpreted as zero at $n=0$, as in Lean. Finally `pi_ge` gives $A(n)/\log n\le\pi(n)$ for every $n\in\mathbb N$ using Lean's zero quotient at $n=0,1$. The ordinary real quotient bound `pi_ge'` is $B(x)/\log x\le\pi(\lfloor x\rfloor)$ for $x>1$.

**Proof.** Take logarithms of the row inequality with both arguments positive. This gives $n\log2\le\log(n+1)+\log L_n$. For real $x\ge0$, $x-1<\lfloor x\rfloor\le x$ implies $B(x)\le A(\lfloor x\rfloor)\le\psi(x)$, since $\log2>0$ and $\lfloor x\rfloor+1\le x+2$. The estimate with the floor left in place is stronger. For $\theta$, subtract the inherited proper-power budget $0\le\psi(x)-\theta(x)\le2\sqrt x\log x$ for $x\ge1$. Use the stronger natural bound on integers $n\ge1$ and check $n=0$ by the empty sum. For the prime count at $x>1$, each $p\le N=\lfloor x\rfloor$ contributes $e_p(N)\log p\le\log x$ since $p^{e_p(N)}\le N\le x$. Sum and divide by the positive $\log x$. At integers $n\ge2$ use $A(n)$ in the same argument. The cases $n=0,1$ of the totalized statement reduce to zero on both sides. [Pinned source record](../sources/SOURCES.md#chapter-4-41015-chebyshev-lower-bound-from-lcms)

#### Boundary checks and the meaning of the estimate

**Small scales [Expository].** The integer lower bound has equality at $n=0,1$ and is positive at every $n\ge2$, since $2^2>3$ and $2(n+1)\ge n+2$. On $0<x<2$ we have $\psi(x)=0$, so the pure inequality $c x\le\psi(x)$ fails for every $c>0$. The floor bound is already positive at $x=2$. The relaxed real expression $B$ has exactly one zero on $[0,\infty)$, lying in $(3,4)$. It is strictly increasing because $B'(x)=\log2-1/(x+2)>0$, using $\log2=\int_1^2dt/t>1/2$, and $B(3)=\log(4/5)<0<B(4)=\log(8/6)$. Its delay is a cost of the relaxation.

For a uniform pure comparison from $x=2$ onward one may take $c=\tfrac14\log(4/3)$. The function $\log(1+t)/t=\int_0^1 (1+ts)^{-1}\,ds$ decreases for $t>0$. Hence for $n\ge2$, $A(n)/n\ge\log2-\tfrac12\log3$. With $n=\lfloor x\rfloor\ge x/2$ for $x\ge2$, the asserted $c$ follows. This constant is an expository consequence. The pinned statements use the error terms above.

The conditions also guard the proof itself. At $n=8,k=9$ the binomial coefficient is zero and does not divide $840$. At $x=-31/16$, the natural floor is zero and $\psi(x)=0$, while $B(x)=(17/16)\log2>0$. Even the relaxed real $\theta$ bound can fail below its stated domain. At $x=1/4$ its left side is $\tfrac54\log2-\log(9/4)>0$ since $2^5>(9/4)^4$, and $\theta(1/4)=0$.

**What the two estimates determine [Expository].** With the upper bound of [§4.10.14](#p13-chebyshev-tailmertens), $\psi$ has linear order of growth. Dividing the real lower bound by $x$ gives a lower limit at least $\log2$, and the inherited upper bound gives an upper limit at most $\log4+4$. The proper-power budget is $o(x)$, so $\theta$ also has linear order. The prime-counting lower bound gives order at least $x/\log x$. For an upper bound, at most $\sqrt x$ primes lie up to $\sqrt x$, and the rest have weight at least $\tfrac12\log x$ in $\theta(x)$, so $\pi(\lfloor x\rfloor)\le\sqrt x+2\theta(x)/\log x$ for $x>1$. The PNT requires $\psi(x)/x\to1$, equivalently $\pi(\lfloor x\rfloor)\log x/x\to1$. The bounds here leave a fixed interval for the limiting coefficient. Even the model functions $x$ and $2x$ satisfy the two displayed real inequalities for $\psi$ on $x\ge0$, since $B(x)<0$ on $[0,1]$, $B(x)<(x-1)\log 2<x$ for $x>1$, and $\log4+4>2$, while their normalized values differ. [Tao, Proposition 31](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/#equi-2)

#### Consumer boundaries

| Input | Verified consumer and contract | Scope |
|---|---|---|
| $L_n$ valuation and all-entry binomial bound | Mathlib `two_pow_le_mul_lcmUpto` and `psi_ge`, all $n\in\mathbb N$ | New local reading |
| $\psi$ lower bound | Mathlib `theta_ge`, `theta_ge'` via the proper-power budget, and `pi_ge`, `pi_ge'` via the positive logarithm split | New local reading of the calls |
| Exact $\psi=\log L$ identity | A2 `psi_le_of_lt_thirty` uses $L_n\le3^n$ for $n<30$ to obtain $\psi(x)\le1.1056x$ for $0\le x<30$. A2 `psi_le_two_mul_small` uses $L_n\le4^n$ for $n\le100$ to obtain $\psi(x)\le2x$ for $0\le x\le100$. | Actual identity calls in finite **upper** bounds |
| $\psi(x)\le(\log4+4)x$ for $x\ge0$ | A2 `tail_mertens_psi` takes every natural prefix, including zero. The Mertens budget for $y\ge2$ passes to the existing prime-moment and tail consumers. | Inherited §4.10.14 and its same-source review, with downstream reviews as recorded in §§4.10.12–4.10.13 |
| Relative PNT and Deuring–Heilbronn | The LCM lower inequality has no identified direct A2 call in the reviewed snapshot. The upper input to the Mertens argument is the row above. | Inherited analytic material |

The A2 finite upper calls share the LCM identity and have separate finite premises. The textbook proof above follows the pinned Mathlib valuation and lower-bound declarations. [Sources and credits](../sources/SOURCES.md#chapter-4-41015-chebyshev-lower-bound-from-lcms)

The local author-level source reading inherits the same-source preliminary ruling 11251451. The exact certificate covers the two worked rows and small-scale boundaries. Independent review and Lean kernel replay remain open.

### 4.10.16 The Costa–Pereira comparison

#### Motivation

The primorial bound controls the total weight of primes. The LCM bound of [§4.10.15](#41015-the-chebyshev-lower-bound-from-least-common-multiples) gives a lower estimate for the total weight of prime powers. To pass from prime powers to primes, one needs a third estimate: the weight removed by discarding proper powers. Costa Pereira's regrouping isolates the square and cube scales with a correction for their overlap. Together with the linear upper bound of [§4.10.14](#p13-chebyshev-tailmertens) it improves the earlier $O(\sqrt{x}\log x)$ budget to $O(\sqrt{x})$.

#### Two hand calculations [Expository]

For integer $n$, let $F_j$ be the largest integer with $F_j^j\le n$ and set $B_j=\prod_{p\le F_j}p$, with the product over primes. All terms from $j=8$ onward have $B_j=1$ in these examples, since $2^8>128$.

| $n$ | $(F_2,F_3,F_4,F_5,F_6,F_7)$ | $(B_2,B_3,B_4,B_5,B_6,B_7)$ |
|---|---|---|
| $63$ | $(7,3,2,2,1,1)$ | $(210,6,2,2,1,1)$ |
| $64$ | $(8,4,2,2,2,1)$ | $(210,6,2,2,2,1)$ |
| $127$ | $(11,5,3,2,2,1)$ | $(2310,30,6,2,2,1)$ |
| $128$ | $(11,5,3,2,2,2)$ | $(2310,30,6,2,2,2)$ |

For $63,64$, the square and cube cutoffs change at $8^2=4^3=64$, and the sixth cutoff changes at $2^6=64$. The fourth and fifth cutoffs are $2$ since $2^4=16$, $2^5=32$ and $3^4=81$. The seventh cutoff is $1$. For $127,128$ the square bounds are $11^2=121$ and $12^2=144$, the cube bounds are $5^3=125$ and $6^3=216$, and the fourth bounds are $3^4=81$ and $4^4=256$. The fifth and sixth cutoffs are $2$ since $2^6=64$ and $3^5=243$. The seventh cutoff changes at $2^7=128$. The products for cutoffs $7,8$ are $2\cdot3\cdot5\cdot7=210$, and the product for $11$ is $210\cdot11=2310$.

**Across $2^6$.** In product form the gap is $\prod_{j\ge2}B_j$. The square and cube factors are $B_2B_4B_6$ and $B_3B_6$. At $63$ the gap is $210\cdot6\cdot2\cdot2=5040$, the square and cube factors are $420$ and $6$, and the correction factor is $B_5B_7/B_6=2$. Thus the sandwich is $2520\le5040\le5040$. At $64$ these factors are $840$, $12$, and $1$, with gap $10080$. The sandwich is $10080\le10080\le20160$. The sixth power contributes twice to the square and cube factors together, and the denominator removes one copy.

**Across $2^7$.** At $127$ the gap product is $2310\cdot30\cdot6\cdot2\cdot2=1663200$, the square factor is $2310\cdot6\cdot2=27720$, and the cube factor is $30\cdot2=60$. The correction is $2\cdot1/2=1$, giving $1663200\le1663200\le3326400$. At $128$ the square and cube factors stay fixed, the correction is $2\cdot2/2=2$, and the gap doubles. Both bounds equal $3326400$. Taking logarithms gives the additive comparisons.

#### Definitions and cutoff

Write $\theta(y)=\sum_{p\le y}\log p$ and $\psi(y)=\sum_{p^j\le y,\ j\ge1}\log p$, with $p$ prime. Mathlib uses the natural floor $\lfloor y\rfloor_+=\max(0,\lfloor y\rfloor)$. Both sums vanish for $y<2$. For $x\ge0$ and positive integer $j$, set $b_j=\theta(x^{1/j})$. Since positive integer powers are increasing on the nonnegative axis,
$$
p\le\lfloor x^{1/j}\rfloor_+
\quad\Longleftrightarrow\quad p^j\le x
\quad\Longleftrightarrow\quad p^j\le\lfloor x\rfloor_+.
$$
Taking the natural floor before the root therefore gives the same prime cutoff as taking it after the root. The inequalities include the endpoint.

**Lemma (finite exponent reindexing) [Lean, read].** For every real $x\ge0$ and integer $d\ge1$, put $M_d=\lfloor\log(x^{1/d})/\log2\rfloor_+$. For every natural $N\ge M_d$,
$$
\psi(x^{1/d})=\sum_{k=1}^N b_{dk}.
$$
The sequence $b_j$ is nonincreasing for $j\ge1$.

**Proof.** Write $y=x^{1/d}$. For $y<2$, every prime-power term and every term of the exponent sum vanishes. This includes zero, where Mathlib sets $\log0=0$. For $y\ge2$, each $p^k\le y$ implies $2^k\le y$ and hence $k\le M_d$. The pair $(k,p)$ is uniquely determined by $p^k$ by unique prime factorization. Every prime power in the prefix has such a pair, with weight $\log p$. At fixed $k$ the prime cutoff is $\lfloor y^{1/k}\rfloor_+$. The exponential definition gives $y^{1/k}=x^{1/(dk)}$ for positive $x$, and both powers vanish at zero. This proves the reindexing. For $0\le x\le1$, all $b_j$ are zero. For $x>1$, the exponents $1/j$ decrease, so the root arguments decrease and monotonicity of $\theta$ gives the claim. [Source ledger](../sources/SOURCES.md#chapter-4-41016-the-costapereira-comparison)

#### Proposition (six-term regrouping and comparison) [Lean, read]

For every $x\ge0$ put $c_m=b_{6m-1}-b_{6m}+b_{6m+1}$ for integers $m\ge1$ and $N=M_1+M_2+M_3+M_5+M_7$. Then
$$
\psi(x)-\theta(x)=\psi(x^{1/2})+\psi(x^{1/3})+\sum_{m=1}^N c_m .
$$
Set $S_j(x)=\psi(x^{1/2})+\psi(x^{1/3})+\psi(x^{1/j})$. Then
$$
S_7(x)\le\psi(x)-\theta(x)\le S_5(x),
\qquad
\psi(x)-S_5(x)\le\theta(x)\le\psi(x)-S_7(x).
$$
The upper bound on the gap holds for all real $x$ with Mathlib's real powers.

**Proof.** For every natural $N$ the finite identity is
$$
\sum_{j=1}^{1+6N} b_j
=b_1+\sum_{k=1}^{3N}b_{2k}+\sum_{k=1}^{2N}b_{3k}+\sum_{m=1}^N c_m .
$$
At $N=0$ both sides equal $b_1$. Appending the block numbered $m=N+1$ adds the indices $6m-4$ through $6m+1$. The even terms contribute $6m-4,6m-2,6m$, and the multiples of three contribute $6m-3,6m$. The correction adds $6m-1$ and $6m+1$ and subtracts one copy of $6m$. This is the induction implemented by extending inclusive finite intervals at their upper endpoint. The index subtraction is ordinary since $m\ge1$. With the prescribed $N$, the lengths $1+6N$, $3N$, $2N$, $N$ and $N$ dominate $M_1$, $M_2$, $M_3$, $M_5$ and $M_7$ respectively. The reindexing lemma and $b_1=\theta(x)$ give the exact identity.

For $m\ge1$, the inequalities $5m\le6m-1<6m<6m+1\le7m$ give
$$
b_{7m}\le b_{6m+1}\le c_m\le b_{6m-1}\le b_{5m}.
$$
The middle inequalities use $b_{6m-1}-b_{6m}\ge0$ and $b_{6m+1}-b_{6m}\le0$. Sum over $1\le m\le N$ and reindex at $d=5,7$. Rearranging gives the $\theta$ bounds. For negative $x$ the gap is zero and $S_5(x)$ is nonnegative. [Source ledger](../sources/SOURCES.md#chapter-4-41016-the-costapereira-comparison)

#### Boundaries and consumers

At $x=255/4$, rounding the sixth root to the nearest integer admits $2$, since $(3/2)^6<255/4<2^6$. The resulting term $\log2$ should be zero. At $64$ the strict cutoff $p^6<x$ loses the legitimate endpoint term. Using $p^j\le x$ directly preserves exactly the floored sum. Reversing the minus sign on $b_{6m}$ in the identity makes its right side too large by $2\log2$ at $64$.

The lower bound needs a sign restriction in the pinned convention. At $x=-64$, Mathlib gives $x^{1/3}=64^{1/3}\cos(\pi/3)=2$. Thus $S_7(x)\ge\log2>0=\psi(x)-\theta(x)$. [Pinned real powers](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L95)

**Corollary (square-root budget) [Lean, read].** For every real $x$, $0\le\psi(x)-\theta(x)\le3(\log4+4)\sqrt{x}$, with Mathlib's nonnegative square root. The first inequality follows by inclusion of prime terms. For $x\le1$ the gap vanishes. For $x>1$ the three roots in $S_5(x)$ lie between $0$ and $\sqrt{x}$. Apply the inherited estimate $\psi(y)\le(\log4+4)y$ to each. Nonnegativity also gives the norm bound at infinity.

| Verified consumer | Contract |
|---|---|
| Mathlib square-root and big-O lemmas | Use the upper root estimate and the linear upper bound, then take the absolute-value bound at infinity. |
| A2 dyadic prime intervals, psiTheta | For $x\ge1$, monotonicity puts the cubic and fifth-root weights below the square-root weight, yielding $\psi(x)-\theta(x)\le3\psi(\sqrt{x})$. The dyadic claim calls this wrapper. |
| A2 Iwasawa decomposition, psi_le_of_le_sqrt | For $x\ge1$, $C\ge0$ and $\psi(y)\le Cy$ on $0\le y\le\sqrt{x}$, the upper root estimate and primorial bound give $\psi(x)\le1.4x+3C\sqrt{x}$. This supplies the large-scale step of the archive's $\psi(y)\le2y$ argument. |
| A2 prime norms, normPrimes_short_interval_lower | Applies the square-root budget at $X(1+h)$ with $X\ge1$ and $0<h\le1$ to absorb the proper-power contribution in a short-interval count. |
| Chapter 4 relative prime count and prime moments | The identified PNTPiA and PsiAPLeCount calls use the earlier logarithmic budget. TailMertens uses the inherited linear upper bound for $\psi$. |

The three upper-side calls above are present in A2. The lower root inequality is established in Mathlib, and the scoped A2 search found no direct caller. [Source ledger](../sources/SOURCES.md#chapter-4-41016-the-costapereira-comparison)

The local author-level source reading inherits the same-source preliminary ruling 11251609. The 85 exact checks cover finite instances. Direct inspection of the 1985 article and 1987 corrigendum, independent review of this section, and Lean kernel replay remain open.

### 4.10.17 A strict prime count in a real dyadic interval

#### Motivation

A lower bound for the weight of prime powers can supply primes in $(y,2y]$ once we subtract the weight of proper powers at the upper endpoint. To get a count, we then divide by the largest weight a single prime could contribute. The archive needs this quantitative step in its count of squarefree polynomials over finite fields.

#### Examples [Expository]

* At $y=41/2$, the integers in the interval run from $21$ through $41$. The primes are $23,29,31,37,41$. The even entries are composite, and the remaining odd nonprimes are $21,25,27,33,35,39$. Thus $\pi(41)-\pi(20)=13-8=5$. The weight $\psi(41)-\psi(41/2)$ includes, in addition, $25,27,32$, with total extra weight $\log 5+\log 3+\log 2=\log 30$. Since $\log(41/2)>\log16>4(0.69)$, the count exceeds $3y/(5\log y)$ by more than $5-12.3/2.76>0$. Opening the right endpoint loses $41$, leaving four primes. Since $\log(41/2)<3.075$, four fails the claimed lower bound.
* At $y=43/2$, the integers run from $22$ through $43$. The primes are $23,29,31,37,41,43$. Trial division by $2,3,5$ suffices since $43<49$. Thus $\pi(43)-\pi(21)=14-8=6$. The same proper powers contribute $\log30$. The half-open interval still contains six primes for every $43/2\le y<22$ by the floor identity below. Throughout that cell $3y/(5\log y)<13.2/2.76<5$, so the margin exceeds one prime. At $y=23$ the strict lower endpoint excludes $23$. The primes in $(23,46]$ are $29,31,37,41,43$. Counting on $[23,46]$ would give six.

#### Definitions

Let $\pi(n)$ count the primes at most $n$, and let $\lfloor x\rfloor_+$ be the natural floor. Set $N(y)=\pi(\lfloor 2y\rfloor_+)-\pi(\lfloor y\rfloor_+)$ for $y\ge1$. It counts exactly the primes $p$ with $y<p\le2y$. Define the two envelopes
$$
U(t)=1.1056t+0.7(\log t)^2,\qquad V(t)=0.92129t-\tfrac52\log t.
$$
Write $B(y)=3y/(5\log y)$ and $R(y)=V(2y)-3U(\sqrt{2y})-U(y)-B(y)\log(2y)$ on $y>1$.

#### Lemma and proof [Lean, read]

For $y\ge41/2$, the assembly `PI.PrimesDyadicRS.W.claim_of_two` gives $N(y)>B(y)$ from these two inputs:

1. For every integer $41\le h<131072$, put $d_h=\pi(h)-\pi(\lfloor h/2\rfloor)$. Then $3(h+1)<10d_h\log(h/2)$.
2. For every real $y\ge65536$, $R(y)>0$.

The archive supplies both inputs to obtain `primes_dyadic_range`. For every $y\ge41/2$ this gives a nonempty set of primes in $(y,2y]$, since $N(y)>B(y)>0$.

**Proof of the assembly.** Write $h=\lfloor 2y\rfloor_+$ and divide the inequalities $h\le2y<h+1$ by two. If $h=2k$ the resulting cell lies in $[k,k+1/2)$, and if $h=2k+1$ it lies in $[k+1/2,k+1)$. In both cases $\lfloor y\rfloor_+=\lfloor h/2\rfloor$, so $N(y)=d_h$. Below $65536$, $41\le h<131072$. The first input forces $d_h>0$, and
$$
5N(y)\log y\ge5d_h\log(h/2)>\tfrac32(h+1)>3y.
$$
This proves the claim in the whole real cell, including its left endpoint.

For $y\ge65536$ use the archive's envelopes $\psi(t)\le U(t)$ for $t\ge1$ and $\psi(t)\ge V(t)$ for $t\ge30$. Their production uses the factorial quotient described below. The Costa–Pereira upper comparison of [§4.10.16](#41016-the-costapereira-comparison) gives, for $x\ge1$, $\psi(x)-\theta(x)\le3\psi(\sqrt{x})$, since the cubic and fifth roots are at most $\sqrt{x}$ and $\psi$ is increasing. Apply this at $x=2y$. At the lower endpoint, $\theta(y)\le\psi(y)$. Finally, summing $\log p\le\log(2y)$ over the primes in the interval gives
$$
N(y)\log(2y)\ge\theta(2y)-\theta(y)
\ge V(2y)-3U(\sqrt{2y})-U(y).
$$
The second input therefore gives $N(y)-B(y)\ge R(y)/\log(2y)>0$. The error paid is at the upper endpoint only. [Source ledger](../sources/SOURCES.md#chapter-4-41017-a-strict-prime-count-in-a-real-dyadic-interval)

#### Proof of the two inputs

**The finite input [Lean, read].** Start with $d_2=1$. When $h$ is replaced by $h+1$, add the primality indicator of $h+1$ and, if $h+1$ is even, subtract that of $(h+1)/2$. These are the changes at the two ends. The latter prime, when present, belonged to the old interval since $h\ge2$, so natural subtraction agrees with ordinary subtraction. A candidate $m$ passes the archive's primality test if it is coprime to $(m-1)!$ for $2\le m\le362$, and to $362!$ for $362<m<363^2$. A composite in the second range has a prime divisor at most $362$, and a prime in that range has none. All candidates in the loop lie in the tested ranges.

For $d=d_h>0$, let
$$
q=\left\lfloor\frac{7680000000000(h+1)}{10d\cdot6931471803}\right\rfloor.
$$
The checked integer test is $2^{q+257}\le h^{256}$. Taking logs and subtracting $256\log2$ gives $(q+1)\log2\le256\log(h/2)$. The floor gives $256\cdot 3(h+1)<10d(q+1)\cdot0.6931471803$. Since $0.6931471803<\log2$, the desired strict bound follows. The four kernel-decided runs start at $h=2,32768,65536,98304$ and terminate at $32768,65536,98304,131072$. Their endpoint counts are $1612,3030,4388,5709$, respectively. Each run tests its initial state through the state just before its terminal state, skipping the inequality for $h<41$. The recurrence and the endpoint checks chain the four runs and cover every required integer.

**The real input [Lean, read].** Let $s=\sqrt y$, $L=\log y$ and $M=\log(2y)$. At $y\ge65536$ we have $s\ge256$, $L\ge16\log2>0$, $M/L\le17/16$ and $\sqrt2<1.4143$. From $\log(s/256)\le s/256-1$ and $\log2<0.6931471808$,
$$
L\le9.1+s/128,\qquad M\le9.8+s/128.
$$
The source squares these bounds and uses $s^2\ge256s$. Equivalently, dividing by $s$ first gives $L/s<0.044$ and $M/s<0.047$. Since $\log(\sqrt{2y})=M/2$, we get
$$
\frac{R(y)}{y}\ge
2(0.92129)-1.1056-\tfrac35\tfrac{17}{16}
-\frac{3(1.1056)(1.4143)}{256}
-\frac{(5/2)(0.047)}{256}
-0.7(0.044)^2-\frac{3(0.7)}4(0.047)^2>0.075.
$$
Every decimal in this comparison is an exact rational. In particular the large branch gives an explicit surplus of more than $0.075y/\log(2y)$ in the prime count, even at the join $y=65536$.

#### Notes on the estimates and their consumer

The sharper envelopes here come from the archive's factorial argument. Write $F(x)=\log(\lfloor x\rfloor_+!)$ and $D(x)=F(x)-F(x/2)-F(x/3)-F(x/5)+F(x/30)$. Expanding the factorials in von Mangoldt weights gives $D(x)=\sum_{n\le x}\Lambda(n)E(\lfloor x/n\rfloor)$, where $E(k)=k-\lfloor k/2\rfloor-\lfloor k/3\rfloor-\lfloor k/5\rfloor+\lfloor k/30\rfloor$. The function $E$ is periodic mod $30$, since $30-15-10-6+1=0$. On the residues $0,\ldots,29$, it is one on $1,2,3,4,5,7,8,9,11,13,14,17,19,23,29$ and zero elsewhere, by integer division. This yields $\psi(x)-\psi(x/6)\le D(x)\le\psi(x)$.

The archive bounds $F(t)$ for $t\ge1$ between $t\log t-t-(\log t)/2+0.9$ and $t\log t-t+(\log t)/2+1$. For the upper bound, apply the upper integer Stirling estimate at $n=\lfloor t\rfloor_+$, using the monotonicity of the normalized Stirling sequence from its value at $1$. The remainder is then at most $1$ in the formula $n\log n-n+(\log n)/2$. The latter expression is increasing on $[1,\infty)$, so replace $n$ by $t$. For the lower bound, apply the lower integer Stirling estimate at $m=n+1$ and subtract $\log m$. This gives $H(m)+(\log(2\pi))/2$, where $H(u)=u\log u-u-(\log u)/2$. For $t\ge3/2$ the derivative $\log t-1/(2t)$ is nonnegative, by $\log(3/2)\ge1/3$. If $1\le t<3/2$, the inequality $\log t\le t-1$ gives $H(t)\le-1$, whereas $H(m)\ge H(2)>-1$. In both cases $H(m)\ge H(t)$, and $\log(2\pi)\ge1.8$ gives the stated lower bound. Substitution at $x,x/2,x/3,x/5,x/30$ for $x\ge30$ gives
$$
Ax-\tfrac52\log x+2\le D(x)\le Ax+\tfrac52\log x-4,
\qquad
A=\frac{\log 2}{2}+\frac{\log 3}{3}+\frac{\log 5}{5}-\tfrac{\log30}{30}.
$$
Indeed the five main terms combine to $Ax$. The additive corrections are $-1.2+\log30$ and $-0.7-\log30$, respectively, so $\log30\ge3.3$ gives the displayed bounds. With $0.92129\le A\le0.9213$ the lower envelope follows at once. For the upper envelope, start at $0\le t<30$ with $\operatorname{lcm}(1,\ldots,\lfloor t\rfloor_+)\le3^{\lfloor t\rfloor_+}$, the finite base test, and $\log3<1.1056$. For $x\ge30$ use $\psi(x)\le D(x)+\psi(x/6)$ and induct by factors of six. After substituting $U(x/6)$, the excess over $U(x)$ is bounded above by
$$
(0.9213+1.1056/6-1.1056)x
+(2.5-1.4\log6)\log x+0.7(\log6)^2-4<0
$$
using $1.7917\le\log6\le1.7918$. The LCM identity of [§4.10.15](#41015-the-chebyshev-lower-bound-from-least-common-multiples) is used in the finite base, while the general LCM lower bound and the coarser square-root budget from the preceding sections can be read independently of these sharper envelopes.

The lower range matters. At $y=3/2$ the interval contains exactly the two primes $2,3$. The bound asks for more than $0.9/\log(3/2)>2$, since $\log(3/2)<0.45$. Thus the quantitative claim fails even with $y>1$. If the range is deleted altogether, $(1/2,1]$ is empty. At the odd cell $h=41$, replacing $h/2$ as a real logarithm argument by the integer $20$ changes the finite inequality, while using $21$ for the lower counting cutoff changes the represented integer interval. At $y=41/2$ rounding the upper cutoff down to an even integer would lose the prime $41$.

In A2, `OrbitalBoundsConclusion/PrimesDyadicRS.lean:7–8` supplies `primes_dyadic_range` by passing `small_natural_numbers_bound` and `real_dyadic_inequality` to `claim_of_two`. The direct call is in `ExplicitFormulaCounts/SqfCounts.lean:43–45` in `counts_closed`, through `sqfPrimeFactor_of` and `analytic_of`. The latter passes the bound to `ana_main`, which applies it at $y=r/2$ with integer $r\ge100$. The count in $(r/2,r]$ is compared with the primes satisfying $r<2p$ and $p+3\le r$. Of the three omitted candidates $r-2,r-1,r$, at most two can be prime. [§4.10.18](#41018-counting-the-prime-degree-factor-exception) uses this endpoint budget in the fourth squarefree count.

The `CharacterBoxes` construction chooses auxiliary primes with congruence and twist restrictions through its separate `PairEx` input from `MeanSquareBounds/pairEx.lean` and its prime-pair selection calls. The dyadic estimate counts all primes. The checked consumer is the squarefree count above. The present reading establishes no transitive dependency for the host-field prime selection. [Source ledger](../sources/SOURCES.md#chapter-4-41017-a-strict-prime-count-in-a-real-dyadic-interval)

The local author-level source reading inherits the same-source preliminary ruling 11251733. The certificate covers 131,031 integer states, the segment joins and the rational surplus. The proof above transfers the finite checks to real intervals. Independent review and Lean kernel replay remain open.

### 4.10.18 Counting the prime-degree factor exception

#### Motivation

A prime in a dyadic interval gives a possible **degree** of an irreducible polynomial over the host field. A bound on the number of exceptional labels needs more. It needs enough irreducibles of those degrees, a way to count their multiples, and a guarantee that the same multiple is counted only once. Work first in the entire space of monic polynomials. This makes divisibility a count of residue classes with an exact power of the field size.

#### Two calculations at host-size parameters [Expository]

For a prime $g$ and a prime degree $p$, the number of monic irreducibles of degree $p$ is $(g^p-g)/p$. For the exact arithmetic in these examples, the lower-bound argument below can be sharpened as follows. Every monic irreducible $Q$ of degree $p$ gives a field $\mathbb F_g[X]/(Q)$ of size $g^p$, so $Q$ divides $X^{g^p}-X$. The latter splits with simple roots in $\mathbb F_{g^p}$. Thus each such $Q$ has exactly $p$ preimages under the minimal-polynomial map, and the $g$ base field elements account for all degree-one preimages. The general production proof needs only the lower bound.

The trial divisors for the two field sizes are $2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61$. The corresponding remainders are

| $g$ | Remainders in trial-divisor order |
|---|---|
| $4099$ | $1,1,4,4,7,4,2,14,5,10,7,29,40,14,10,18,28,12$ |
| $4111$ | $1,1,1,2,8,3,14,7,17,22,19,4,11,26,22,30,40,24$ |

1. **The lower degree cutoff, $g=4099$, $r=100$.** Trial division by primes through $61$ proves that $4099$ is prime. Trial division by $2,3,5,7$ gives
   $$S=\{53,59,61,67,71,73,79,83,89,97\}.$$
   Here the dyadic interval gives precisely $S$, since $98,99,100$ are composite. The cofactor degrees in the displayed order are $47,41,39,33,29,27,21,17,11,3$. Write $G=4099^{100}$. The $p=53$ class has $(4099^{53}-4099)4099^{47}/53=(G-4099^{48})/53$ elements. Summing all ten disjoint classes gives the exact normalized count
   $$
   \frac{|B|}{G}=\sum_{p\in S}\frac{1-4099^{1-p}}p
      >\frac{10}{100}\frac{4095}{4096}
      >\frac1{20}>\frac1{5\log100}.
   $$
   For the last step one can use $\log100>6\log2>4$, since $100>2^6$ and $\log2>2/3$. This already bounds the exceptional family by $G-|B|$. Both sides of the exclusion occur among admissible squarefree labels. A product of $100$ distinct nonzero linear factors belongs to the exceptional family. A monic irreducible of degree $97$ times three distinct nonzero linear factors has the prescribed factor.

2. **Two primes lost at the boundary, $g=4111$, $r=109$.** The same trial divisors through $61$ certify $4111$. The real lower endpoint is $54.5$, so the integer test starts at $55$. Trial division by $2,3,5,7$ gives thirteen primes through $109$. Of $107,108,109$, exactly $107$ and $109$ are prime. Hence
   $$S=\{59,61,67,71,73,79,83,89,97,101,103\},$$
   with cofactor degrees $50,48,42,38,36,30,26,20,12,8,6$. For $G=4111^{109}$, the $p=103$ class has $(G-4111^7)/103$ elements. The exact normalized sum and its margin satisfy
   $$
   \frac{|B|}{G}=\sum_{p\in S}\frac{1-4111^{1-p}}p
       >\frac{11}{109}\frac{4095}{4096}
       >\frac1{20}>\frac1{5\log109}.
   $$
   A budget that allows only one lost prime fails here. A degree-$103$ monic irreducible times six distinct nonzero linear factors supplies a squarefree witness in $B$. Replacing those six factors with $(X-1)^6$ still gives a member of $B$, now divisible by a square. The count of $B$ intentionally includes both. A product of $109$ distinct nonzero linear factors supplies a squarefree witness outside $B$.

#### Definitions and inherited prime count

Let $g$ be a natural prime and let $r$ be a natural number. Put $F=\mathbb F_g=\mathbb Z/g\mathbb Z$, $M_d=\{f\in F[X]: f\text{ monic},\ \deg f=d\}$, and let $I_d$ denote the irreducible members of $M_d$. Write
$$
S=\{p\in\mathbb N: p\text{ prime},\ r<2p,\ p+3\le r\}.
$$
These are exactly `monicDeg`, `irrDeg`, and `bigPrimes`. The archived `Ev g r f` requires $f\in M_r$, $f(0)\ne0$, squarefreeness, and absence of any irreducible divisor whose degree belongs to $S$. A nonmonic irreducible divisor can be normalized by its leading coefficient without altering the degree or divisibility. For the analytic step we use [§4.10.17](#41017-a-strict-prime-count-in-a-real-dyadic-interval) in its full real form. For every real $y\ge41/2$, the number of primes $y<p\le2y$ is strictly greater than $3y/(5\log y)$. This input already includes the finite range and the Chebyshev and factorial budgets.

#### Lemma (disjoint divisibility classes and the irreducible supply) [Lean, read]

For every prime $g$, every natural $r$, and every finite set $T$ all of whose members satisfy `Ev g r`,
$$
|T|\le g^r-\sum_{p\in S}|I_p|g^{r-p}.
$$
For every prime $g$ and every natural prime $p$,
$$
g^p-g\le p|I_p|.
$$

**Proof.** Reading and reconstructing the $d$ lower coefficients gives a bijection $F^d\to M_d$, so $|M_d|=g^d$, including $M_0=\{1\}$. For $p\in S$ and $Q\in I_p$, congruence $f\equiv0\pmod Q$ among monic degree-$r$ polynomials is equivalent to $f=Qh$ with $h\in M_{r-p}$. Equivalently, division by $Q$ gives a bijection from $M_r$ to pairs of a monic degree-$r-p$ quotient and a remainder of degree less than $p$ (including zero). Each of the $g^p$ remainder classes has $g^{r-p}$ elements. Lean counts the zero class by its product image.

Suppose $Qh=Q'h'$ with both degrees $p,p'$ in $S$. Irreducibility over a field makes $Q$ prime. If $Q\mid h'$, then $p\le r-p'$, whereas both $p$ and $p'$ are strictly greater than $r/2$. Thus $Q\mid Q'$, and irreducibility and monicity force $Q=Q'$, hence $p=p'$ and $h=h'$. This proves both injectivity within the product for each $p$ and disjointness between distinct degrees. Write $B$ for the union of these product images. It is contained in $M_r$ and has the stated sum as its exact cardinality. Since $T$ excludes all these divisors, $T\sqcup B\subseteq M_r$, which yields the first inequality. Polynomials divisible by an irreducible square constitute a separate excluded family in the definition of $T$. For a fixed monic irreducible $R$ of degree $e$, that square condition is the zero residue class modulo $R^2$. It has $g^{r-2e}$ monic degree-$r$ members when $2e\le r$, and none when $2e>r$. The proof needs neither the size of that family nor a disjointness claim about its intersection with $B$. In particular a qualifying $Q$ itself cannot occur twice, because $2\deg Q>r$.

For the second inequality, take $K=\mathbb F_{g^p}$. It has $g^p$ elements and dimension $p$ over $F$. At most $g$ elements are in the image of the base field. For every remaining element $a$, the tower law gives $[F(a):F]\mid p$. The value $1$ would put $a$ in $F$, so its monic minimal polynomial has degree $p$ and belongs to $I_p$. Each fiber of the minimal-polynomial map sits inside the distinct roots of one nonzero degree-$p$ polynomial over $K$ and has at most $p$ elements. This proves $g^p-g\le p|I_p|$. In particular $I_p$ is nonempty. This argument constructs the supply independently of any existence assumption about factors in the labels.

#### Theorem (the fourth squarefree count) [Lean, read]

For every natural prime $g\ge4096$, every natural $r\ge100$, and every finite set $T$ of polynomials satisfying `Ev g r`,
$$
|T|\le \left(1-\frac{1}{5\log r}\right)g^r.
$$
In fact the number of ambient monic polynomials in $B$ is strictly greater than
$$
\left(1+\frac{36605}{1024000}\right)\frac{g^r}{5\log r}.
$$

**Proof.** In the analytic proposition $S$ may be any finite set of naturals with the displayed membership equivalence. Application of the inherited theorem at the real $y=r/2$ is permitted since $r/2\ge50$. The upper floor is $r$, the lower floor is natural division by two, and the count is $\pi(r)-\pi(\lfloor r/2\rfloor)$. Compared with $S$, this includes the primes among $r-2,r-1,r$. At least one of these three integers is even and greater than two, so at most two extra primes enter. Write $L=\log r>0$. Since $0<\log(r/2)<L$, the strict dyadic bound gives
$$
5L(|S|+2)>\tfrac32r.
$$
The elementary estimate $\log100<4.64$ follows from $\log100=7\log2-\log(128/100)$, $\log2<0.693147181$, and $\log(128/100)\ge1-100/128$. The function $\log x/x$ has derivative $(1-\log x)/x^2$ and decreases for $x\ge100$, so $L\le0.0464r$. Therefore
$$
5L|S|>\tfrac32r-10L\ge\tfrac{259}{250}r.
$$
This gives $|S|>0$ before choosing any member. It also explains the strict margin in `AnaCore.lean:73–96`: with $c=4095/4096$, one has $(259/250)c=1+36605/1024000$, so $5L|S|c>r$.

Now $p\ge2$, $p\le r$, and $g\ge4096$ give $g^{1-p}\le1/4096$. The lemma and coefficient count therefore yield, term by term,
$$
|I_p|g^{r-p}\ge\frac{g^p-g}{p}g^{r-p}
   =g^r\frac{1-g^{1-p}}p\ge g^r\frac c r.
$$
Summing and using the strict bound on $5L|S|c$ proves the margin and the claimed weak upper bound on $|T|$. To see that the same supply guarantees a squarefree polynomial with nonzero constant and a qualifying factor for all these parameters, choose $p\in S$ and $Q\in I_p$ from the two strict counts. For $d=r-p$ use $h=X^d-1$ if $g\nmid d$, and $h=X^d+X+1$ if $g\mid d$. Here $d\ge3$. In the first case $h$ is coprime to $dX^{d-1}$, and in the second the derivative is $1$. In either case $h(0)\ne0$, and $d<p$ implies $Q\nmid h$. Thus $Qh$ is a squarefree label with the required factor. This existence argument is an exposition of the count's consequence.

#### Boundary and consumer notes

Deleting the lower cutoff without a replacement can invalidate the theorem. At $r=2$ the degree set $S$ is empty. The entire exceptional family then has $(g-1)^2$ elements: start with $g(g-1)$ monic quadratics with nonzero constant and remove the $g-1$ squares $(X-a)^2$ with $a\ne0$. For $g=4099$ this exceeds $4g^2/5$, while $1-1/(5\log2)<4/5$ by $\log2<1$. Also the strict degree cutoff $r<2p$ is essential to the product-image argument. Over $\mathbb F_2$ at $r=6$, $p=3$, the distinct rootless cubics $X^3+X+1$ and $X^3+X^2+1$ can be interchanged as factor and cofactor of their product. Both ordered pairs have the same image when $r=2p$ is admitted.

In A2, `SquarefreePrimeFactor/SqfPrimeFactorOf.lean:8–9` passes `squarefree_count_estimate`, `irreducible_count_lower_bound`, and `analytic_of hRS` to `claim_of`. The latter substitutes the irreducible lower bound in the subtracted sum, with division by the positive prime degree. `Analytic.lean:8–14` calls `ana_main` with `bigPrimes r`; the range guard follows from $p+3\le r$. In `ExplicitFormulaCounts/SqfCounts.lean:18–45`, `counts_closed D` supplies the closed `primes_dyadic_range` to `sqfPrimeFactor_of` and uses the resulting `h6` at $g=D.\mathrm{host}.g(k)$ and $r=D.R.r$ for each $k\in\mathrm{Fin}(2)$. The field primality instance comes from the host. The tuple's other entries consume `squarefree_roots_injective`, `squarefree_root_shift`, and `squarefree_div_degree`. The modulus calculation inside `counts_of_sqf` supplies the root-shift entry. The fourth entry uses polynomial divisibility and all primes in its degree range, with no residue restriction on the degree. The table in [§4.10.23](#41023-when-prime-to-parts-of-roots-collide) gives the order of the four inputs. In `StmtLocFOfCountsAll.lean:188–192`, `P5` applies `wt_le_count` to the `Ev` filter. The corresponding positive label condition in [§4.11](#411-from-separated-inertia-lines-to-residual-irreducibility) is the sixth clause of `IsGood`. The weight conversion and the other clauses keep their own hypotheses. [Source ledger](../sources/SOURCES.md#chapter-4-41018-counting-the-prime-degree-factor-exception)

The fourth count retains author-level local source reading and the independent-source second-level ruling 11251827 on the count, irreducible supply, analytic margin and specified handoff. The author's 100 exact checks and the audit's 1,530,033 assertions are finite certificates. Lean kernel replay remains open.

### 4.10.19 Rational factors and the seven-eighths bound for squarefree degree splits

#### Motivation

A monic polynomial of degree $r$ can have several divisors of degree $a$. When estimating how many labels admit a split of degrees $a$ and $r-a$, we must count each product only once. The space of ordered pairs of monic factors has the same cardinality as the space of monic polynomials of degree $r$. A bound below that cardinality comes from the pairs with a rational root on each side. In a squarefree product, those roots are distinct, and exchanging them gives a second factorization with the same degrees. A second-order inclusion–exclusion bound shows that there are enough pairs of this kind to save one eighth of the ambient cardinality.

#### Examples

**A quadratic over $\mathbb F_3$.** Write $L_c=X-c$ and let $M_n$ and $R_n$ denote the monic degree-$n$ polynomials and those among them with a root in the base field. Here $M_1=R_1=\{X,X-1,X+1\}$ and
$$
\begin{aligned}
M_2
 &=\{X^2,X^2+1,X^2+2,\ X^2+X,X^2+X+1,X^2+X+2,\\
 &\hspace{3.7em}X^2+2X,X^2+2X+1,X^2+2X+2\},\\
R_2
 &=\{X^2,X^2+2,X^2+X,X^2+X+1,X^2+2X,X^2+2X+1\}.
\end{aligned}
$$
Indeed, the six products $L_cL_d$ indexed by unordered pairs with repetition account for exactly $R_2$. With $r=2$ and $a=1$, the squarefree labels admitting the split and having nonzero constant term form the singleton $E_{2,1}=\{X^2+2\}$. Its only two ordered factorizations are $(X-1,X+1)$ and $(X+1,X-1)$, exchanged by transferring the roots $1$ and $-1$. All nine pairs in $M_1\times M_1$ have a root on each side. Their total weight at one half per pair is $9/2$, and the displayed product uses exactly one unit. Thus the weight bound here is $1\le9/2$, while the seven-eighths bound is $1<63/8$. The actual fraction is $1/9$.

**A cubic over $\mathbb F_4$.** Write $K=\{0,1,u,v\}$, where $u^2+u+1=0$ and $v=u+1=u^2$. The exact sets of monic polynomials are $M_1=\{L_c:c\in K\}$, $M_2=\{X^2+bX+d:b,d\in K\}$ and $M_3=\{X^3+bX^2+dX+e:b,d,e\in K\}$. The root sets in these three degrees are
$$
\begin{aligned}
R_1 &= M_1,\\
R_2 &= \{L_c L_d:c,d\in K\},\\
R_3 &= \{L_cL_dL_e:c,d,e\in K\}\ \cup\ \{L_c Q:c\in K,\ Q\in\mathcal I\},\\
\mathcal I &= \{X^2+bX+b^2s:b\in\{1,u,v\},\ s\in\{u,v\}\}.
\end{aligned}
$$
These descriptions include repetitions among the linear factors. To check the list $\mathcal I$ of rootless quadratics, observe that the square map permutes $K$, so every monic quadratic with zero linear coefficient has a root. For $b\ne0$, put $X=bY$. Then $Y^2+Y$ takes the values $0,0,1,1$ at $0,1,u,v$, giving exactly the two rootless choices at each $b$. Unique factorization gives $|R_2|=4+6=10$. A product of three linear factors is specified by its multiset of roots. There are four triples with all entries equal, $4\cdot3$ with exactly two equal, and four with all entries distinct. This gives $|R_3|=20+4\cdot6=44$.

For $(r,a)=(3,1)$, the exact exceptional set is
$$
E_{3,1}=\{L_1L_uL_v\}\ \cup\ \{L_cQ:c\in\{1,u,v\},\ Q\in\mathcal I\}.
$$
The two parts are disjoint. The first consists of $X^3+1$, since $u+v=1$ and $uv=1$. In its ordered decomposition $(X+1,X^2+X+1)$, exchange $1$ and $u$. This gives $(X+u,X^2+uX+v)$, since $(X+1)(X+v)=X^2+uX+v$. The remaining pair in the fiber is $(L_v,L_1L_u)$. All three have weight one half. For each product $L_cQ$ the only pair is $(L_c,Q)$, of weight one. The exceptional set thus has $1+3\cdot6=19$ members and uses $3/2+18=39/2$ units of weight. The full pair space has $4\cdot16=64$ pairs, of which $4\cdot10=40$ have roots on both sides. Its weight is $64-40/2=44$, strictly below the seven-eighths budget $56$. The actual fraction is $19/64$.

#### Definitions

Let $K=\mathbb F_q$ be a finite field of cardinality $q$, and work in $K[X]$. For every $n\ge0$, put
$$
M_n=\{f:f\text{ is monic of degree }n\},
\qquad
R_n=\{f\in M_n:f(c)=0\text{ for some }c\in K\}.
$$
Here $M_0=\{1\}$ and $R_0=\varnothing$. A polynomial is squarefree if no square of a nonconstant irreducible polynomial divides it. For integers $0\le a\le r$, define
$$
E_{r,a}=\{f\in M_r:f(0)\ne0,\ f\text{ is squarefree, and }f
\text{ has a divisor of degree }a\}.
$$
The divisor may initially have any nonzero leading coefficient. All roots used in the count are in $K$. For $f\in M_r$, its ordered factorization fiber for this split is the set of $(A,B)\in M_a\times M_{r-a}$ with $AB=f$.

#### Lemmas and theorem

**Lemma (rational-root density).** For every $n\ge0$, $|M_n|=q^n$. For $n\ge1$ and a prescribed $c\in K$, exactly $q^{n-1}$ polynomials in $M_n$ vanish at $c$. For $n\ge2$ and distinct $c,d\in K$, exactly $q^{n-2}$ vanish at both. Consequently $2|R_n|\ge q^n$ for every $n\ge1$. In degrees $n\ge2$ the argument gives the sharper inequality $2|R_n|\ge q^n+q^{n-1}$.

**Lemma (weighted factorization fibers).** For $0\le a\le r$ and every $\mathcal T\subseteq E_{r,a}$,
$$
2|\mathcal T|+|R_a|\,|R_{r-a}|\le2q^r.
$$

**Theorem (seven-eighths bound).** If $0<a<r$ and $\mathcal T\subseteq E_{r,a}$, then
$$
8|\mathcal T|\le7q^r.
$$
In particular this holds over a prime field of order $q\ge4096$ for $r\ge100$ and $1\le a\le r/2$, the range of the third squarefree counting estimate.

#### Proof

The coefficients below the monic leading term identify $M_n$ with $K^n$. For a prescribed root $c$, the factor theorem identifies its fiber with $M_{n-1}$ by multiplication by $L_c$. For distinct $c,d$, first divide by $L_c$. The quotient still vanishes at $d$, because $L_c(d)=d-c\ne0$. A second division identifies the simultaneous fiber with $M_{n-2}$. In each case the quotient is monic of the indicated degree and multiplication is the inverse.

Every monic linear polynomial has a root. For $n\ge2$, let $k(f)$ be the number of distinct rational roots of $f$. For every nonnegative integer $k$,
$$
2\,\mathbf 1_{k>0}\ge 2k-k(k-1).
$$
This is equality for $k=0,1,2$. For $k\ge3$ the right hand side is $k(3-k)\le0$. Summing the inequality is the second-order Bonferroni bound. Counting incidences by their prescribed root gives $\sum_{f\in M_n}k(f)=q\cdot q^{n-1}$. Counting ordered pairs of distinct roots gives $\sum_{f\in M_n}k(f)(k(f)-1)=q(q-1)q^{n-2}$. Hence
$$
2|R_n|\ge2q^n-q(q-1)q^{n-2}=q^n+q^{n-1}.
$$

For the second lemma, every $f\in\mathcal T$ has an ordered factorization of the required degrees. If $f=DH$ and $D$ has degree $a$ and leading coefficient $\lambda$, take $A=\lambda^{-1}D$ and $B=\lambda H$. Both are monic, because their product is monic, and the degrees sum to $r$.

Give weight $1/2$ to a pair in $R_a\times R_{r-a}$ and weight $1$ to every other pair in $M_a\times M_{r-a}$. A pair of weight $1$ already gives its fiber one unit. Otherwise choose roots $x$ of $A$ and $y$ of $B$. Squarefreeness of $f=AB$ makes $A$ and $B$ coprime, since a common irreducible divisor would have its square dividing $f$. In particular $A(y)\ne0$, $B(x)\ne0$, and $x\ne y$. Write $A=L_x A_0$ and $B=L_y B_0$. Exchanging the marked roots gives
$$
(A,B;x,y)\longmapsto (L_y A_0,L_x B_0;y,x).
$$
The new factors are monic of the same degrees, and their product is still $f$. The new first factor vanishes at $y$, so it differs from $A$. Applying the exchange with the new markings recovers the original factors by cancellation. Thus the exchange is an involution on factorizations with marked roots, and supplies a distinct unmarked pair in the same fiber. Two pairs of weight $1/2$ give at least one unit. The argument allows further pairs in the fiber.

Distinct products have disjoint fibers. Summing the lower bound of one unit over $\mathcal T$ and comparing with the weight of the entire pair space gives
$$
|\mathcal T|\le |M_a|\,|M_{r-a}|-\tfrac12|R_a|\,|R_{r-a}|
=q^r-\tfrac12|R_a|\,|R_{r-a}|.
$$
For the theorem, both degrees are positive, so multiplication of the two density bounds gives $4|R_a|\,|R_{r-a}|\ge q^r$. Multiply the second lemma by four to get
$$
8|\mathcal T|+q^r\le 8|\mathcal T|+4|R_a|\,|R_{r-a}|\le 8q^r.
$$

#### Remarks

The computed fractions $1/9$ and $19/64$ show strict slack in the two examples. In fact every positive split has slack at each fixed $q$. The density proof gives $2|R_n|\ge (1+1/q)q^n$ for every positive $n$, using $2q\ge q+1$ for $n=1$. The same weight argument bounds the fraction by $1-(1+1/q)^2/8<7/8$. This comparison is a consequence of the displayed counts at fixed field size.

Squarefreeness excludes fixed points in the exchange. For $c\in K$ nonzero, take $f=(X-c)^2$, $r=2$ and $a=1$. There is just one ordered pair, $(L_c,L_c)$. Its marked exchange returns the same pair and the whole fiber has weight $1/2<1$. The one-unit estimate for individual fibers therefore fails.

At $a=0$ or $a=r$, the factor of degree zero must be $1$, the doubly rooted pair set is empty, and the weighted lemma gives $|\mathcal T|\le q^r$. Every squarefree monic polynomial of degree $r$ with nonzero constant is eligible. For a counterexample to the seven-eighths bound at either endpoint, take $q=4099$ and $r=100$. The prime divisors to test for $4099$ are at most $61$. There are $q^{99}$ monic polynomials of degree $100$ with zero constant. For each $1\le d\le50$, there are at most $q^d$ monic irreducibles of degree $d$, and each square divides exactly $q^{100-2d}$ monic polynomials of degree $100$. A union bound shows that the excluded fraction is at most
$$
q^{-1}+\sum_{d=1}^{50}q^{-d}<q^{-1}+(q-1)^{-1}<1/8.
$$
The endpoint label set therefore has more than $(7/8)q^{100}$ elements. By contrast, the restriction $a\le r/2$ in the third count simply chooses one of the two degrees. Taking the complementary monic factor gives the same eligible set for $r-a$.

The third squarefree count uses the polynomial estimate over each of the two host prime fields, with the corresponding field size and the common degree. Its inputs are the lower bounds on field size and degree, the specified degree split and the defining conditions on the labels. The progression congruence enters the separate root-shift estimate. The fourth count uses a different exclusion, involving prime-degree irreducible divisors. [Source ledger](../sources/SOURCES.md#chapter-4-41019-rational-factors-and-squarefree-degree-splits)

**An original-range nonempty family [Expository].** In the prime field of order $4099$, take $r=100$ and the singleton containing $f=\prod_{j=1}^{100}(X-j)$. Its roots are distinct and nonzero. For every $1\le a\le50$, the product of the first $a$ factors is a divisor of degree $a$, so the same singleton witnesses the original label contract at every allowed split.

**The actual third slot [Lean, read].** In `counts_of_sqf`, `h5` consumes the finite $Eiv$ family at $g=D.\mathrm{host}.g(k)$ and $r=D.R.r$, with the host prime instance, $g\ge4096$, $r\ge100$, $1\le a$ and $2a\le r$. The closed export supplies `squarefree_div_degree`. In `propW_of_counts`, `P4` takes $a$ from the integer interval $[1,\lfloor r/2\rfloor]$ and uses `Civ` with `wt_le_count` and the named `lawL` for the filter at each place. The adjacent slots use [root collisions](#41023-when-prime-to-parts-of-roots-collide), [translation by a unit](#41021-counting-roots-after-translation-by-a-unit) and [the prime-degree exception](#41018-counting-the-prime-degree-factor-exception). [A2 SqfCounts.lean:18–45 and StmtLocFOfCountsAll.lean:98–111,182–188](../sources/SOURCES.md#chapter-4-41019-rational-factors-and-squarefree-degree-splits)

**Reading boundary.** The local production proof has author-level R3 and a same-source initial review of all five audited claims. Independent-source adjudication and Lean kernel replay are [Open]. The bound $7/8$ is a uniform upper bound. The fixed-field comparison above records the available slack.

The first squarefree count circulated in draft form as §4.10.20. Its published proof is in [§4.10.23](#41023-when-prime-to-parts-of-roots-collide).

### 4.10.21 Counting roots after translation by a unit

#### Motivation

Fix one prescribed unit $c$ in the host prime field. The second squarefree count measures how often a label has a root whose prime-to-$\ell$ part agrees with that of $c$. The same projection acts on the root and on the prescribed scalar because the target characteristic polynomial is built from the projected roots, and the irreducibility criterion tests the image of the projected scalar in it. The last clause of that criterion applies the multiplicative map $\iota_v$ to both. Dividing the root by $c$ turns equality of the projections into a prime-power order condition. Over the base field, one translated root of degree $k$ gives a whole orbit of $k$ witnesses. [A2, CyclotomicNorms/StatementT.lean:19–26,36–52](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

#### Examples [Expository]

**Linear factors over $\mathbb F_7$ with $c=3$.** The units $1,2,3,4,5,6$ have orders $1,3,6,3,6,2$, respectively. The quotients $y=x/c$ of prime-power order, including order $1$, are $1,2,4,6$. The corresponding roots $x$ are $3,6,5,4$. For instance, $x=4$ gives $y=6$ of order $2$. The odd-order part of $3$ is $3^4=4$ and that of $4$ is $4$. Comparing the odd-order part of $x$ directly with $3$ would miss this witness. These four monic linear labels are exactly the exceptions at $g=7,r=1,c=3$. The factor bound is $\operatorname{ppSum}(6)=2+3=5$, which counts the identity in both torsion subgroups.

**Quadratic factors over $\mathbb F_7$ with $c=2$.** Work in $\mathbb F_7[i]$ with $i^2=-1$. The polynomial $X^2+1$ is irreducible since the squares are $0,1,2,4$. Set $x=2i$. Its conjugate is $-2i$, since $i^7=-i$. The quotient $x/2=i$ has order $4$, while $2$ and $x$ have orders $3$ and $12$. The odd-order part of $x$ is $x^4=2$ and that of $c$ is $2$. Thus $X^2+4$ is an exceptional squarefree quadratic label.

The extension's unit group is cyclic of order $48=16\cdot3$. The two relevant subgroups can be generated by $2+3i$ and $2$. In fact $(2+3i)^2=2-2i$, $(2+3i)^4=-i$ and $(2+3i)^8=-1$, so the first generator has order $16$. The two subgroups intersect in $1$, giving $18$ possible quotients. Exactly $4$ lie in $\mathbb F_7^\times$, where the corresponding subgroup sizes are $2$ and $3$. The other $14$ quotients give $14$ roots of degree two under multiplication by $c$. They form seven conjugate pairs and give exactly seven irreducible quadratic exceptions for this $c$. The degree-two factor bound is $(16+3)/2=19/2$. The full quadratic label count also includes split labels. At $k=1$ the four eligible roots are $2\{1,2,4,6\}=\{1,2,4,5\}$, so there are $\binom 62-\binom 22=14$ split exceptions among pairs of distinct nonzero roots. This gives $21$ quadratic exceptions in all. The two models illustrate the algebraic count at these values of $g,r$. The final host estimate has its own scale and congruence hypotheses. [A2 CountA.lean:47–78, CountB.lean:30–72, CountC.lean:15–57, and Milne, pp. 53–55](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

#### Definitions

Let $g$ be prime, $K=\mathbb F_g$ and $\overline K$ an algebraic closure. Use $c$ also for the image of $c\in K^\times$ in $\overline K$. For $z\ne0$, write its finite order as $ab$, with $a$ an $\ell$-power and $b$ prime to $\ell$. Define $P_\ell(z)=z^u$, where $u\equiv0\bmod a$ and $u\equiv1\bmod b$. The archive takes $u$ to be $a$ times the residue of $a^{-1}$ modulo $b$. When $b=1$ the prime-to-$\ell$ part is $1$. This describes the archive's total monoid definition on the nonzero elements used here.

A label is a monic degree-$r$ polynomial with nonzero constant term. The predicate **Eiii** says that $f$ is a squarefree label and that the following assertion fails: for every prime $\ell\ne g$ and every root $x$ of $f$ in $\overline K$, $P_\ell(x)\ne P_\ell(c)$. The allowed primes are all primes different from $g$. The first count uses a different prime range, described in [§4.10.23](#41023-when-prime-to-parts-of-roots-collide). Root membership is in the multiset of roots after base change.

For $N\ge1$ let $L_p(N)=p^{v_p(N)}$ and define
$$
\operatorname{ppSum}(N)=\sum_{p\mid N,\;p\ \mathrm{prime}}L_p(N).
$$
The sum at $N=1$ is zero. For a fixed $c$, **Good** means that $P\in K[X]$ is monic and irreducible and that for some prime $\ell$ and integer $j\ge0$ it divides $X^{\ell^j}-c^{\ell^j}$. The case $j=0$ allows $P=X-c$. [A2 SqfLab.lean:13–24,30–32, Development.lean:11–22 and CountB.lean:30–32](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

#### Lemmas and theorem

**Translation and factor count [Lean, read].** A label satisfying Eiii for $c$ has a Good divisor of degree $1\le k\le r$. For $g\ge3$ and any finite set $Q$ of distinct degree-$k$ Good polynomials, with $k\ge1$, one has $k|Q|\le\operatorname{ppSum}(g^k-1)$.

**Counting lemma (`CountP`) [Lean, read].** For every prime $g\ge3$, every integer $r\ge1$, every $c\in K^\times$ and every finite set $T\subset K[X]$ whose members satisfy Eiii for this $c$,
$$
|T|\le\sum_{k=1}^r\frac{\operatorname{ppSum}(g^k-1)}{k}\,g^{r-k}.
$$

**Second squarefree count (`PI.SqfRootShift.Claim`) [Lean, read].** Let $g,r,q,d,e$ be natural numbers. Assume $g,q,d$ are prime, $q\equiv3\bmod8$, $d\equiv7\bmod16$, $e\ge2$, $q,d\ge16$, and
$$
g\equiv1\bmod(4\cdot2^e qd),\qquad r\ge100,\qquad g\ge4096.
$$
For every $c\in K^\times$ and every finite set $T$ of polynomials satisfying Eiii for this **same** $c$,
$$
|T|\le\left[\frac{1}{4\min(q,d)}+\frac{1+\log r}{g-1}\right]g^r.
$$
The logarithm is natural. The arithmetic lemma `ArithP` bounds the entire right side of `CountP` by this expression under the displayed hypotheses on the integers. [A2 SqfRootShift.lean:11–16, Development.lean:13–27, CountC.lean:15–57 and CountD.lean:11–93](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

#### Proof

**The common power and the translated roots.** Let $z$ have degree $k$. Counting basis coordinates gives $|K(z)|=g^k$. If $z\ne0$, Lagrange's theorem gives $z^{g^k-1}=1$. The embedded unit $c$ belongs to $K(z)^\times$ and satisfies the same power identity. Both orders are finite and positive.

For $z$ of order $ab$ as above, $(u-1)a$ is a multiple of $ab$, so $P_\ell(z)^a=z^a$. If $P_\ell(x)=P_\ell(c)$, take $j=v_\ell(\operatorname{ord}x)+v_\ell(\operatorname{ord}c)$. The power $\ell^j$ is a multiple of the $\ell$-part of each order, so $x^{\ell^j}=c^{\ell^j}$. Conversely, from $x^{\ell^j}=c^{\ell^j}$ raise both sides again by the product of those two $\ell$-parts. This gives equality of the two projections raised to an $\ell$-power. Both projections have order prime to $\ell$, so this last power is injective on their subgroup by Bézout's identity. This proves the equivalence with $x/c$ having $\ell$-power order, including $1=\ell^0$. In characteristic $g$, every nontrivial such order divides $g^k-1$, so $\ell\ne g$. If $x=c$, every prime different from $g$ witnesses the original equality.

For an Eiii label $f$, negate the universal assertion to choose $\ell,x$ with equal projections. The nonzero constant term gives $x\ne0$. Its monic minimal polynomial $P$ divides $f$ and has degree $1\le k\le r$. The common power identity says the binomial in Good also vanishes at $x$, so $P$ divides it. Conversely, if $P$ is Good, evaluation of its binomial at any root $z$ gives $z^{\ell^j}=c^{\ell^j}$ and hence $z\ne0$. Its minimal polynomial equals $P$. Thus every root gives a translated element $y=z/c$ with
$$
y^{g^k-1}=1,\qquad y^{\ell^j}=1.
$$
Division by the fixed base-field unit is an injection, stays in the same simple field, and commutes with Frobenius, since $(z/c)^g=z^g/c$. [A2 CountA.lean:11–43, CountB.lean:13–72 and CountD.lean:11–49](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

**Counting a degree fiber.** For an irreducible $P$ of degree $k$, Frobenius $z\mapsto z^g$ is an automorphism of $K(z)$ and has fixed field $K$. Indeed $X^g-X$ has at most $g$ roots and all of $K$ is fixed. The product of $X-w$ over the orbit of $z$ has coefficients in $K$ and is divisible by $P$. Each orbit member is a root of $P$, so the orbit consists of exactly $k$ distinct roots. The Lean body uses perfect-field separability and splitting in the algebraic closure for this cardinality. Distinct monic irreducibles have disjoint root sets by uniqueness of the minimal polynomial. The union over $Q$ has $k|Q|$ roots, and translating by the same $c$ is injective on this union.

Take $N=g^k-1\ge2$. If a translated root has order $\ell^i>1$, then $\ell\mid N$ and the order divides $L_\ell(N)$. The identity is also covered, for example by the $L_p(N)$-th roots of unity for the least prime factor $p$ of $N$. For each prime $p\mid N$, the polynomial $X^{L_p(N)}-1$ has at most $L_p(N)$ roots. Summing these cardinalities bounds the union even when it has overlaps. This proves $k|Q|\le\operatorname{ppSum}(N)$. [A2 CountA.lean:47–78, CountC.lean:15–57 and Milne, Corollary 4.22 and Proposition 4.26](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

**From factors to labels.** Choose one Good divisor $P_f$ for each $f\in T$ and let $Q_k$ be the degree-$k$ part of the image of this choice. Each fiber of $f\mapsto P_f$ is contained in the monic degree-$r$ multiples of its fixed divisor $P$. Each such multiple has zero remainder and a unique monic quotient of degree $r-k$. The $r-k$ coefficients below the leading one determine the quotient, giving $g^{r-k}$ possibilities, including just $1$ when $r=k$. Thus
$$
|T|\le\sum_{P\in\{P_f:f\in T\}}g^{r-\deg P}
=\sum_{k=1}^r|Q_k|g^{r-k}
\le\sum_{k=1}^r\frac{\operatorname{ppSum}(g^k-1)}{k}\,g^{r-k}.
$$
The choice of a single factor partitions the labels even when several primes or degrees give witnesses. The disjoint $k$-element root sets justify division by $k$. In `countP` the regrouping by degree takes place before the inequality is cast to the reals. [A2 CountC.lean:59–100 and CountD.lean:51–93](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

**The term of degree one (`arith1`).** Put $n=g-1$ and $m=\min(q,d)$. The progression and $e\ge2$ give $16\mid n$, $q\mid n$ and $d\mid n$. The residues give $q\equiv3\bmod8$ and $d\equiv7\bmod8$, hence $q\ne d$. The powers $A=L_2(n)$, $B=L_q(n)$ and $C=L_d(n)$ are three distinct entries of the sum, with $A\ge16$ and $B,C\ge m\ge16$. Write $R,U$ for the sum and product of the remaining entries, with $R=0,U=1$ if there are none. Then $n=ABCU$ and $\operatorname{ppSum}(n)=A+B+C+R$.

For entries at least $2$, the sum is at most the product. The empty case gives $0\le1$, the singleton case is equality, and induction appends an entry $a\ge2$ to a nonempty list with product $b\ge2$. Its new sum is at most $a+b\le ab$, using $(a-1)(b-1)\ge1$. Thus $R\le U$. This also proves $\operatorname{ppSum}(N)\le N$ for $N\ge1$ by unique factorization. The archive budgets the four summands by
$$
16mA\le n,\qquad16mB\le n,\qquad16mC\le n,\qquad64mR\le n.
$$
For each of the first three, remove the indicated factor from $ABCU$. The other two distinguished factors have product at least $16m$. For the last, $ABC\ge16m^2\ge64m$ and $R\le U$. Combining the four bounds gives $16m\operatorname{ppSum}(n)\le(3+1/4)n\le4n$. Hence $4m\operatorname{ppSum}(n)\le n$, and the first term of the count is at most $(g-1)g^{r-1}/(4m)\le g^r/(4m)$. [A2 SumLeProdOfTwoLe.lean:9–108 and ArithP.lean:31–59,106–109](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

**Higher-degree prime powers (`arith2`).** For $k\ge1$ write $N_k=g^k-1=nS_k$, where $S_k=1+g+\cdots+g^{k-1}$. Split the primes dividing $N_k$ according to whether they divide $n$. For $p\mid n$ the valuation identity is
$$
v_p(N_k)=v_p(n)+v_p(k).
$$
For any $a\equiv1\bmod p$, an exponent $u$ prime to $p$ leaves $v_p(a-1)$ unchanged, since the geometric quotient of $a^u-1$ by $a-1$ is $u\bmod p$. Write $k=p^su$. For odd $p$, if $v_p(a-1)=b\ge1$, expand $(1+(a-1))^p-1$. The first term has valuation $b+1$, the intermediate terms have valuations at least $1+2b$, and the last has valuation $pb>b+1$. Raising to $p$ adds exactly one. Iteration proves the identity. For $p=2$, the preceding $16\mid n$ supplies $g\equiv1\bmod4$. Every positive power $a$ of $g$ is $1\bmod4$. Hence $v_2(a+1)=1$, so $v_2(a^2-1)=v_2(a-1)+1$. The same iteration proves the identity there. The archived `lte_two` and `lte_odd` use the corresponding Mathlib lifting-the-exponent lemmas.

For $p\mid n$ the identity gives $L_p(N_k)=L_p(n)p^{v_p(k)}\le kL_p(n)$, since $p^{v_p(k)}\mid k$. If $p\nmid n$ and $p\mid N_k$, the entire prime power of $p$ in $N_k$ is in $S_k$. The latter entries sum to at most $\operatorname{ppSum}(S_k)\le S_k$. Thus
$$
\operatorname{ppSum}(g^k-1)\le k\operatorname{ppSum}(g-1)+\frac{g^k-1}{g-1}.
$$
The archive first uses the integer quotient and then uses $g-1\mid g^k-1$ to identify its real cast with the displayed fraction. [A2 SumLeProdOfTwoLe.lean:110–196 and ArithP.lean:60–75](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

**Summing `ArithP` and closing the theorem.** Set $G=g$ in the reals. For $2\le k\le r$, divide the last estimate by $k$ and multiply by $G^{r-k}$. Use $\operatorname{ppSum}(g-1)\le G-1$ and $(G^k-1)G^{r-k}\le G^r$ to get
$$
\frac{\operatorname{ppSum}(g^k-1)}{k}G^{r-k}\le
(G-1)G^{r-k}+\frac{G^r}{G-1}\frac1k .
$$
The first sum over $k=2,\dots,r$ telescopes by $(G-1)G^j=G^{j+1}-G^j$ to $G^{r-1}-1\le G^r/(G-1)$. The second uses $\sum_{k=2}^r1/k\le\int_1^r dt/t=\log r$ by comparison on each interval $[k-1,k]$. Both comparisons include the empty tail at $r=1$. Adding the degree-one estimate gives the theorem's coefficient, with the $1$ in $1+\log r$ coming from the geometric sum. This proves `arithP` on the actual `CountP` sum. The archive forms the transitive inequality in `claim_of`, and the closed export `squarefree_root_shift` supplies both proved arguments. [A2 ArithP.lean:9–29,76–116, Development.lean:24–27 and OrbitalBoundsConclusion/SqfRootShift.lean:1–5](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

#### Remarks

**Use of the hypotheses.** The residues of $q,d$ give distinctness in `arith1`. Primality identifies the two prime-power entries, and $q,d\ge16$ supplies the lower bounds for the four budgets. The progression and $e\ge2$ give $16,q,d\mid g-1$, and $4\mid g-1$ gives the two-adic valuation identity. The host guard $g\ge4096$ implies $g\ge3$ for `CountP`, which gives $g^k-1\ge2$ for the least-prime-factor argument. It also ensures positivity of $G-1$. The guard $r\ge100$ gives $r\ge1$ for the degree interval and the geometric and harmonic sums. The proof uses $g\ge3$ and $r\ge1$ at these steps. Squarefreeness is part of Eiii and enters the weighted consumer. Extraction uses monicity, degree and nonzero constant. The quotient budget uses monicity and degree. [A2 CountC.lean:42–47,70–100, CountD.lean:11–27, ArithP.lean:31–75 and StmtLocFOfCountsAll.lean:98–111,176–181](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

**An original-range nonempty family [Expository].** Set $(g,r,q,d,e)=(34961,100,19,23,2)$. Trial division up to $186$ proves $g$ prime, and $g-1=5\cdot16\cdot19\cdot23$. The two auxiliary primes have the required residues. In $\mathbb F_g$ take $c=8491$, $y=24311$ and $x=cy=14957$. Repeated squaring gives $y^8=-1$, $y^{16}=1$, $c^{19}=1$ and $c\ne1$. Thus $y$ has order $16$, $c$ has order $19$, and $x$ has order $304$. The exponent $96$ is divisible by $16$ and is $1\bmod19$, so $P_2(x)=x^{96}=c=P_2(c)$. Take
$$
f=(X-14957)\prod_{a=1}^{99}(X-a),\qquad T=\{f\}.
$$
The $100$ distinct nonzero roots give monicity, degree $100$, squarefreeness and nonzero constant. Since $2\ne g$, the root $14957$ witnesses Eiii. Here $\operatorname{ppSum}(g-1)=16+5+19+23=63$. At $k=2$, $g+1=2\cdot3\cdot5827$, with $5827$ prime by trial division up to $76$. The old prime powers of $g^2-1$ contribute $32+5+19+23=79$ and the new ones contribute $3+5827=5830$, giving $5909\le2\cdot63+34962$. This witnesses the original quantifiers of `SqfRootShift.Claim`. A full host record $D$ requires additional data.

**Failures under specified changes [Expository].**

- At $g=2,r=1,c=1$, the singleton $T=\{X-1\}$ satisfies Eiii with $\ell=3$. But $\operatorname{ppSum}(2^1-1)=0$. The assumption $g\ge3$ in the algebraic bound keeps the identity case inside the prime-factor union.
- Allowing $c$ to vary with a label would make each of the six nonzero monic linear labels at $g=7$ eligible by choosing its root as $c$. This exceeds the fixed-unit budget $5$. In the linear model at $c=3$, $x=1$ has order $1$, but $x/3=5$ has order $6$. Thus $X-1$ fails Eiii for $c=3$, since no prime projection kills the entire quotient. In the quadratic model $x$ itself has order $12$ and still gives an Eiii witness. The prime-power test is on $x/c$.
- Drop $4\mid g-1$ from `lte_two`. At $g=7,k=2$, $v_2(48)=4$ while $v_2(6)+v_2(2)=2$. Even the estimate in `pp_lte` fails for $p=2$, since $16>2\cdot2$. Drop distinctness from `arith1`. Then $q=d=19$ and $n=16\cdot19^2$ give $4\cdot19(16+361)>n$. These examples concern the indicated intermediate assertions.
- The entire Claim with just the progression hypothesis deleted is false. Take $(g,r,q,d,e)=(65537,100,19,23,2)$ and $c=1$. Trial division up to $256$ proves $g$ prime. All nonzero elements have order dividing $2^{16}$, so every squarefree monic degree-$r$ polynomial with nonzero constant and a nonzero rational root satisfies Eiii. Let $n=g-1$. Each of the $n$ possible roots is imposed on exactly $g^{r-1}$ monic polynomials, and each pair on $g^{r-2}$. If a polynomial has $b$ of these roots, then $1$ when $b>0$ and $0$ when $b=0$ is at least $b-\binom b2$. Summing over polynomials gives at least $ng^{r-1}-\binom n2 g^{r-2}>g^r/2$ polynomials with such a root, since $n/g-n(n-1)/(2g^2)=1/2+(g-2)/(2g^2)$. Remove at most $g^{r-1}$ polynomials with zero constant. The non-squarefree polynomials are covered by multiples of $P^2$ for monic irreducible $P$ of degree $1\le a\le r/2$. There are at most $g^a$ such $P$ of each degree and each square divides $g^{r-2a}$ monic polynomials, so this removes less than $g^r/(g-1)$. The remaining family has more than $g^r/3$ members, since $1/g+1/(g-1)<1/6$. But $100<2^7$ and $\log2<1$ imply $\log100<7$. The proposed coefficient is less than $1/76+8/65536<1/3$. The original size and auxiliary-prime hypotheses hold.

**The actual second slot.** At host index $i\in\mathrm{Fin}\,2$, `counts_of_sqf` installs primality of $g=D.\mathrm{host}.g(i)$, specializes at $r=D.R.r$ and supplies the primes and their residues from `D.host.hyp`. It derives the size bounds on $q,d$ from `qd_big`, the positivity of the odd parameter $D.R.t$ and $r\ge100$. The admissibility component of `TieAdmG` gives $g\equiv1\bmod(D.\mathrm{host}.QS\cdot qd)$. The tower divisibility $2^{e+2}\mid D.\mathrm{host}.QS$ gives the required smaller modulus. The four slots are for Eii, Eiii, Eiv and Ev, in order. The second calls `h4` with the original fixed $c$ and finite family $T$. The closed `counts_closed` supplies `squarefree_root_shift` at that argument. The host Eiii uses the same definitions in the `CyclotomicNorms` namespace. [A2 ExplicitFormulaCounts/SqfCounts.lean:18–45, StmtLocFOfCountsAll.lean:61–94 and CyclotomicNorms/StatementT.lean:9–26](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

In `propW_of_counts` the second projection `Ciii` bounds the cardinality of the Eiii filter at each fixed $c$. The lemma `wt_le_count` multiplies the count by the per-label bound from `lawL`, cancelling $g^r$ and leaving $(1+C_Lr/g)$ times the coefficient. The other place weights sum to at most one per coordinate, so the product-weight sum for a single place is bounded by that place’s filter. For each place $v$ and index $j$, the tuple argument applies the estimate to $c=\chi_T(i,v,j)$ and to its inverse. If $B$ is the coefficient of the second count, summing both gives $2(D.R.f)(D.R.m)(1+C_Lr/g)B$, the Eiii term of the weight bound. The other three proofs are [§4.10.23 for Eii](#41023-when-prime-to-parts-of-roots-collide), [§4.10.19 for Eiv](#41019-rational-factors-and-the-seven-eighths-bound-for-squarefree-degree-splits) and [§4.10.18 for Ev](#41018-counting-the-prime-degree-factor-exception). The wider bad-set and irreducibility supplies retain their named interfaces. [A2 StmtLocFOfCountsAll.lean:9–39,98–111,113–146,154–181,282–294,319–328 and LocalShareBounds.lean:58–69](../sources/SOURCES.md#chapter-4-41021-counting-roots-after-translation-by-a-unit)

**Reading boundary.** This count has author-level local R3 and a same-source initial review of all five audited claims. Independent-source adjudication and Lean kernel replay are [Open]. The bad-set counts and their two selection calls are in [§4.10.22](#41022-how-exceptional-prime-sets-avoid-each-other). The producer of `lawL` and the deeper irreducibility inputs keep their own evidence.

### 4.10.22 How exceptional prime sets avoid each other

#### Motivation

The first squarefree label count tests prime-to-$\ell$ parts of roots for primes outside a set $BB(N,g)$ attached to the host $g$. Two hosts with disjoint bad sets ensure that every prime lies outside at least one bad set. There are two counting problems. First, how many bad elements can a single host have? Second, as $g$ varies in one interval, how many hosts can have even one bad element in common with a fixed host? The second question leads from a large prime power in $g^d-1$ to a sparse set of residue classes. [First squarefree count](#41023-when-prime-to-parts-of-roots-collide) · [Source map](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

#### Two integer examples [Expository]

Here $\mathrm{Exc}_{g,d}$ means the set of primes whose full prime-power factor in $g^d-1$ has fourth power greater than $g^d$. The set $BB(N,g)$ contains $g$ and the union of these sets for $1\le d\le N$. Both examples use the archive definitions.

**Example 1.** Take the real endpoint $Y=5/2$, $N=2$ and the fixed base $g_1=3$. The window contains exactly $3,4,5$. The factorization of each $g^d-1$ and the resulting sets are as follows.

| $g$ | $g-1$ and $\mathrm{Exc}_{g,1}$ | $g^2-1$ and $\mathrm{Exc}_{g,2}$ | $BB(2,g)$ |
|---|---|---|---|
| $3$ | $2$, $\{2\}$ | $2^3$, $\{2\}$ | $\{2,3\}$ |
| $4$ | $3$, $\{3\}$ | $3\cdot5$, $\{3,5\}$ | $\{3,4,5\}$ |
| $5$ | $2^2$, $\{2\}$ | $2^3\cdot3$, $\{2,3\}$ | $\{2,3,5\}$ |

The fourth powers used are $16,4096$ for the two entries at $g=3$, $81$ and then $81,625$ at $g=4$, and $256$ and then $4096,81$ at $g=5$. Each exceeds the corresponding $g^d$. A prime absent from a factorization has prime-power factor $1$ and cannot enter. Thus the entire conflicting set $S$ is $\{3,4,5\}$. At $g=3$, the common prime $2$ is exceptional at both degrees and $3$ comes from both copies of the singleton. At $g=4$, the only common prime is $3$, exceptional at both degrees for $4$ and the singleton for $3$. At $g=5$, the common prime $2$ is exceptional at both degrees on both sides and $3$ comes from degree two for $5$ and the singleton for $3$. This last candidate lies in two of the filters indexed by common primes. The base $4$ is composite. For $\ell=3$ at degree one, the exceptional filter is just $\{4\}$ with modulus $3$. At degree two it is $\{4,5\}$, with common modulus $3$ and two root classes $1,2$. At $\ell=2,d=2$, the filter is $\{3,5\}$, both valuations are three, and the common modulus is $8$. In each case $Y<M^4$. Here $B(5/2,2)\ge119>3$, since $P(5/2)\ge2$.

**Example 2.** Take $Y=9/2$, $N=1$ and $g_1=7$. Here the entire integer window is $\{5,6,7,8,9\}$.

| $g$ | $g-1$ | $\mathrm{Exc}_{g,1}$ | $BB(1,g)$ | Common elements with $BB(1,7)$ |
|---|---|---|---|---|
| $5$ | $2^2$ | $\{2\}$ | $\{2,5\}$ | $2$ from degree one on both sides |
| $6$ | $5$ | $\{5\}$ | $\{5,6\}$ | none |
| $7$ | $2\cdot3$ | $\{2,3\}$ | $\{2,3,7\}$ | $2,3$ from degree one and $7$ from the singleton on both sides |
| $8$ | $7$ | $\{7\}$ | $\{7,8\}$ | $7$ from degree one for $8$ and from the singleton for $7$ |
| $9$ | $2^3$ | $\{2\}$ | $\{2,9\}$ | $2$ from degree one on both sides |

The fourth powers are $256,625,16,81,2401,4096$ in row order, with two entries in the row for $7$. They all clear the strict threshold. The conflicting set is exactly $S=\{5,7,8,9\}$. For the common element $\ell=7$, the special candidate $g=7$ and the exceptional candidate $g=8$ contribute through different branches. The pair $7,6$ has disjoint bad sets within this window. The bound is $B(9/2,1)\ge20>4$, using $P(9/2)\ge2$. These bases illustrate the integer selection problem. The host-prime consumers impose additional norm and primality conditions.

#### Definitions

For $g,d,\ell\in\mathbb N$ use the archive's predicates
$$
\begin{aligned}
\operatorname{Exc}(g,d,\ell)
 &\iff \ell\text{ is prime and } g^d<\ell^{4v_\ell(g^d-1)},\\
\mathrm{Exc}_{g,d}&=\{\ell:\operatorname{Exc}(g,d,\ell)\},\\
BB(N,g)&=\{g\}\cup\bigcup_{d=1}^N\mathrm{Exc}_{g,d}.
\end{aligned}
$$
The valuation is the archive's $\mathrm{padicValNat}$ and on the positive integers used here it is the exponent in prime factorization. The union at $N=0$ is empty. Even for composite $g$ the singleton is present. Write
$$
P(Y)=Y^{3/4}+1,\qquad
B(Y,N)=(3N+1)(1+2N^2P(Y)).
$$
Cardinalities in real inequalities are cast to $\mathbb R$. [A2 CyclotomicNorms/StatementI.lean:10–27](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

#### Lemmas and theorem [Lean, read]

**The bad set of one base ($\mathrm{BBCount}$).** For every natural $g\ge2$ and every natural $d\ge1$, $\mathrm{Exc}_{g,d}$ is finite with at most three members. For every natural $N$, $BB(N,g)$ is finite and has cardinality at most $3N+1$.

**Roots modulo a prime power ($\mathrm{RootsOfUnityCount}$).** For every prime $\ell$ and natural $w,d\ge1$, the congruence $x^d\equiv1\bmod\ell^w$ has at most $2d$ residue classes. For $\ell\ne2$ it has at most $d$, which implies the archived first bound $d\ell^{v_\ell(d)}$.

**Fixed-element bounds.** Let $Y\ge2$ be real and $T\subseteq\mathbb N\cap[Y,2Y]$ be finite. For any natural $\ell$ and $d\ge1$, if $\operatorname{Exc}(g,d,\ell)$ holds for every $g\in T$, then $|T|\le2dP(Y)$. For any natural $\ell,N$, if $\ell\in BB(N,g)$ for every $g\in T$, then $|T|\le1+2N^2P(Y)$.

**The choice bound ($\mathrm{ChoiceCount}$).** For every real $Y\ge2$, every natural $N\ge1$ and every natural $g_1$ with $Y\le g_1\le2Y$, every finite set $S$ of natural numbers satisfying
$$
\forall g\in S,\qquad Y\le g\le2Y,\qquad BB(N,g)\cap BB(N,g_1)\ne\varnothing
$$
has cardinality $|S|\le B(Y,N)$. Both $g$ and $g_1$ may be composite. [A2 StatementI.lean:14–27 and DivLeRpowThreeQuarters.lean:66–221](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

#### Proofs

**At most three primes at one degree.** Put $m=g^d$ and $n=m-1$. Then $m\ge2$ and $1\le n<m$. An exceptional prime must divide $n$, since valuation zero gives $1$ on the right of the strict test. This proves finiteness, including $n=1$. If there were four distinct exceptional primes $\ell_1,\ldots,\ell_4$, put $L_i=\ell_i^{v_{\ell_i}(n)}$. The product $\prod_i L_i$ divides $n$ by unique factorization, whereas $\prod_i L_i^4>m^4$ by the exceptional tests. Therefore $n^4\ge(\prod_i L_i)^4>m^4$, contrary to $n<m$. The Lean helper compares the product over the full filtered prime factor set and uses the same upper bound $n^4<m^4$. Start the union at $BB(0,g)=\{g\}$. Adding one degree adds at most three elements, giving $3N+1$ by induction. [A2 ExceptionalPrimesFiniteCardLe.lean:8–91](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

**At most $2d$ root classes.** Every root is a unit with inverse $x^{d-1}$. In a cyclic group of order $m$, write $x=u^j$ for a generator $u$. The congruence $dj\equiv0\bmod m$ has $\gcd(d,m)\le d$ solutions modulo $m$. More generally, if $H$ is a cyclic subgroup of a finite abelian group $G$, each coset of $H$ contains at most $d$ roots. If $x$ is one root in the coset, then $xh$ is a root exactly when $h^d=1$. This yields the bound $[G:H]d$ used by the archive. Its proof expresses the same count via the kernel of the power map.

For odd $\ell$, the units modulo $\ell^w$ are cyclic. Here is the construction behind the classical theorem. Every finite subgroup of a field's multiplicative group is cyclic. Indeed its exponent $e$, the least common multiple of element orders, is attained by one element. For each prime dividing $e$, take the corresponding maximal prime-power part of an element order and multiply elements of those pairwise coprime orders. For commuting elements of coprime orders, a power killing the product must kill each factor, since their cyclic subgroups intersect only in the identity. Thus the product has order $e$. Every group element solves $X^e=1$ and the field polynomial has at most $e$ roots. The element of order $e$ therefore generates the group. In particular there is a generator modulo $\ell$.

For $a=1+\ell^b u$ with $b\ge1$ and $\ell\nmid u$, the binomial expansion of $a^\ell-1$ has a first term of valuation $b+1$, middle terms of valuation at least $2b+1$, and a last term of valuation $\ell b>b+1$. Iteration gives $v_\ell((1+\ell)^{\ell^j}-1)=j+1$, so $1+\ell$ has order $\ell^{w-1}$ modulo $\ell^w$. For $w=1$ its order is one. For $w>1$ the stated power kills it and the previous power does not, which suffices since its order divides $\ell^{w-1}$. Lift a generator modulo $\ell$ to a unit modulo $\ell^w$ by taking an integer representative. Its order $t$ is divisible by $\ell-1$ since reduction is a homomorphism. Raising this lift to $t/(\ell-1)$ gives a unit of order $\ell-1$. Its product with $1+\ell$ has order $\ell^{w-1}(\ell-1)$, the number of units obtained by excluding the multiples of $\ell$. This proves cyclicity and the bound $d$.

For $\ell=2,w=1$ there is only one unit. For $w\ge2$ the subgroup generated by $5$ has order $2^{w-2}$. In fact $v_2(5-1)=2$, and every $a=5^{2^j}$ is $1\bmod4$, so $v_2(a^2-1)=v_2(a-1)+1$ by factoring $(a-1)(a+1)$. Thus $v_2(5^{2^j}-1)=j+2$. The stated order follows by the same divisibility and previous-power test, with $w=2$ giving the identity. There are $2^{w-1}$ units, so the subgroup has index two. The coset bound gives $2d$. For example all four units modulo $8$ square to $1$, so a uniform bound $d$ would fail at $d=2$. [A2 CardPowEqOneLeOfIsCyclicUnits.lean:6–87](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other) · [Gauss, Disquisitiones Arithmeticae, Arts. 85–91](https://la.wikisource.org/wiki/Disquisitiones_arithmeticae/Sectio_tertia#III.85)

**A single modulus for a fixed exceptional prime and degree.** The empty case of the first fixed-element bound has cardinality zero. Otherwise choose $g_0\in T$ minimizing $v_\ell(g^d-1)$ and set $w=v_\ell(g_0^d-1)$. The exceptional test at $g_0$ gives primality of $\ell$ and $w\ge1$, since $g_0^d\ge g_0\ge Y\ge2$. Set $M=\ell^w$. The minimum gives $M\mid g^d-1$ for every $g\in T$. The threshold at that minimum gives
$$
Y\le g_0\le g_0^d<M^4.
$$
Thus the image of $T$ modulo this **one** $M$ is contained in the at most $2d$ root classes of $x^d=1$. In any such class, if its fiber in $T$ has $t\ge1$ members, successive members differ by at least $M$. Its largest and smallest members differ by at most $2Y-Y=Y$. Hence $(t-1)M\le Y$ and $t\le Y/M+1$. This bound also holds for an empty fiber. Since $M>Y^{1/4}$ and $Y>0$, one has $Y/M<Y^{3/4}$. Summing over the image proves $|T|\le2dP(Y)$. The interval length is a real number throughout. [A2 DivLeRpowThreeQuarters.lean:10–140](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

**A fixed bad element in varying bases.** Filter $T$ by $g=\ell$ and also by $\operatorname{Exc}(g,d,\ell)$ for each $d=1,\ldots,N$. These filters cover $T$ when all its bad sets contain $\ell$. The first filter has at most one member. The first and exceptional branches are disjoint, since for prime $g=\ell$ one has $g^d-1\equiv-1\bmod\ell$, and for composite $\ell$ the exceptional branch is empty. Filters for different degrees can overlap. Each degree filter has at most $2dP(Y)\le2NP(Y)$ members, so
$$
|T|\le1+\sum_{d=1}^N2NP(Y)=1+2N^2P(Y).
$$
For $N=0$ only the singleton filter occurs. This explains the additive $1$ even when the fixed bad element is composite. [A2 DivLeRpowThreeQuarters.lean:142–187](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

**A fixed bad set.** Write $F=BB(N,g_1)$. It is finite with $|F|\le3N+1$, since $g_1\ge Y\ge2$. For $\ell\in F$ use the filter $S_\ell=\{g\in S:\ell\in BB(N,g)\}$. The intersection hypothesis says $S=\bigcup_{\ell\in F}S_\ell$. Each filter satisfies the preceding fixed-element bound. Adding the bounds gives $|S|\le |F|(1+2N^2P(Y))\le B(Y,N)$. Summing is valid when several $\ell$ witness the same intersection. The filters are a cover. Their cardinality sum is an upper bound. In Lean, `choiceCount_of` uses `BBCount` and `RootsOfUnityCount` for these two steps, and `choice_count` supplies both proofs. The argument consumes the lower bound on $g_1$ through $g_1\ge2$. The original contract also retains its upper endpoint and $N\ge1$. A nonempty set of candidates can contain its fixed base. [A2 DivLeRpowThreeQuarters.lean:189–221](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

#### Remarks

**Which hypotheses carry the estimate [Expository].** Keep $Y=2,N=1,g_1=3$ and drop only the upper endpoint for the varying $g$ in `ChoiceCount`. Take the $28$ distinct numbers $g=1+2^j$ for $2\le j\le29$. Each is above $Y$, has $v_2(g-1)=j$, and satisfies $1+2^j<2^{4j}$. The common prime $2$ is exceptional at degree one for $3$ and for every $g$ in this family. Yet $B(2,1)=4(1+2(2^{3/4}+1))<28$ since $2^{3/4}<2$. This defeats the full choice conclusion under that deletion.

For a separate weakening of the fixed-prime lemma, replace the large-power test by ordinary divisibility $\ell\mid g^d-1$, keeping primality. Take $Y=4096=8^4$, $\ell=2$, $d=1$, and all odd integers from $4097$ to $8191$. They satisfy the weakened test in $[Y,2Y]$, and there are $2048$ of them, exceeding $2dP(Y)=1026$. The minimum valuation is one, attained at $4099$, so the common modulus $2$ fails $Y<M^4$. This defeats the fixed-prime cardinality bound with the weakened predicate. The same weakening also defeats the three-prime bound at $g=211,d=1$, since $210=2\cdot3\cdot5\cdot7$. These are changes to the stated hypotheses, and the two earlier worked examples use the original predicate.

**Choosing the second host [Lean, read].** Let $G\subseteq\mathbb N\cap[Y,2Y]$ be finite with $|G|>B(Y,N)$. Fix any $a\in G$. The subfamily of $G$ whose bad sets intersect $BB(N,a)$ has size at most $B(Y,N)$. Its complement contains $b$. Then the bad sets are disjoint, and $b\ne a$ since $a\in BB(N,a)$. Both actual Lean selectors implement this budget with $N=r$, candidate lower bound $Y^{9/10}\le |G|$, and the strict window inequality $20r^3<Y^{3/20}$. Indeed for $Y,r\ge1$ put $U=Y^{3/4}\ge1$. Then $3r+1\le4r$ and $1+2r^2(U+1)\le5r^2U$, so $B(Y,r)\le20r^3U<Y^{9/10}$. The short-norm selector argues against the absence of a distinct disjoint pair, explicitly including $g=a$ using the singleton. The global interpolation selector fixes $a$ first and rules out intersection with every candidate. [A2 typePrimesN.lean:9–49 and ExistsTwoLargeNormOnePrimes.lean:17–52](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

| Actual call to `choice_count` | Parameters and independent supplies |
|---|---|
| `GlobalTheory.EX.exists_pair_disjoint_exceptional` | `two_type_primes` uses $N=r=R.r$, $Y=(R.k\,s.b)^8$, and takes all candidates for $S=G$. The fixed $g_1=a$ is chosen from $G$. Here $G$ filters the naturals from $0$ to $\lfloor2Y\rfloor$ by primality, $Y\le g$ and `GlobalTheory.EX.NormOne` at the discriminant parameter $d$ and ray modulus. `NormPrimes` gives $Y^{9/10}\le |G|$ under `RankVal`, `ModRow`, $s.\mathrm{eps}=\varepsilon$, $0<\varepsilon<1/52$ and sufficiently large $s.x$. The rank and scale supplies give $r\ge1$, $r\le(s.x)^5$ and $(s.x)^{16}\le s.b$. The additional threshold $s.x\ge21$ gives $20r^3<s.b\le R.k\,s.b\le Y^{3/20}$. [A2 ExistsTwoLargeNormOnePrimes.lean:33–96](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other) |
| `UpperTheory.T3.exists_pair_disjoint` | `typePrimesN` uses $N=r$, $Y=(kE)^8$, $E=\exp(x^\varepsilon)$, and $S=G=\texttt{normPrimes}(d,M,Y,2Y)$ with ray modulus $M$ and discriminant parameter $d$. This filter uses $Y<g\le2Y$, primality and `GlobalTheory.Mem.An.NormOne`. The fixed $g_1$ is any member furnished by positive cardinality. `normPrimesN` supplies $Y^{9/10}\le |G|$ from `ShortNorm`, `ModAt`, $0<\varepsilon$, sufficiently large $x$, and $8x^\varepsilon\le\log Y$. The size inputs $1\le k$, $1\le r\le x^5$ and the eventual comparison `poly_le_exp`, $21x^{15}\le E$ with $x\ge1$, give $20r^3<E\le kE\le Y^{3/20}$. [A2 typePrimesN.lean:29–129 and normPrimesN.lean:108–110](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other) |

The $N$ in $BB(N,g)$ is the degree cutoff. The archives also use the letter $N$ for the ray modulus in surrounding selection theorems. In the second table row it is written $M$. The discriminant parameter in `NormOne` is likewise distinct from the variable degree in $\operatorname{Exc}$. The global interpolation selector passes the disjointness field into `HostGood` at modulus $4R.n\,q\,d$. The short-norm selector passes it into `levelData`, which also requires `SmallOne` to supply its auxiliary primes. The separate analytic supplies and the other host fields keep their own hypotheses. [A2 HostExistenceOfChoices.lean:179–190,222–230,280–286 and levelData.lean:36–69](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

**Reading boundary.** The four squarefree label projections are [Eii](#41023-when-prime-to-parts-of-roots-collide), [Eiii](#41021-counting-roots-after-translation-by-a-unit), [Eiv](#41019-rational-factors-and-the-seven-eighths-bound-for-squarefree-degree-splits) and [Ev](#41018-counting-the-prime-degree-factor-exception). The two prime selectors give a pair of candidate primes when their named supplies are available. The [Lean] irreducibility interface additionally requires both `IsGood` families, a chosen index whose bad set avoids the residue prime, and the stated representation, transport and characteristic-polynomial identities. Those proofs retain their prior reading scope. The local production proofs and direct selectors have author-level R3 and a same-source initial review of all five audited claims. Independent-source adjudication and Lean kernel replay are [Open]. [A2 StatementT.lean:19–52](../sources/SOURCES.md#chapter-4-41022-how-exceptional-prime-sets-avoid-each-other)

### 4.10.23 When prime-to parts of roots collide

#### Motivation

The host labels in [§4.11](#411-from-separated-inertia-lines-to-residual-irreducibility) must pass several tests at once. To bound the weight of the failures, the archive first counts the exceptional labels in the two host prime fields. For each host datum `D`, `counts_closed D` assembles four estimates in `Counts D`, in this order.

| Slot | Exceptional labels counted | Supplier |
|---|---|---|
| First | Two roots with the same prime-to part at an allowed prime | `squarefree_roots_injective` |
| Second | A root with the same prime-to part as a prescribed unit | `squarefree_root_shift` ([§4.10.21](#41021-counting-roots-after-translation-by-a-unit)) |
| Third | A divisor of a specified positive degree $a$ with $2a\le r$ | `squarefree_div_degree` ([§4.10.19](#41019-rational-factors-and-the-seven-eighths-bound-for-squarefree-degree-splits)) |
| Fourth | No irreducible divisor of prime degree $p$ in $r/2<p\le r-3$ | `sqfPrimeFactor_of primes_dyadic_range` ([§4.10.18](#41018-counting-the-prime-degree-factor-exception)) |

The first slot concerns injectivity among the roots of a single label. Its exceptional predicate is `Eii`. The four slots share the host interfaces listed in the source ledger. [A2 `ExplicitFormulaCounts/SqfCounts.lean:18–45`](../sources/SOURCES.md#chapter-4-41023-when-prime-to-parts-of-roots-collide)

Taking the prime-to-$\ell$ part of a root erases its component of $\ell$-power order. The host conditions require the roots of a label to remain distinguishable after this operation at every allowed prime $\ell$. The first squarefree count bounds the exceptional labels. When two conjugate roots collide, the power that erases their difference shortens a Frobenius orbit. When roots from distinct irreducible factors collide, the product of their minimal polynomials divides the label.

#### Examples

Fix $\ell=2$ and $r=2$. Taking the prime-to-$2$ part retains the odd-order component. We count collisions at this fixed prime. Both examples lie outside the large-parameter range of the host estimate.

**Conjugate roots over $\mathbb F_{83}$.** Trial division by $2,3,5,7$ proves primality. The polynomial $X^2+1$ is irreducible because a root in $\mathbb F_{83}$ would have order $4$, which fails to divide $82$. Adjoin $i$ with $i^2=-1$. The two roots $4i,-4i$ of $X^2+16$ are distinct and conjugate, since $83\equiv3\bmod4$. The order of $4$ divides $41$ by $4^{41}=2^{82}=1$. Both $i$ and $-i$ have order $4$, so the two prime-to-$2$ parts equal $4$. Since $83-1=2\cdot41$ and $83^2-1=8\cdot861$, the comparisons $16\le83$ and $4096\le6889$ show that $2$ is allowed at both degrees.

For the equal-minimal-polynomial branch take $e=2,j=1$. The power $L_2=8$ sends $4i$ to $4^8\in\mathbb F_{83}$. The equation $w^{82\cdot8}=1$ has $\gcd(656,6888)=328$ solutions in the cyclic group $\mathbb F_{83^2}^{\times}$, by solving the linear congruence on the exponent of a generator. All $82$ nonzero base-field elements solve it. The other $246$ have degree two and their eighth powers are fixed by Frobenius. Raising to the eighth power is injective on the odd-order subgroup, so each of these roots has the same prime-to-$2$ part as its conjugate. Conversely a collision gives this power equation. The $246/2=123$ two-element orbits give $123$ irreducible quadratic labels. The archive's budget at these indices is $656\cdot83^0=656$. For the distinct-minimal-polynomial branch both degrees are one. For each nonzero $y$, the equation $x^2=y^2$ has the roots $y$ and $-y$, of which only $-y$ is distinct from $y$. Each unordered pair is counted twice, giving $82/2=41$ split labels. The archive's budget is $83\cdot2\cdot83^0=166$.

**Distinct minimal polynomials over $\mathbb F_{67}$.** Trial division by $2,3,5,7$ again suffices. The roots $4,-4$ of $(X-4)(X+4)=X^2-16$ are distinct and have different linear minimal polynomials. The order of $4$ divides $33$ by $4^{33}=2^{66}=1$, while $-1$ has order $2$. Both prime-to-$2$ parts equal $4$. The valuations at $2$ of $67-1=2\cdot33$ and $67^2-1=8\cdot561$ are $1$ and $3$. The comparisons $16\le67$ and $4096\le4489$ give $2\notin BB(2,67)$.

In the distinct-factor branch $e=e'=1$ and $L_1=2$. Each nonzero $y$ satisfies $y^{67}=y$, and $(x-y)(x+y)=0$ gives the two solutions of $x^2=y^2$. The distinct choice gives $X^2-y^2$. Two choices give the same label exactly when they differ by sign, so there are $66/2=33$ labels. The archive's budget is $67\cdot2\cdot67^0=134$. In the equal-factor branch, $w^{66\cdot8}=1$ has $\gcd(528,4488)=264$ solutions in $\mathbb F_{67^2}^{\times}$. Removing the $66$ nonzero base-field elements leaves $198$ degree-two roots, with eighth powers fixed by Frobenius. Injectivity on the odd-order subgroup gives $198/2=99$ irreducible labels with a collision at $2$. The archive's budget is $528\cdot67^0=528$. [Source ledger](../sources/SOURCES.md#chapter-4-41023-when-prime-to-parts-of-roots-collide)

#### Definitions

Let $g$ be prime, $K=\mathbb F_g$, and $\overline K$ its algebraic closure. Write $m_z$ for the monic minimal polynomial over $K$ of $z\in\overline K$. For $e\ge1$ put $N_e=g^e-1$ and $L_e=L_p(g,e,\ell)=\ell^{v_\ell(N_e)}$, where $L_p$ denotes the archive's `Lp` and the subscript $e$ leaves $\ell$ implicit. Define
$$
BB(r,g)=\{g\}\cup\{\ell:\ell\text{ prime and }g^d<L_p(g,d,\ell)^4\text{ for some }1\le d\le r\}.
$$
For an allowed prime $\ell\notin BB(r,g)$ this gives $L_e^4\le g^e$ for every $1\le e\le r$.

If $z\ne0$ has multiplicative order $ab$, with $a$ an $\ell$-power and $\ell\nmid b$, put $P_\ell(z)=z^u$ for $u\equiv0\bmod a$, $u\equiv1\bmod b$. In `primeToPart`, the exponent is $a$ times the residue of $a^{-1}$ modulo $b$. When $b=1$, the part is $1$. The archive uses a total monoid definition, also defined at zero in the counting cover.

A label satisfies `IsLab` if it is monic of degree $r$ with nonzero constant coefficient. It satisfies `Eii` if it is such a label, is squarefree and fails the injectivity test. In other words, there are a prime $\ell\notin BB(r,g)$ and two distinct roots $x,y$ of $f$ in $\overline K$ with $P_\ell(x)=P_\ell(y)$. Root membership in the archive is in the multiset of roots of the base-changed polynomial. [A2 `SqfLab.lean:9–28`, `ClaimOf.lean:11–27`](../sources/SOURCES.md#chapter-4-41023-when-prime-to-parts-of-roots-collide)

#### Lemma and theorem

**Lemma (witnesses from a colliding pair) [Lean, read].** For a collision as above at an allowed prime $\ell$, the following conditions hold in the respective branches.

- **A, equal minimal polynomials.** There exist a root $w$ of degree $2\le e\le r$ and an integer $1\le j\le e/2$ with $\ell\mid N_e$, $m_w\mid f$ and $w^{(g^j-1)L_e}=1$.
- **B, distinct minimal polynomials.** Order the roots to have degrees $e,e'$ with $1\le e'\le e$. Then $e+e'\le r$, $\ell\mid N_eN_{e'}$, $m_xm_y\mid f$, $y^{g^{e'}}=y$ and $x^{L_e}=P_\ell(y)^{L_e}$.

**Theorem (first squarefree count) [Lean, read].** For every prime $g\ge4096$, every integer $r\ge100$ and every finite set $T\subset K[X]$ with each $f\in T$ satisfying `Eii`,
$$
|T|\le23\log(g)\,g^{-1/2}g^r .
$$

#### Proof

**Powers and Frobenius.** If $z\ne0$ has degree $e$, then $K(z)$ has $g^e$ elements by counting the coordinates in a basis. Thus $z^{g^e}=z$ and $\operatorname{ord}(z)\mid N_e$. For any positive $N$ divisible by the order of $z$ and $L=\ell^{v_\ell(N)}$, we have $z^L=P_\ell(z)^L$. Indeed $b\mid u-1$ and $a\mid L$, so $ab\mid(u-1)L$. Apply this identity with $N$ the product of the two field-group orders. If $\ell$ failed to divide the product, $L$ would be one and equality of parts would give $x=y$. In the equal-minimal-polynomial branch one can use $N=N_e$ for both roots.

Frobenius $z\mapsto z^g$ on a finite extension is a field automorphism by the characteristic-$g$ binomial identity and finiteness. Its fixed field is $K$, since all $g$ base-field elements are roots of $Z^g-Z$ and that polynomial has degree $g$. The orbit of $z$ in $K(z)$ consists of roots of $m_z$. The product of $Z-v$ over the orbit is Frobenius-invariant, hence belongs to $K[Z]$, and vanishes at $z$. Its divisibility by $m_z$ shows that the orbit has length at least $e$. It has length at most $e$ by the root bound, so it consists of all roots of $m_z$. [A2 `WitBase.lean:11–59`, `WitMain.lean:36–56` and Milne, pp. 53–55](../sources/SOURCES.md#chapter-4-41023-when-prime-to-parts-of-roots-collide)

**The witness lemma.** Each root is nonzero since $f(0)\ne0$, and its monic irreducible minimal polynomial divides $f$ by the defining property of the minimal polynomial. Its degree therefore lies between $1$ and $r$.

In A, a power of Frobenius sends $x$ to $y$. The power identity gives $z=x^{L_e}=y^{L_e}$. That automorphism fixes $z$ and every element of $K(z)$, while it moves $x$. Thus $K(z)$ is a proper subfield of $K(x)$ and $j=[K(z):K]$ is a positive proper divisor of $e$. The tower law gives $2j\le e$, and $z\ne0$ gives $z^{g^j-1}=1$. This yields A with $w=x$. The archive obtains the base-field automorphism using `Normal.minpoly_eq_iff_mem_orbit` and then proves the same proper-subfield step.

In B the two distinct monic irreducibles are coprime, so their product divides $f$ and their degrees sum to at most $r$. Order them so that $e'\le e$. The field of $y$ gives $y^{g^{e'}}=y$. Apply the power identity to $x$ at $N_e$ and use equality of parts. This gives $x^{L_e}=P_\ell(y)^{L_e}$, including when $\ell$ divides only $N_{e'}$ and $L_e=1$. [A2 `WitMain.lean:14–34,58–165`](../sources/SOURCES.md#chapter-4-41023-when-prime-to-parts-of-roots-collide)

**The finite cover.** For a fixed monic divisor $h$ of degree $d\le r$, multiplication by $h$ identifies the ambient monic degree-$r$ multiples with monic degree-$(r-d)$ quotients. Their $r-d$ coefficients below the leading term give exactly $g^{r-d}$ possibilities, bounding each filter of $T$. The root bound follows by successive division by the distinct linear factors.

Write $\mathcal L(n)$ for the set of distinct prime factors of $n>0$ outside $BB(r,g)$. In A, for fixed $e,j,\ell$, the power equation gives at most $(g^j-1)L_e$ roots of degree exactly $e$. Each $m_w$ gives at most $g^{r-e}$ labels. In B, for fixed $e,e',\ell$, the polynomial $Y^{g^{e'}}-Y$ gives at most $g^{e'}$ choices of degree $e'$ for $y$. Each $X^{L_e}-P_\ell(y)^{L_e}$ gives at most $L_e$ roots of degree $e$ for $x$. The monic product $m_xm_y$ gives at most $g^{r-e-e'}$ labels. The larger witness sets can include zero and, in B, equal minimal polynomials. A single label can appear through several witnesses, including roots from the same orbit. Summing the cover gives
$$
\begin{aligned}
|T|&\le S_A+S_B,\\
S_A&=\sum_{e=2}^r\sum_{j=1}^{\lfloor e/2\rfloor}\sum_{\ell\in\mathcal L(N_e)}
       (g^j-1)L_e\,g^{r-e},\\
S_B&=\sum_{e=1}^r\sum_{e'=1}^{\min(e,r-e)}\sum_{\ell\in\mathcal L(N_eN_{e'})}
       g^{e'} L_e\,g^{r-e-e'} .
\end{aligned}
$$
[A2 `DivCount.lean:11–48`, `TwoPowCardPrimeFactorsLe.lean:28–35`, `CardLeSumOfCover.lean:14–173`](../sources/SOURCES.md#chapter-4-41023-when-prime-to-parts-of-roots-collide)

**The geometric sums.** Put $t=g^{-1/4}$, $G=g^r$ and $H=\log g/\log 2$. The field-size guard gives $0<t\le1/8$. Each prime in either sum satisfies $L_e^4\le g^e$ by the negated defining inequality at $d=e$. Thus $L_e\le g^{e/4}$. A summand of $S_A$ is at most $Gt^e$, since $g^j-1\le g^{e/2}$. A summand of $S_B$ is at most $Gt^{3e}$, since the factor $g^{e'}$ cancels the loss $g^{-e'}$.

The product of the primes in $\mathcal L(n)$ divides $n$, and each prime is at least $2$. Hence $2^{|\mathcal L(n)|}\le n$. Taking logs and using $N_e\le g^e$ and $N_eN_{e'}\le g^{2e}$ gives bounds $eH$ and $2eH$ for the respective innermost index sets. There are at most $e/2$ choices of $j$ and $e$ choices of $e'$. Since $t^{3e}\le t^et^2$ for $e\ge1$, this gives
$$
S_A\le\tfrac12 HG\sum_{e=2}^r e^2t^e,\qquad
S_B\le2HGt^2\sum_{e=1}^r e^2t^e.
$$
Induction using $e+1\le2e$ for $e\ge1$ proves $e^2\le4^{e-1}$. Thus $e^2t^e\le t(4t)^{e-1}$. Since $4t\le1/2$, comparison with the finite geometric sum gives $\sum_{e=1}^r e^2t^e\le2t$. Starting at $e=2$ gives $t(4t)^{e-1}=4t^2(4t)^{e-2}$ and $\sum_{e=2}^r e^2t^e\le8t^2$. These estimates include empty sums. We obtain
$$
S_A\le4HGt^2,\qquad S_B\le4HGt^3,\qquad S_A+S_B\le\tfrac92 HGt^2.
$$
The archive uses `Real.log_two_gt_d9` for $\log2>1/2$, which also follows by integrating $1/u>1/2$ over $1<u<2$. Thus $H\le2\log g$, yielding $9\log(g)Gt^2$. The final comparison $9\le23$ gives the declared constant, with $t^2=g^{-1/2}$. This proves `local_orbit_count` on the witness cover. The closed export calls `claim_of` with `counted_labels_have_witness` and `local_orbit_count` to obtain the claim for the original labels. [A2 `TwoPowCardPrimeFactorsLe.lean:13–26`, `SumSqPowLeTwo.lean:13–73`, `RpowQuarterPowFour.lean:13–231`, `ClaimOf.lean:25–37`, `OrbitalBoundsConclusion/SqfRootsInj.lean:1–7`](../sources/SOURCES.md#chapter-4-41023-when-prime-to-parts-of-roots-collide)

#### Remarks

**Use of the hypotheses.** Monicity ensures the label is nonzero and fixes the leading coefficient of the quotient. For example, over $\mathbb F_{67}$ the fixed divisor $X-4$ divides all $66$ degree-one polynomials $a(X-4)$ with $a\ne0$. Its monic degree-one fiber has size $67^0=1$. The degree of the label bounds witness degrees and fixes the quotient sizes. The constant term excludes zero from the multiplicative-order argument, since zero has no positive power equal to $1$. Squarefreeness is part of `Eii` and enters the later weight conversion. The witness proof discards it, since distinct minimal polynomials are already coprime. After receiving the witnesses the cover count uses only monicity and degree. The body of `local_orbit_count` discards $r\ge100$, and it uses $g\ge4096$ for $4t\le1/2$. The prime exclusion provides the fourth-power bound. For example, $g=11$, $e=1$ and $\ell=2$ give $L_1^4=16>11$.

**A label in the stated range.** Take $g=4099$, $r=100$ and $f=(X+1)\prod_{a=1}^{99}(X-a)$. The integer $4099$ is prime by trial division by the primes at most $61$. Its $100$ roots are distinct and nonzero. The roots $1,-1$ have the same prime-to-$2$ part $1$. If $d$ is odd, then $v_2(g^d-1)=1$, since the sum remaining after factoring out $g-1$ has an odd number of odd terms. If $d=2^a b$ with $a\ge1$ and $b$ odd, factoring off the odd exponent and then repeated differences of squares gives $v_2(g^d-1)=a+2$. Indeed $v_2(g-1)=1$, $v_2(g+1)=2$ and $g^{2^k}+1\equiv2\bmod8$ for $k\ge1$. For odd $d$, $L_d^4=16<g^d$. For even $d$, $4(a+2)\le12d$ since $a\le d$ and $d\ge2$. As $g>2^{12}$, again $L_d^4<g^d$. Therefore $2\notin BB(100,4099)$, and the singleton $\{f\}$ is a legal nonempty family in the original count.

**Return to the host.** For each $k\in\mathrm{Fin}\,2$, `counts_of_sqf` installs primality at $g=D.\mathrm{host}.g(k)$ and applies its first argument `h3` at $r=D.R.r$ to the finite label set with the same guards. The host `Eii` uses identical definitions under `CyclotomicNorms`. `counts_closed` supplies `squarefree_roots_injective` as that first argument. In `propW_of_counts`, fix a place $v$ of the chosen host and take $T$ to be the filter of $S_0$ by `Eii`. Set $B=23\log(g)g^{-1/2}$. Under `TieAdmG`, the degree and size guards, $C_L\ge0$ and `lawL`, the bound `Cii` gives $|T|\le Bg^r$. The weight law bounds each summand by $(1+C_Lr/g)/g^r$ using monicity, degree, nonzero constant term and squarefreeness. Thus `wt_le_count` gives the bound $(1+C_Lr/g)B$ in `P2`. In `b2`, the one-coordinate mass bounds let `sum_pi_single` apply `P2` once per place in the product-weight sum. The two direct callers of `propW_of_counts (counts_closed …)` are `family_bound_all` and `family_count_all`.

The first projection has author-level local R3 source reading and a finite exact certificate for the two examples and the singleton. Independent review and Lean kernel replay of this projection remain open. The third projection retains its same-source initial review and the fourth its independent audit. The second projection receives the progression congruence and retains its own reading scope. The larger arithmetic and representation-theoretic inputs of `CyclotomicNorms` enter at their own interfaces. [A2 consumers and reading boundary](../sources/SOURCES.md#chapter-4-41023-when-prime-to-parts-of-roots-collide)

---

**Summary of the chapter.** Embedding a primitive Dirichlet character $\psi$ into a CM host field
$E \subset \mathbb Q(\zeta_N)$ of degree $4 c \cdot 2^e$ requires two auxiliary primes
$q \equiv 3 \pmod 8$ and $d \equiv 7 \pmod{16}$ (excluding complex conjugation so $E$ is CM over
$F = E^+$, splitting $2, q$ and all prime divisors of $\psi.N$ in $K = \mathbb Q(\sqrt{-d})$, and
providing an odd parity partner for odd $\psi$, Lemma 4.2) [Lean, read]. Choosing
$\log q \asymp Y^{\varepsilon/5}$ and $\log d \asymp Y^{\varepsilon/5}(\log Y)^2$ with $q \mid d + 1$
and small odd primes dividing $d + 1$ allows a two-stage unconditional sieve — combining a $Q^{1/4}$
zero-density bound (`zero_density_box` [Lean, read], Section 4.7), explicit-formula truncation at $Z = x^{400}$ matched
to box width $1/400$ (Lemma 4.4), $L^2$ Jacobi character-sum bounds with at most one Landau–Page
modulus (Proposition 4.5), and a dyadic Sobolev–Markov inequality (Lemma 4.6) — to produce a pair
$(q, d)$ whose parasitic twists satisfy $\lvert G_\chi(x) \rvert \le x^{1/2+\varepsilon}$ and
$\lvert L'/L(1,\chi) \rvert \le 4\log x$ on $[Y, Y^A]$ (Theorem 4.7) [Lean, read]. Rescaling
quadratic `VWin` windows from exponent $401$ to $400$ and from $[W, W^2]$ to $[Z, Z^{3/2}]$ yields
`supplyChi` (Proposition 4.8 and Theorem 4.9) [Lean, read], delivering the exact host-field package
`EAtH` consumed in Chapter 5.

### 4.10.24 Separating a real zero from 1

#### 4.10.24.1 Motivation

In a reduced residue class $b$ with $\chi(b)=1$, the exceptional term subtracts $\operatorname{li}_2(X^\beta)$ from $\operatorname{li}_2(X)$ before division by $\varphi(M)$. As $\beta$ approaches $1$ at fixed $X$, this difference approaches zero. A relative prime-counting estimate therefore needs a separate lower bound on $1-\beta$ to give a useful count. An estimate for $L(1,\chi)$ provides such a bound once we control the rate at which $L(\sigma,\chi)$ can change on the real segment from $\beta$ to $1$.

#### 4.10.24.2 Two worked substitutions [Expository]

Take the character modulo $8$ that is $+1$ on $1,7$, $-1$ on $3,5$, and zero on even integers. Its values are given by $(-1)^{(n^2-1)/8}$ for odd $n$. This is multiplicative on the units, and $1$ and $5$ have different values although they agree modulo $4$. Thus its conductor is $8$. In the class $b=1$, an exceptional term, if present, has the subtractive sign. The counting input with constant $c$ gives $1-\beta\ge c/8$.

For a second example take modulus $40$ and induce the preceding character from modulus $8$. The new character has the same signs on integers coprime to $40$ and is zero on multiples of $2$ or $5$. It is nonprincipal since its value at $3$ is $-1$. Its conductor is still $8$. The counting input now gives $1-\beta\ge c/40$. The extra Euler factor is $1+5^{-s}$, since the inducing character takes value $-1$ at $5$. At $s=1$ it multiplies the primitive value by $6/5$.

To do the threshold arithmetic by hand, insert trial values $c=1/2$, $d=1/2$, $B=C=1$, and $\varepsilon=1/100$ into the formula in §4.10.24.5. These are illustrative inputs to the formula. They do not supply witnesses for the analytic estimates. The logarithm of the threshold is
$320+20.008+8\log 8+8(\log 8)^2+\log 640<400$,
using $\log 8<2.08$ and $\log 640<6.47$. Set $x=\exp(400)$ and choose $X=M^{40000}$ in each example. Then $\log X=(\log x)^2\log M/4$. Since $2<\log 8<\log 40<4$, both choices give $80000<\log X<160000$. This meets the auxiliary lower scale $x^{\varepsilon/6}=\exp(2/3)$ and the upper scale $x^{\varepsilon/5}(\log x)^2=160000\exp(4/5)$. The trial gaps are $1/16$ at modulus $8$ and $1/80$ at modulus $40$. The corresponding requirements $\log(320/c)\le \log X/20$ hold in both cases since $\log 640<6.47<4000$. These substitutions make no assumption about the existence of a real zero for either character.

#### 4.10.24.3 Definitions and analytic inputs

A Dirichlet character modulo $M$ is a character of $(\mathbb Z/M\mathbb Z)^\times$, extended by zero on nonunits. It is real precisely when every unit value is $1$ or $-1$. Equivalently, $\chi^2$ is the principal character modulo $M$, which Lean denotes by $1$. The additional condition $\chi\ne 1$ excludes the character that is identically $1$ on the units.

The conductor $f$ is the least divisor of $M$ through whose unit group the character factors. The character of modulus $f$ inducing $\chi$ is primitive. The character of modulus $M$ is primitive when $f=M$ and imprimitive when $f<M$. If $\chi^\ast$ is the primitive inducing character, the Euler products give
$L(s,\chi)=L(s,\chi^\ast)\prod_{p\mid M,\ p\nmid f}(1-\chi^\ast(p)p^{-s})$.
The factorization first holds in $\Re s>1$ and extends by analytic continuation. Every extra factor is nonzero for $\Re s>0$ because $|\chi^\ast(p)p^{-s}|<1$ there. The progression has modulus $M$, and the inputs below are uniform at that modulus, including imprimitive characters. In particular, a primitive lower bound at $f$ needs control of the extra factors at $1$ before it can supply the required bound at $M$. [NIST DLMF, §25.15(i), equations (25.15.2) and (25.15.4)](https://dlmf.nist.gov/25.15#i)

We use the following two bounds in the form supplied by the archive.

- **Siegel lower bound** ($\texttt{SiegelLower}$) [Lean]. For each $\eta>0$ there exists $a(\eta)>0$ such that $|L(1,\chi)|\ge a(\eta)M^{-\eta}$ for every positive integer $M$ and every real nonprincipal character modulo $M$.
- **Derivative bound near 1** ($\texttt{LDerivNearOne}$). There is one constant $D$ such that for every positive integer $M$, every nonprincipal character modulo $M$, and every real $\sigma$ in $[1-1/\log(3M),1]$, one has $|L'(\sigma,\chi)|\le D\log^2(3M)$. Real-valuedness of the character is unnecessary for this bound.

We use the standard analytic continuation of $L(s,\chi)$ for nonprincipal $\chi$ and nonvanishing for real $s\ge1$. For $s>1$ the Euler product proves nonvanishing, and at $s=1$ the Dirichlet nonvanishing theorem applies. [NIST DLMF, §25.15(i)–(ii)](https://dlmf.nist.gov/25.15)

**Lemma (the derivative bound) [Lean, read].** One may take $D=76\exp(3/2)$.

**Proof.** A nonprincipal character has $M\ge3$. Put $H=\log(3M)\ge2$ and $A(t)=\sum_{1\le n\le t}\chi(n)$. The sum over a full period vanishes by character orthogonality, so $|A(t)|\le M+1$. Summation by parts for $w$ with $r=\Re w>0$ gives
$L(w,\chi)=\sum_{n\le M}\chi(n)n^{-w}-A(M)(M+1)^{-w}+R(w)$,
where
$R(w)=\sum_{n\ge M+1} A(n)(n^{-w}-(n+1)^{-w})$.
Indeed, the finite summation-by-parts identity telescopes and its last boundary term tends to zero. The series on the right converges locally uniformly for $r>0$, and agrees with $L$ by continuation from $r>1$. Integrating the derivative of $t^{-w}$ over each unit interval gives $|R(w)|\le (M+1)(|w|/r)(M+1)^{-r}$.

Suppose $r\ge1-3/(2H)$, $r\ge1/4$, and $|w|\le2$. For $1\le t\le M+1$, one has $t^{1-r}\le \exp(3/2)$, by considering the sign of $1-r$ and using $\log t\le H$. The harmonic sum now bounds the first term by $\exp(3/2)(1+H)$. The boundary term is at most $\exp(3/2)$ and the tail at most $8\exp(3/2)$. Their sum is at most $38\exp(3/2)H$, the bound used in the archive. Around any $\sigma\in[1-1/H,1]$, the circle of radius $1/(2H)$ lies in this region: its real part is at least $1-3/(2H)\ge1/4$, and its modulus is at most $1+1/(2H)\le2$. Cauchy's derivative estimate divides the circle bound by the radius, giving the stated $D$.

#### 4.10.24.4 The conditional real-zero separation theorem

**Lemma (absorbing the logarithm).** If $h>0$ and $u\ge1$, then $\log(3u)\le (\log 3+1/h)u^h$.

**Proof.** Integrate $1/t\le t^{h-1}$ from $1$ to $u$ to obtain $\log u\le (u^h-1)/h\le u^h/h$. Also $\log 3\le (\log 3)u^h$.

**Theorem (real-zero separation from the two bounds) [Lean, read].** Assume the two bounds in §4.10.24.3. For every $\delta>0$ there is $c(\delta)>0$ such that for every positive integer $M$, every real nonprincipal character $\chi$ modulo $M$, and every real $\beta$ with $L(\beta,\chi)=0$,
$\beta\le1-c(\delta)M^{-\delta}$.
The statement applies to all such real zeros. No simplicity or exceptional-region hypothesis is needed.

**Proof.** Fix $\delta>0$ and take the lower-bound witness $a=a(\delta/3)$. Put $K=\log 3+3/\delta$ and $D_+=\max(D,1)$. Choose
$c(\delta)=\min(1/K,a/(D_+K^2))>0$
before choosing $M,\chi,\beta$. Now let $U=M^{\delta/3}$ and $H=\log(3M)$. Then $U\ge1$, $H>0$, $H\le KU$, and $M^{-\delta}=U^{-3}$. Nonvanishing on the real half-line $[1,\infty)$ implies $\beta<1$.

If $\beta\le 1-1/H$, then $1-\beta\ge 1/H\ge 1/(KU)\ge c(\delta)U^{-3}$. Otherwise the entire interval $[\beta,1]$ is in the derivative range. The fundamental theorem of calculus for the restriction of $L$ to the real segment and $L(\beta,\chi)=0$ give
$|L(1,\chi)|\le \int_\beta^1 |L'(\sigma,\chi)|\,d\sigma\le D_+K^2U^2(1-\beta)$.
The lower bound at exponent $\delta/3$ gives $|L(1,\chi)|\ge a/U$. Division by $D_+K^2U^2$ yields $1-\beta\ge aU^{-3}/(D_+K^2)\ge c(\delta)U^{-3}$. The three powers of $U$ account for the exponent: one comes from the lower bound at $1$ and two come from the derivative estimate.

#### 4.10.24.5 The constant actually used by the counting proof

Write $d,B,C$ for the relative progression constants $c_3,A_0,C_0$ in Lean. First fix $\varepsilon>0$ and obtain the uniform relative progression estimate with $d>0$. In `count_a`, apply the separation theorem at $\delta=1$ once and call its witness $c_0$. With the witness constructed in §4.10.24.4, $c_0=\min(1/(\log 3+3),a(1/3)/(D_+(\log 3+3)^2))$. Put $c=\min(c_0,1)$, so $0<c\le1$. The implication $L(\beta,\chi)=0\Rightarrow\beta\le1-c/M$ for real nonprincipal $\chi$ can now be specialized to any chosen modulus. This specialization is the hypothesis `hcb` of `count_pos`. The relative-error exponent $d$ comes from the progression estimate.

For each $M$ with $8\mid M$, the relative progression supplier chooses an option $e$ fixed for that modulus. If $e$ contains $(\chi_1,\beta_1)$, the conditions of `IsExcPair` give $\chi_1^2=1$, $\chi_1\ne1$, and $L(\beta_1,\chi_1)=0$, along with $1-1/(8\log M)<\beta_1<1$. In the subtractive case $\chi_1(b)=1$, put $L=\log X\ge4$. Then $X^{\beta_1}\ge2$ and
$X-X^{\beta_1}\ge X(1-\exp(-c/M))\ge cX/(2M)$.
The first inequality uses $(1-\beta_1)L\ge c/M$. The second uses $0<c/M\le1$ and the convexity bound $\exp(-v)\le1-v/2$ on $[0,1]$. Integrating $1/\log t$ from $X^{\beta_1}$ to $X$ gives at least $(X-X^{\beta_1})/L$. The empty option and the nonsubtractive case already have the lower bound $(X-2)/L$ before division by $\varphi(M)$. Using $\varphi(M)\le M$ gives the uniform lower bound $cX/(2LM^2)$ for the progression main term. This is the point where the separation constant enters `mainAP_lower`.

Set $J=\log(4(|B|+1))$. The exact uniform threshold chosen in `count_a` is
$x_0=\exp\big(320+4|C|(5+\varepsilon/5)+|4J/d|+|4J^2/d|+|\log(320/c)|\big)$.
For all $x\ge x_0$, positive $X$, positive integers $M$ divisible by $8$, and $b$ coprime to $M$, the positive branch invokes `count_pos` when
$(\log x)^2\log M/4\le\log X\le x^{\varepsilon/5}(\log x)^2$.
The outer `count_a` also accepts $x^{\varepsilon/6}\le\log X$, which the call in the positive branch does not use. The threshold enforces the range and relative-error conditions in [§4.9](#49-counting-enough-candidates-before-the-sieve). In particular, $\log x\ge320$ and $\log M\ge1$ give $L\ge80\log x$ and hence $\log(320/c)\le L/20$. Along with $L\ge80\log M$, these are the two size conditions that convert the main-term lower bound into $4X^{9/10}$ in [§4.9](#49-counting-enough-candidates-before-the-sieve). The conclusion is at least $X^{9/10}$ primes in $(\sqrt X,X]$ in the class $b$.

The displayed formula expresses the threshold in terms of the witnesses. The Siegel input asserts existence of $a(\eta)$ and leaves its numerical value as an input to this deduction. The derivative constant and logarithm bound are explicit, but this proof supplies neither an effective $c_0$ nor an effective numerical $x_0$. The same witness works simultaneously for all moduli and characters. An effective bound for a fixed modulus would address a different quantifier order.

#### 4.10.24.6 Notes and source map

[Source register](../sources/SOURCES.md#chapter-4-real-zeros-and-the-siegel-product)

The direct producer of `ExcBound` is the two-input theorem `exceptional_zero_bound_of`. The file named `LogDerivRegionChiOf` declares both `LDerivNearOne` and `ExcBoundOf`, and it also declares a separate proposition controlling the *logarithmic* derivative with exceptional poles subtracted. The proof here uses the ordinary derivative of $L$. In the supplier file, `excBound_of_siegelLower` inserts the ordinary derivative bound, and `excBound` inserts `siegelLower` from `FinalSiegel`. The neighboring Siegel–Walfisz statement is another consumer of this separation.

All archive paths below are relative to the extracted Lean root of the [pinned release](../sources/SOURCES.md#1-the-lean-archive-primary-source), SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

| Role and read status | Declaration and archive location |
|---|---|
| Statements and dependency arrows | `LDerivNearOne`, `ExcBound`, `ExcBoundOf`, `SiegelWalfiszOf`, `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:45–52,78–80` |
| Lower-bound statement [Lean] | `SiegelLower`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean:29–31` |
| Derivative estimate [Lean, read] | `lfunction_norm_le_near_one` and `lfunction_deriv_near_one` with the preliminary estimates, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean:10–159` |
| Separation proof [Lean, read] | `log_le_const_mul_rpow`, `rpow_neg_eq_inv_pow`, `exceptional_zero_bound_of`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExcBoundOf.lean:9–102` |
| Direct assembly [Lean, read] | `excBound_of_siegelLower`, `excBound`, and neighboring use in `siegelWalfisz_of_siegelLower`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:26–34` |
| Lower-bound assembly [Lean] | `bqKey`, `siegelLower`, `src/Formalism/LandauZeroFreeBounds/FinalSiegel.lean:14–19` |
| Exceptional pair | `IsExcPair`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MeanSquareHypWIff.lean:29–32` |
| Counting specialization [Lean, read] | `mainAP_lower`, `count_pos`, `count_a`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean:86–173,175–203,275–397`; production call in `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMain.lean:58` |

The local reading covers the elementary reduction, the ordinary derivative estimate with its partial-sum and Cauchy steps, and the stated counting specialization. The summation-by-parts representation of $L$, Dirichlet nonvanishing and Cauchy's estimate are standard inputs. The conditional proof through `siegel_theorem_of` is developed in [§4.10.25](#41025-the-siegel-lower-bound-from-biquadratic-product-series). The regularization and circle bound it uses are developed in [§4.10.26](#41026-regularizing-the-four-factor-product-and-bounding-its-taylor-remainder). The assembly in `FinalSiegel` identifies its producers and carries no full-proof reading claim. Siegel's original paper gives the classical context for the lower bound. [Siegel1935, pp. 83–86](https://doi.org/10.4064/AA-1-1-83-86)

### 4.10.25 The Siegel lower bound from biquadratic product series

#### 4.10.25.1 Motivation

[§4.10.24](#41024-separating-a-real-zero-from-1) reduced the real-zero separation `ExcBound` to two analytic inputs: the explicit derivative bound `LDerivNearOne` near $s = 1$, proved there with $D = 76\exp(3/2)$, and the named lower bound `SiegelLower`, which asserts that for every $\delta > 0$ there is a constant $c_\delta > 0$ such that $\lVert L(1, \chi) \rVert \ge c_\delta q^{-\delta}$ for every positive modulus $q$ and every real nonprincipal character $\chi \bmod q$. In Section 4.10.24.5, specializing `ExcBound` at exponent $1$ supplied the uniform counting threshold in `count_a` and `count_pos`.

How can one bound $L(1, \chi)$ from below without first knowing where the real zeros of $L(s, \chi)$ lie? The auxiliary product $\zeta(s)L(s, \chi)$ has nonnegative Dirichlet coefficients $(1 \ast \chi)(n) \ge 0$ and a simple pole at $s = 1$ with residue $L(1, \chi)$, and positivity alone leaves its size to be controlled. Siegel’s method uses two real characters $\chi_1 \bmod q_1$ and $\chi \bmod q$ together in the four-factor biquadratic product
$\displaystyle F(s) := \zeta(s)\,L(s, \chi_1)\,L(s, \chi)\,L(s, \psi),$
where $\psi \bmod q_1 q$ represents the pointwise product of $\chi_1$ and $\chi$ on $(\mathbb Z/q_1 q\mathbb Z)^\times$. When $\chi_1, \chi, \psi$ are all nonprincipal, $F(s)$ has only a simple pole at $s = 1$ with residue $\lambda = L(1, \chi_1)L(1, \chi)L(1, \psi)$, while its Dirichlet series still has **nonnegative** coefficients and leading term $1$. The Taylor method presented by Montgomery and Vaughan (Lemma 11.13) expands $G(s) := F(s) - \lambda/(s - 1)$ in a Taylor series around $s = 2$ and leads here to the lower bound $\frac{1}{2} - C\lVert \lambda \rVert (q_1 q)^{K(1-\sigma)}/(1 - \sigma)$ for $\Re F(\sigma)$ at every $\sigma \in [7/8, 1)$. Fixing **one** reference character $\chi_1 \bmod q_1$ and abscissa $\sigma$ depending only on $\delta$ — taken at an exceptional real zero $\beta \in [\sigma_0, 1)$ if any exists across all moduli, and otherwise at $\sigma_0$ itself using $\zeta(\sigma_0) < 0$ — forces $\Re F(\sigma) \le 0$ for every $\chi$ with $\psi \neq 1$, which rearranges to $\lVert L(1, \chi) \rVert \ge c_\delta q^{-\delta}$. When $\psi = 1$, $\chi_1$ and $\chi$ share the same underlying primitive character and a finite Euler-factor comparison across the prime divisors of $q_1 q$ handles $\chi$ directly.

#### 4.10.25.2 Two hand calculations [Expository]

Before stating the formal interfaces, we test both branches of the archive's construction on concrete real nonprincipal characters.

**Example 4.10.25.1 (A genuinely biquadratic pair with $\psi \neq 1$: an odd character modulo $4$ and an even character modulo $5$).** Take $\chi_1 = \chi_4 \bmod 4$, the archive's explicit witness `characterModFour` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean:36`), defined by $\chi_4(1) = +1$, $\chi_4(3) = -1$, and $\chi_4(n) = 0$ for even $n$ (odd: $\chi_4(-1) = -1$, primitive of conductor $4$, corresponding to negative fundamental discriminant $-4$). Pair it with the Legendre symbol $\chi_2 = \chi_5 \bmod 5$, defined by $\chi_5(1) = \chi_5(4) = +1$, $\chi_5(2) = \chi_5(3) = -1$, and $\chi_5(5k) = 0$ (even: $\chi_5(-1) = +1$, primitive of conductor $5$, corresponding to positive fundamental discriminant $+5$). Their level-lifted product $\psi \bmod 20$ satisfies $\psi(n) = \chi_4(n)\chi_5(n)$ for every $n \in \mathbb N$: on the eight reduced classes $(1, 3, 7, 9, 11, 13, 17, 19) \bmod 20$ it takes values $(+1, +1, +1, +1, -1, -1, -1, -1)$, and it vanishes whenever $2 \mid n$ or $5 \mid n$. Because $\psi(11) = -1 \neq 1$, $\psi$ is nonprincipal (primitive of conductor $20$, odd, corresponding to discriminant $-20$). Notice that negative and positive discriminants enter symmetrically with no separate case analysis.

For $\Re s > 1$, $F(s) = \zeta(s)L(s, \chi_4)L(s, \chi_5)L(s, \psi) = \sum_{n=1}^\infty f(n)n^{-s}$ has local Euler factor
$\displaystyle E_p(s) = (1 - p^{-s})^{-1}(1 - \chi_4(p)p^{-s})^{-1}(1 - \chi_5(p)p^{-s})^{-1}(1 - \psi(p)p^{-s})^{-1}$
and multiplicative coefficients $f = (1 \ast \chi_4) \ast (\chi_5 \ast \psi)$. Representative primes display every case of the archive's coefficient proof (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean:63–72`):

1. **Double-inert prime $p = 3$, with $(\chi_4(3), \chi_5(3), \psi(3)) = (-1, -1, +1)$.** The local Euler factor is
   $\displaystyle E_3(s) = (1 - 3^{-s})^{-2}(1 + 3^{-s})^{-2} = (1 - 3^{-2s})^{-2} = \sum_{m=0}^\infty (m + 1)\,3^{-2ms}.$
   In the archive's divisor-convolution formula, $(1 \ast \chi_4)(3^a) = \sum_{i=0}^a (-1)^i = \mathbf{1}_{2 \mid a}$ and $(\chi_5 \ast \psi)(3^b) = (-1)^b \mathbf{1}_{2 \mid b} = \mathbf{1}_{2 \mid b}$. Hence $f(3^k) = \sum_{a+b=k,\,2\mid a,\,2\mid b} 1$ equals $0$ when $k$ is odd ($f(3) = f(27) = 0$) and $k/2 + 1$ when $k$ is even ($f(1) = 1$, $f(9) = 2$, $f(81) = 3$).
2. **Ramified prime $p = 2$, with $(\chi_4(2), \chi_5(2), \psi(2)) = (0, -1, 0)$ (the swap branch).** The local Euler factor is
   $\displaystyle E_2(s) = (1 - 2^{-s})^{-1}(1 + 2^{-s})^{-1} = (1 - 2^{-2s})^{-1} = \sum_{m=0}^\infty 2^{-2ms},$
   so $f(2^k) = \mathbf{1}_{2 \mid k}$ ($f(1) = 1$, $f(2) = 0$, $f(4) = 1$, $f(8) = 0$). Watch why the proof of `dirichlet_product_coefficients` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean:55–70`) swaps $\chi_1$ and $\chi_2$ here: in the unswapped grouping $(1 \ast \chi_4) \ast (\chi_5 \ast \psi)$, the second convolution factor at $2^1$ is $\chi_5(2)\psi(1) + \chi_5(1)\psi(2) = -1 < 0$, so termwise nonnegativity of the two factors fails; after rewriting $f = (1 \ast \chi_5) \ast (\chi_4 \ast \psi)$, both $(1 \ast \chi_5)(2^a) = \mathbf{1}_{2 \mid a} \ge 0$ and $(\chi_4 \ast \psi)(2^b) = 0^b \mathbf{1}_{2 \mid b} = \mathbf{1}_{b=0} \ge 0$ are nonnegative at every divisor of $2^k$.
3. **Ramified prime $p = 5$, with $(\chi_4(5), \chi_5(5), \psi(5)) = (+1, 0, 0)$, and totally split prime $p = 41 \equiv 1 \pmod{20}$, with $(+1, +1, +1)$.** At $p = 5$, $E_5(s) = (1 - 5^{-s})^{-2} = \sum_{k=0}^\infty (k + 1)5^{-ks}$, giving $f(5^k) = k + 1$ ($f(5) = 2$, $f(25) = 3$). At $p = 41$, $E_{41}(s) = (1 - 41^{-s})^{-4} = \sum_{k=0}^\infty \binom{k+3}{3}41^{-ks}$ ($f(41) = 4$, $f(41^2) = 10$).

By multiplicativity, the first twelve coefficients $f(1), \dots, f(12)$ are $1, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 0$, with $f(20) = f(4)f(5) = 2$ and $f(36) = f(4)f(9) = 2$; all coefficients are nonnegative and $f(1) = 1$.

**Example 4.10.25.2 (Imprimitive characters induced by $\chi_4$: why $\psi = 1$ occurs and why `SiegelLower` uses the modulus $q$).** Keep $\chi_1 = \chi_4 \bmod 4$ and let $\chi \bmod 12$ be the character induced by $\chi_4$: $\chi(1) = \chi(5) = +1$, $\chi(7) = \chi(11) = -1$, and $\chi(n) = 0$ when $2 \mid n$ or $3 \mid n$. Then $\chi^2 = 1$ and $\chi \neq 1$, with conductor $\operatorname{cond}(\chi) = 4 < 12$. Its product with $\chi_4$ at modulus $q_1 q = 48$ satisfies $\psi(n) = \chi_4(n)^2 = +1$ whenever $\gcd(n, 48) = 1$ and $\psi(n) = 0$ otherwise, so **$\psi = 1$ is the principal character modulo $48$**. Here $L(s, \psi) = (1 - 2^{-s})(1 - 3^{-s})\zeta(s)$ has a pole at $s = 1$, giving $F(s)$ a double pole and excluding `BqKey`. Instead, lifting both $\chi_4$ and $\chi$ to modulus $48$, whose prime-factor set is $S = \{2, 3\}$ of size $\omega(48) = 2$, equates
$\displaystyle L(1, \chi_4)\bigl(1 - \chi_4(2)2^{-1}\bigr)\bigl(1 - \chi_4(3)3^{-1}\bigr) = L(1, \chi)\bigl(1 - \chi(2)2^{-1}\bigr)\bigl(1 - \chi(3)3^{-1}\bigr).$
Since $\chi_4(2) = 0$, $\chi_4(3) = -1$, and $\chi(2) = \chi(3) = 0$, this gives $\frac{4}{3}L(1, \chi_4) = L(1, \chi)$, so $L(1, \chi) = \frac{4}{3}\cdot\frac{\pi}{4} = \frac{\pi}{3}$. The archive's universal Case B bound (`lfunction_one_same_character`) replaces the exact Euler factors by $\prod_{p \in \{2,3\}}(1 - 1/p) = \frac{1}{3} = \frac{1}{\omega(48)+1}$ on the left and $\prod_{p \in \{2,3\}}(1 + 1/p) = 2 \le 3 = \omega(48) + 1$ on the right, obtaining $L(1, \chi) \ge \frac{1}{(\omega(48)+1)^2}L(1, \chi_4) = \frac{1}{9}L(1, \chi_4)$.

By contrast, if $\chi' \bmod 20$ is induced by $\chi_4$ across the split prime $5 \equiv 1 \pmod 4$ ($\chi_4(5) = +1$), the extra factor **shrinks** the $L$-value to $L(1, \chi') = (1 - \frac{1}{5})L(1, \chi_4) = \frac{4}{5}L(1, \chi_4) = \frac{\pi}{5}$ (still above the Case B bound $\frac{1}{9}L(1, \chi_4)$, since $\omega(80) = 2$). Inducing $\chi_4$ modulo $q_P = 4\prod_{p \le P,\,p \equiv 1 \pmod 4} p$ keeps $\operatorname{cond}(\chi) = 4$ constant while $L(1, \chi) = \frac{\pi}{4}\prod_{p \le P,\,p \equiv 1 \pmod 4}(1 - 1/p) \to 0$ as $P \to \infty$. Thus a lower bound valid for **imprimitive** characters cannot have the form $c_\delta \operatorname{cond}(\chi)^{-\delta}$; the bound here uses the **modulus** factor $q^{-\delta}$ (absorbing $(\omega(q_1 q) + 1)^2 \ll_\delta (q_1 q)^\delta$), and it specializes to $c_\delta \operatorname{cond}(\chi)^{-\delta}$ precisely when $\chi$ is primitive ($q = \operatorname{cond}(\chi)$).

#### 4.10.25.3 Definitions, quantifiers, and analytic inputs

Inspecting `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean`, `src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean`, and `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelOf.lean` gives four features of the formal statements [Lean]:

1. **Quantifier order and modulus versus conductor.** In `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean:29–31`, `SiegelLower` is defined (writing $\delta$ here for Lean's parameter `ε`, to distinguish it from the chapter's sieve exponent $\varepsilon < 1/52$) by
   $\displaystyle \forall \delta > 0,\ \exists c_\delta > 0,\ \forall q \ge 1,\ \forall \chi \bmod q,\quad \chi^2 = 1 \implies \chi \neq 1 \implies c_\delta\,q^{-\delta} \le \lVert L(1, \chi) \rVert.$
   The witness $c_\delta$ is chosen once after $\delta$ and works uniformly for all positive integers $q$ and all real nonprincipal characters modulo $q$, primitive or imprimitive.
2. **Primitivity and level-lifted products.** Given $\chi_1 \bmod q_1$ and $\chi_2 \bmod q_2$, `IsProdChar χ₁ χ₂ ψ` (`src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:10–12`) means $\psi$ is a Dirichlet character modulo $q_1 q_2$ satisfying $\psi(n) = \chi_1(n)\chi_2(n)$ for every $n \in \mathbb N$ (viewing each value through the natural cast $\mathbb N \to \mathbb Z/M\mathbb Z$). Neither $\chi_1$, $\chi_2$, nor $\psi$ is reduced to its conductor; instead `siegel_product_character_inequality` branches on whether $\psi = 1$ or $\psi \neq 1$.
3. **Positive and negative discriminants.** A quadratic field $\mathbb Q(\sqrt{d})$ of fundamental discriminant $d$ corresponds to an even primitive quadratic character ($\chi(-1) = +1$) when $d > 0$ and to an odd one ($\chi(-1) = -1$) when $d < 0$. The archive never passes through quadratic number fields, regulators, or Dirichlet's class-number formula: every real nonprincipal character $\chi \bmod q$ ($\chi^2 = 1$, $\chi \neq 1$) of either parity is handled by one uniform analytic argument.
4. **Selection of the fixed reference character.** In `siegel_theorem_of` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelOf.lean:9–64`), after fixing $\delta > 0$ and the cutoff $\sigma_0 := \max\bigl(\frac{7}{8}, 1 - \frac{\delta}{2(K+1)}\bigr)$, classical excluded middle splits on whether *any* positive modulus $q_1$ and real nonprincipal $\chi_1 \bmod q_1$ has a real zero $\beta \in [\sigma_0, 1)$: if so, one such triple $(q_1, \chi_1, \beta)$ is fixed with $\sigma = \beta$; if not, the explicit modulus-$4$ character $(q_1, \chi_1) = (4, \chi_4)$ is fixed with $\sigma = \sigma_0$.

For positive $q_1, q_2$ and characters $\chi_1 \bmod q_1$, $\chi_2 \bmod q_2$, $\psi \bmod q_1 q_2$, define (`src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:14–21`) [Lean]
$\displaystyle F_{\chi_1, \chi_2, \psi}(s) := \zeta(s)\,L(s, \chi_1)\,L(s, \chi_2)\,L(s, \psi), \qquad \lambda_{\chi_1, \chi_2, \psi} := L(1, \chi_1)\,L(1, \chi_2)\,L(1, \psi)$
(`Fbq` and `lamBq`). We use the following analytic inputs. [§4.10.26](#41026-regularizing-the-four-factor-product-and-bounding-its-taylor-remainder) gives the construction for `BqEntire` and the boundary estimate for `BqGrowth`. These enter here as hypotheses.

- **Simple-pole decomposition (`BqEntire`, `src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:34–37`, supplied by `dirichlet_product_entire`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqEntire.lean:31–50`) [Lean].** Whenever $\chi_1 \neq 1$, $\chi_2 \neq 1$, and $\psi \neq 1$, there exists an entire function $G : \mathbb C \to \mathbb C$ (`Differentiable ℂ G`) such that $F_{\chi_1, \chi_2, \psi}(s) = G(s) + \lambda_{\chi_1, \chi_2, \psi}/(s - 1)$ for all $s \neq 1$.
- **Circle growth bound (`BqGrowth`, `src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:39–42`, supplied by `product_lfunction_growth_bound`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqGrowth.lean:48–82`) [Lean].** There exist real constants $C_g, K_g$ such that for all positive $q_1, q_2$, all nonprincipal $\chi_1 \bmod q_1$, $\chi_2 \bmod q_2$, $\psi \bmod q_1 q_2$, and all $s \in \mathbb C$ on the circle $\lVert s - 2 \rVert = 3/2$, one has $\lVert F_{\chi_1, \chi_2, \psi}(s) \rVert \le C_g (q_1 q_2)^{K_g}$ (proved in the archive with $K_g = 3$ from `lfunction_polynomial_growth` in `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:53` and `Formalism.ZF.growthBound` in `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaGrowth.lean:78`).
- **Logarithmic upper bound at $1$ (`LFunctionOneUpperBound`, `src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:44–46`, supplied by `lfunction_one_upper_bound`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LFunctionOneUpperBound.lean:10–17`) [Lean, read].** There exists $C_L \in \mathbb R$ such that $\lVert L(1, \chi) \rVert \le C_L \log(3q)$ for every $q \ge 1$ and every $\chi \bmod q$ with $\chi \neq 1$. In `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LFunctionOneUpperBound.lean:11–17`, this is an eight-line specialization at $w = 1$ of the circle bound `lfunction_norm_le_near_one` already proved in Section 4.10.24.3, yielding $C_L = 38\exp(3/2)$.
- **Negativity of $\zeta$ on $(0, 1)$ (`ZetaNegReal`, `src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:55–56`, supplied by `zeta_negative_real_axis`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZetaNegReal.lean:29–66`) [Lean].** For every real $\sigma \in (0, 1)$, $\Im\zeta(\sigma) = 0$ and $\Re\zeta(\sigma) < 0$.
- **Real positivity of real $L$-functions (`LRealPos`, `src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:58–61`, supplied by `real_lfunction_real_on_reals`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRealPos.lean:27–44`) [Lean, read].** For every $q \ge 1$, every $\chi \bmod q$ with $\chi^2 = 1$ and $\chi \neq 1$, and every $\sigma_0 \in \mathbb R$, if $L(\sigma, \chi) \neq 0$ for all $\sigma \ge \sigma_0$, then $\Im L(\sigma, \chi) = 0$ and $\Re L(\sigma, \chi) > 0$ for all $\sigma \ge \sigma_0$. Indeed (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRealPos.lean:28–44`), Schwarz reflection $\overline{L(\bar s, \chi)} = L(s, \chi)$ (`realCharConj`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TrivReal.lean:60–79` [Lean]) gives $\Im L(t, \chi) = 0$ for all $t \in \mathbb R$; as $x \to +\infty$, $L(x, \chi) = \sum_{n=1}^\infty \chi(n)n^{-x} \to 1 > 0$ (`lfunction_tendsto_one_atTop`, `:16–25`), so if $\Re L(\sigma, \chi) \le 0$ for some $\sigma \ge \sigma_0$, continuity of $t \mapsto \Re L(t, \chi)$ (`differentiable_LFunction`) and the intermediate value theorem on $[\sigma, x]$ would produce $c \ge \sigma_0$ with $L(c, \chi) = 0$, contradicting the zero-free hypothesis.
- **Pinned Mathlib $L$-series and complex-analysis inputs (`0df444a360eaa60ab8c11dca51a86af692955474`) [Lean].** Nonnegativity $(1 \ast \chi)(n) \ge 0$ for $\chi^2 = 1$ (`DirichletCharacter.zetaMul_nonneg`, `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:106`); nonvanishing $L(s, \chi) \neq 0$ for $\Re s \ge 1, \chi \neq 1$ and in particular $L(1, \chi) \neq 0$ (`LFunction_ne_zero_of_one_le_re`, `LFunction_apply_one_ne_zero`, `:398, 406`); level-change Euler-factor identity `LFunction_changeLevel` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:150`); alternating derivative sign $(-1)^n (L\,a)^{(n)}(2) \ge 0$ for nonnegative $a$ (`LSeries.iteratedDeriv_alternating`, `Mathlib/NumberTheory/LSeries/Positivity.lean:40`); and entire Taylor series with Cauchy sphere derivative bounds (`Complex.hasSum_taylorSeries_of_entire`, `Mathlib/Analysis/Complex/TaylorSeries.lean:129`; `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, `Mathlib/Analysis/Complex/Liouville.lean:44`).

#### 4.10.25.4 Nonnegative coefficients, Taylor truncation at $2$, and level comparison

We now give full proofs of all local production lemmas leading to `BqKey` and `SameCharacterLFunctionOne`.

**Lemma 4.10.25.1 (Product characters, real witness, and principal-product criterion) [Lean, read].**
1. *(`ProdCharExists`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean:7–34`.) For any $q_1, q_2 \in \mathbb N$ and characters $\chi_1 \bmod q_1$, $\chi_2 \bmod q_2$, the product $\psi := (\operatorname{changeLevel}\,\chi_1)\cdot(\operatorname{changeLevel}\,\chi_2)$ modulo $q_1 q_2$ satisfies $\psi(n) = \chi_1(n)\chi_2(n)$ for all $n \in \mathbb N$.*
2. *(`RealCharExists`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean:36–56`.) There exists a positive integer $q_1$ and $\chi_1 \bmod q_1$ with $\chi_1^2 = 1$ and $\chi_1 \neq 1$, witnessed by $q_1 = 4$ and $\chi_4$.*
3. *(`product_real_characters_sq_eq_one` and `agree_coprime_of_product_principal`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean:10–44`.) Suppose $q_1, q \ge 1$, $\chi_1^2 = 1$, $\chi^2 = 1$, and `IsProdChar χ₁ χ ψ`. Then $\psi^2 = 1$. Moreover, if $\psi = 1$, then $\chi_1(n) = \chi(n)$ for every $n \in \mathbb N$ with $\gcd(n, q_1 q) = 1$.*

*Proof.*
1. Fix $n \in \mathbb N$. If $n$ is a unit in $\mathbb Z/q_1 q_2\mathbb Z$, then each `changeLevel` evaluates $\chi_i$ at the projected residue $n \bmod q_i$, so $\psi(n) = \chi_1(n)\chi_2(n)$. If $n$ is a nonunit modulo $q_1 q_2$, then $\gcd(n, q_1 q_2) > 1$, hence $\gcd(n, q_1) > 1$ or $\gcd(n, q_2) > 1$; thus $\psi(n) = 0$ and at least one of $\chi_1(n), \chi_2(n)$ is $0$, so both sides vanish.
2. On $\mathbb Z/4\mathbb Z$, $\chi_4$ sends $0, 1, 2, 3$ to $0, 1, 0, -1$. Being quadratic, $\chi_4^2 = 1$; since $3$ is a unit modulo $4$ with $\chi_4(3) = -1 \neq 1$, $\chi_4 \neq 1$.
3. Let $a \in (\mathbb Z/q_1 q\mathbb Z)^\times$ have canonical representative $m \in \mathbb N$ with $\gcd(m, q_1 q) = 1$; then $\gcd(m, q_1) = \gcd(m, q) = 1$, so $\psi^2(a) = \psi(m)^2 = \chi_1(m)^2\chi(m)^2 = 1 \cdot 1 = 1$, giving $\psi^2 = 1$. If $\psi = 1$ and $\gcd(n, q_1 q) = 1$, then $\chi_1(n)\chi(n) = \psi(n) = 1$ and $\chi(n)^2 = 1$, whence $\chi_1(n) = \chi_1(n)\chi(n)^2 = (\chi_1(n)\chi(n))\chi(n) = \chi(n)$. $\square$

**Lemma 4.10.25.2 (Nonnegative Dirichlet coefficients of the biquadratic product: `BqCoeff`) [Lean, read].** *Let $q_1, q_2 \ge 1$, and let $\chi_1 \bmod q_1$, $\chi_2 \bmod q_2$, and $\psi \bmod q_1 q_2$ satisfy $\chi_1^2 = 1$, $\chi_2^2 = 1$, and `IsProdChar χ₁ χ₂ ψ`. Then there exists $a : \mathbb N \to \mathbb C$ such that $a(n) \in [0, \infty)$ for all $n$ (`0 ≤ a n` in `ComplexOrder`, i.e. $\Im a(n) = 0$ and $\Re a(n) \ge 0$), $a(1) = 1$, the abscissa of absolute convergence of $\sum a(n)n^{-s}$ is at most $1$, and $F_{\chi_1, \chi_2, \psi}(s) = \sum_{n=1}^\infty a(n)n^{-s}$ for all $\Re s > 1$.* *(Lean: `dirichlet_product_coefficients`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean:34–93`, via `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean:10–70`.)*

*Proof.* View $\chi_1, \chi_2, \psi$ as arithmetic functions (vanishing at $0$) and define the Dirichlet convolution
$\displaystyle f := (1 \ast \chi_1) \ast (\chi_2 \ast \psi),$
where $1 \ast \chi_1 = \operatorname{zetaMul}(\chi_1)$. Because $1, \chi_1, \chi_2, \psi$ are multiplicative arithmetic functions, $f$ is multiplicative with $f(1) = 1$ (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean:51–54, 83`). Also, by commutativity and associativity of Dirichlet convolution, $f = (1 \ast \chi_2) \ast (\chi_1 \ast \psi)$ (`hswap`, `:55–59`).

First compute $\chi' \ast \psi$ whenever $\psi(m) = \chi(m)\chi'(m)$ (`character_convolution_eq`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean:17–37`): for every $n \ge 1$,
$\displaystyle (\chi' \ast \psi)(n) = \sum_{i \mid n} \chi'(n/i)\,\psi(i) = \sum_{i \mid n} \chi'(n/i)\,\chi(i)\,\chi'(i) = \chi'(n)\sum_{i \mid n} \chi(i) = \chi'(n)\,(1 \ast \chi)(n),$
using complete multiplicativity $\chi'(n/i)\chi'(i) = \chi'(n)$. Next, for any character $\chi$ with $\chi^2 = 1$, every value $\chi(x)$ lies in $\{0, 1, -1\}$ (`hvals`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean:40–50`), and `zetaMul_nonneg` gives $(1 \ast \chi)(d) \ge 0$ for all $d$, with $(1 \ast \chi)(p^j) = \sum_{i=0}^j \chi(p)^i$ at a prime power $p^j$.

We claim `prime_power_coefficient_nonneg` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean:41–70`): if $\chi^2 = 1$, $\psi(m) = \chi(m)\chi'(m)$, $p$ is prime, and either $\chi'(p) = 0$, or $\chi'(p) = 1$, or $(\chi'(p) = -1 \land \chi(p) = -1)$, then $((1 \ast \chi) \ast (\chi' \ast \psi))(p^k) \ge 0$ for all $k \ge 0$. Since the Dirichlet convolution of two functions that are nonnegative on all divisors of $n$ is nonnegative at $n$ (`convolution_nonneg_of_divisors`, `:10–15`), and $(1 \ast \chi)(d) \ge 0$ for every $d \mid p^k$, it suffices to check $(\chi' \ast \psi)(p^j) = \chi'(p)^j (1 \ast \chi)(p^j) \ge 0$ for every $0 \le j \le k$:

- If $\chi'(p) = 0$ or $\chi'(p) = 1$, then $\chi'(p)^j \in \{0, 1\} \ge 0$ while $(1 \ast \chi)(p^j) \ge 0$.
- If $\chi'(p) = -1$ and $\chi(p) = -1$, then $(1 \ast \chi)(p^j) = \sum_{i=0}^j (-1)^i$, which equals $0$ when $j$ is odd and $1$ when $j$ is even; when $j$ is even, $(-1)^j = +1$, so $(\chi' \ast \psi)(p^j) = \mathbf{1}_{2 \mid j} \ge 0$.

Now let $p$ be any prime (`hpp`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean:63–72`). Since $\chi_2(p) \in \{0, 1, -1\}$ and $\chi_1(p) \in \{0, 1, -1\}$: if $\chi_2(p) \in \{0, 1\}$ or $(\chi_2(p) = -1 \land \chi_1(p) = -1)$, apply the claim to $(\chi, \chi') = (\chi_1, \chi_2)$; in the remaining two cases $\chi_2(p) = -1$ and $\chi_1(p) \in \{0, 1\}$, swap the roles via $f = (1 \ast \chi_2) \ast (\chi_1 \ast \psi)$ and apply the claim to $(\chi, \chi') = (\chi_2, \chi_1)$. Thus $f(p^k) \ge 0$ for every prime power, so multiplicativity $f(n) = \prod_{p^k \parallel n} f(p^k)$ (and $f(0) = 0$) gives $f(n) \ge 0$ for all $n \in \mathbb N$. Finally, for $\Re s > 1$, the four Dirichlet series of $1, \chi_1, \chi_2, \psi$ converge absolutely, so Cauchy multiplication of absolutely convergent $L$-series (`ArithmeticFunction.LSeries_mul'`) shows that $\sum_{n=1}^\infty f(n)n^{-s}$ converges absolutely (forcing abscissa $\le 1$) and equals $\zeta(s)L(s, \chi_1)L(s, \chi_2)L(s, \psi) = F_{\chi_1, \chi_2, \psi}(s)$. $\square$

**Proposition 4.10.25.3 (Taylor truncation at $s = 2$ and `BqKey`) [Lean, read].** *Assume `BqCoeff`, `BqEntire`, `BqGrowth`, and `LFunctionOneUpperBound`. Then `BqKey` holds (`src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:48–53`): there exist real constants $C$ and $K \ge 0$ such that for all $q_1, q_2 \ge 1$, all characters $\chi_1 \bmod q_1$, $\chi_2 \bmod q_2$, $\psi \bmod q_1 q_2$ satisfying $\chi_1^2 = 1$, $\chi_2^2 = 1$, $\chi_1 \neq 1$, $\chi_2 \neq 1$, $\psi \neq 1$, and `IsProdChar χ₁ χ₂ ψ`, and every real $\sigma \in [7/8, 1)$,*
$\displaystyle \frac{1}{2} - C\,\lVert \lambda_{\chi_1, \chi_2, \psi} \rVert\,\frac{(q_1 q_2)^{K(1 - \sigma)}}{1 - \sigma} \le \Re F_{\chi_1, \chi_2, \psi}(\sigma).$
*Specifically (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean:64–73`), if $(C_g, K_g)$ and $C_L$ are the witnesses of `BqGrowth` and `LFunctionOneUpperBound`, one may set $c_0 := \lvert C_g \rvert + 54\lvert C_L \rvert^3 + 1$, $K' := \max(K_g, 2)$, $\ell := \log(4/3) > 0$, $C := e^2\exp\bigl(\frac{\log(8c_0)}{8\ell}\bigr)$, and $K := K'/\ell \ge 0$.* *(Lean: `lseries_taylor_lower_bound`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean:30–151`, and `product_lfunction_key_inequality`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean:60–152`.)*

*Proof.* Fix characters as in the statement and write $F = F_{\chi_1, \chi_2, \psi}$, $\lambda = \lambda_{\chi_1, \chi_2, \psi}$, and $N := q_1 q_2 \ge 1$. Let $a : \mathbb N \to \mathbb C$ come from `BqCoeff` and let $G$ come from `BqEntire`, so $G$ is entire and $F(s) = G(s) + \lambda(s - 1)^{-1}$ for $s \neq 1$, while $F(s) = (L\,a)(s)$ on $\Re s > 1$.

**Step 1: Bounding $G$ on the circle $\lVert s - 2 \rVert = 3/2$.** Using $\log(3q) \le 3q$ (`norm_le_of_log_bound`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean:10–18`), `LFunctionOneUpperBound` gives $\lVert L(1, \chi_i) \rVert \le 3\lvert C_L \rvert q_i$ and $\lVert L(1, \psi) \rVert \le 3\lvert C_L \rvert N$, so $\lVert \lambda \rVert \le 27\lvert C_L \rvert^3 N^2$ (`:82–89`). On the sphere $\lVert s - 2 \rVert = 3/2$, the triangle inequality gives $\lVert s - 1 \rVert \ge \lVert s - 2 \rVert - 1 = 1/2$, so $\lVert \lambda/(s - 1) \rVert \le 2\lVert \lambda \rVert \le 54\lvert C_L \rvert^3 N^2$. Combining with `BqGrowth` ($\lVert F(s) \rVert \le C_g N^{K_g}$) and $N \ge 1$ gives (`:95–115`)
$\displaystyle \lVert G(s) \rVert \le \lVert F(s) \rVert + \lVert \lambda/(s - 1) \rVert \le B := c_0 N^{K'} \qquad (\lVert s - 2 \rVert = 3/2),$
with $B \ge c_0 \ge 1$.

**Step 2: Exact pole cancellation in the Taylor series of $G$ at $2$.** Let $\sigma \in [7/8, 1)$ and set $x := 2 - \sigma \in (1, 9/8]$. Since $\{s : \Re s > 1\}$ is an open neighborhood of $2$ on which $(L\,a)(s) = G(s) + \lambda(s - 1)^{-1}$, differentiating $n$ times at $s = 2$ and using $\frac{d^n}{ds^n}(s - 1)^{-1}\big|_{s=2} = (-1)^n n!$ (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivInvSubOneAtTwo.lean:10–26`) gives
$\displaystyle (L\,a)^{(n)}(2) = G^{(n)}(2) + \lambda\,(-1)^n n! \qquad (n \ge 0).$
Put $\beta_n := \frac{(-1)^n}{n!}(L\,a)^{(n)}(2)$. Since $a(m) \ge 0$ and the abscissa of absolute convergence is $\le 1 < 2$, `LSeries.iteratedDeriv_alternating` gives $\beta_n \ge 0$ for all $n \ge 0$, while $\beta_0 = (L\,a)(2) \ge a(1) = 1$ (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean:10–28`). Because $G$ is entire, $G(\sigma) = \sum_{n=0}^\infty t_n$ where, using $\sigma - 2 = -x$,
$\displaystyle t_n := \frac{(\sigma - 2)^n}{n!}G^{(n)}(2) = \frac{(-x)^n}{n!}\bigl((L\,a)^{(n)}(2) - \lambda(-1)^n n!\bigr) = x^n \beta_n - \lambda x^n$
(`:52–71`). Choose any truncation order $M \ge 1$. Summing $n = 0, \dots, M - 1$ via $\sum_{i=0}^{M-1} x^i = \frac{x^M - 1}{x - 1}$ and adding back $\frac{\lambda}{\sigma - 1} = -\frac{\lambda}{x - 1}$ cancels the $+\frac{\lambda}{x - 1}$ term cleanly (`:73–78, 121–133`):
$\displaystyle F(\sigma) = G(\sigma) + \frac{\lambda}{\sigma - 1} = \sum_{i=0}^{M-1} x^i \beta_i - \lambda\frac{x^M}{x - 1} + \sum_{i=0}^\infty t_{i+M}.$
Because $M \ge 1$, $x > 1 > 0$, and $\beta_i \ge 0$, we have $\sum_{i=0}^{M-1} x^i \beta_i \ge \beta_0 \ge 1$ (`:79–88`). For $j = i + M \ge M$, Cauchy's derivative estimate on $\lVert s - 2 \rVert = 3/2$ gives $\lVert G^{(j)}(2) \rVert \le j!\,B/(3/2)^j$; since $x \le 9/8$, we have $\frac{x}{3/2} \le \frac{9/8}{3/2} = \frac{3}{4}$, so $\lVert t_j \rVert \le B(3/4)^j$ and summing the geometric tail yields $\lVert \sum_{i=0}^\infty t_{i+M} \rVert \le B(3/4)^M(1 - 3/4)^{-1} = 4B(3/4)^M$ (`:90–116`). Taking real parts with $x - 1 = 1 - \sigma > 0$ gives `lseries_taylor_lower_bound`:
$\displaystyle 1 - \lVert \lambda \rVert\frac{(2 - \sigma)^M}{1 - \sigma} - 4B\Bigl(\frac{3}{4}\Bigr)^M \le \Re F(\sigma).$

**Step 3: Choosing the truncation order $M$.** Set $T := 8B = 8c_0 N^{K'} \ge 8$ and choose $M := \lceil \frac{\log T}{\ell} \rceil + 1 \ge 1$, where $\ell = \log(4/3)$ (`exists_taylor_truncation_order`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean:20–45`). Then $(4/3)^M \ge T$, so $4B(3/4)^M = \frac{1}{2}T(3/4)^M \le \frac{1}{2}$, leaving $1 - 4B(3/4)^M \ge \frac{1}{2}$. Meanwhile $M \le 2 + \frac{\log(8c_0) + K'\log N}{\ell}$. Since $2 - \sigma = 1 + (1 - \sigma) \le e^{1 - \sigma}$ and $1 - \sigma \le 1/8$ on $[7/8, 1)$, we have (`two_sub_pow_le_exp` and `:122–144`)
$\displaystyle (2 - \sigma)^M \le \exp\bigl(M(1 - \sigma)\bigr) \le e^2\exp\Bigl(\frac{\log(8c_0)(1 - \sigma) + K'(\log N)(1 - \sigma)}{\ell}\Bigr) \le e^2\exp\Bigl(\frac{\log(8c_0)}{8\ell}\Bigr)\,N^{(K'/\ell)(1 - \sigma)} = C\,N^{K(1 - \sigma)},$
which yields the stated lower bound on $\Re F(\sigma)$. $\square$

**Lemma 4.10.25.4 (Euler-factor comparison when two characters agree on coprime integers: `SameCharacterLFunctionOne`) [Lean, read].** *Let $q_1, q \ge 1$, and let $\chi_1 \bmod q_1$ and $\chi \bmod q$ satisfy $\chi_1 \neq 1$, $\chi \neq 1$, and $\chi_1(n) = \chi(n)$ whenever $\gcd(n, q_1 q) = 1$. Writing $\omega(q_1 q)$ for the number of distinct prime divisors of $q_1 q$,*
$\displaystyle \lVert L(1, \chi_1) \rVert \le \bigl(\omega(q_1 q) + 1\bigr)^2\,\lVert L(1, \chi) \rVert.$
*(Lean: `lfunction_one_same_character`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean:98–144`.)*

*Proof.* First we show $\prod_{p \in S}(1 - 1/p) \ge \frac{1}{\lvert S \rvert + 1}$ for every finite set $S \subset \mathbb N$ with $\min S \ge 2$ (`prod_one_sub_inv_ge_inv_card_succ`, `:9–42`), by induction on the maximum element of $S$. For $S = \emptyset$ both sides equal $1$. If $S = s \cup \{a\}$ with $p < a$ for all $p \in s$, then $s \subseteq [2, a) \cap \mathbb N$, so $\lvert s \rvert \le a - 2$, i.e. $a \ge \lvert s \rvert + 2$. By the induction hypothesis on $s$,
$\displaystyle \Bigl(1 - \frac{1}{a}\Bigr)\prod_{p \in s}\Bigl(1 - \frac{1}{p}\Bigr) \ge \Bigl(1 - \frac{1}{a}\Bigr)\frac{1}{\lvert s \rvert + 1} = \frac{1}{\lvert s \rvert + 2} + \frac{a - (\lvert s \rvert + 2)}{a(\lvert s \rvert + 1)(\lvert s \rvert + 2)} \ge \frac{1}{\lvert S \rvert + 1}.$
Also, since $(1 + 1/p)(1 - 1/p) = 1 - 1/p^2 \le 1$, we have $\bigl(\prod_{p \in S}(1 + 1/p)\bigr)\bigl(\prod_{p \in S}(1 - 1/p)\bigr) \le 1$ (`prod_one_add_mul_one_sub_le_one`, `:87–96`), whence $\prod_{p \in S}(1 + 1/p) \le \lvert S \rvert + 1$.

Now let $S := \operatorname{primeFactors}(q_1 q)$, of cardinality $\omega := \omega(q_1 q)$. Because $\chi_1$ and $\chi$ agree on integers coprime to $q_1 q$, their lifts to modulus $q_1 q$ via `changeLevel` coincide on $(\mathbb Z/q_1 q\mathbb Z)^\times$ and hence are equal as Dirichlet characters modulo $q_1 q$ (`changeLevel_eq_of_agree_coprime`, `:44–53`). Evaluating `DirichletCharacter.LFunction_changeLevel` at $s = 1$ (valid since $\chi_1 \neq 1$ and $\chi \neq 1$) and taking norms gives (`:103–111`)
$\displaystyle \lVert L(1, \chi_1) \rVert \prod_{p \in S}\bigl\lVert 1 - \chi_1(p)p^{-1} \bigr\rVert = \lVert L(1, \chi) \rVert \prod_{p \in S}\bigl\lVert 1 - \chi(p)p^{-1} \bigr\rVert.$
Since $\lVert \chi_1(p)p^{-1} \rVert \le 1/p$ and $\lVert \chi(p)p^{-1} \rVert \le 1/p$, the left product is at least $\prod_{p \in S}(1 - 1/p) \ge \frac{1}{\omega + 1}$ and the right product is at most $\prod_{p \in S}(1 + 1/p) \le \omega + 1$ (`:112–133`). Multiplying through by $\omega + 1$ yields $\lVert L(1, \chi_1) \rVert \le (\omega + 1)^2 \lVert L(1, \chi) \rVert$. $\square$

#### 4.10.25.5 Conditional proof of the Siegel lower bound

We now assemble the unified product-character deduction (`siegel_product_character_inequality`) and the top-level dichotomy (`siegel_theorem_of`).

**Theorem 4.10.25.5 (Conditional Siegel lower bound: `SiegelOf` / `SiegelLower`) [Lean, read].** *Assume `BqKey`, `LFunctionOneUpperBound`, `ZetaNegReal`, and `LRealPos` (along with the proved packages `ProdCharExists`, `RealCharExists`, and `SameCharacterLFunctionOne` of Lemmas 4.10.25.1 and 4.10.25.4, and `LFunction_ne_zero_of_one_le_re` / `LFunction_apply_one_ne_zero`). Then `SiegelLower` holds: for every $\delta > 0$ there exists $c_\delta > 0$ such that for every integer $q \ge 1$ and every Dirichlet character $\chi \bmod q$ with $\chi^2 = 1$ and $\chi \neq 1$,*
$\displaystyle L(1, \chi) = \lVert L(1, \chi) \rVert \ge c_\delta\,q^{-\delta}.$
*In particular, for every primitive real nonprincipal Dirichlet character $\chi$ (so $q = \operatorname{cond}(\chi)$),*
$\displaystyle L(1, \chi) \ge c_\delta\,\operatorname{cond}(\chi)^{-\delta}.$
*(Lean: `siegel_product_character_inequality`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean:106–183`; `siegel_theorem_of`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelOf.lean:9–64`; assembled as `siegelLower` at `src/Formalism/LandauZeroFreeBounds/FinalSiegel.lean:17–19`.)*

*Proof.* Fix $\delta > 0$, let $(C, K)$ with $K \ge 0$ be the constants of `BqKey`, and let $C_L$ be the constant of `LFunctionOneUpperBound`. Define (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelOf.lean:13`)
$\displaystyle \sigma_0 := \max\Bigl(\frac{7}{8},\, 1 - \frac{\delta}{2(K + 1)}\Bigr).$
Since $K + 1 > 0$ and $\delta > 0$, we have $\frac{7}{8} \le \sigma_0 < 1$. Moreover, for every $\sigma \in [\sigma_0, 1)$, $1 - \sigma \le \frac{\delta}{2(K + 1)}$ gives $K(1 - \sigma) \le (K + 1)(1 - \sigma) \le \delta/2$ (`hKa`, `:20–29`).

**Part 1: Choosing the fixed reference datum $(q_1, \chi_1, \sigma)$ (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelOf.lean:30–64`).** Split by classical excluded middle on the proposition
$\displaystyle \mathrm{hex} :\iff \exists q_1 \ge 1,\ \exists \chi_1 \bmod q_1,\ \exists \beta \in \mathbb R,\quad \chi_1^2 = 1 \land \chi_1 \neq 1 \land \sigma_0 \le \beta < 1 \land L(\beta, \chi_1) = 0.$

- **Exceptional branch (`hex` holds, `:32–37`).** Choose one witness $(q_1, \chi_1, \beta)$ and set $\sigma := \beta \in [\sigma_0, 1) \subseteq [7/8, 1)$. For any $q \ge 1$, $\chi \bmod q$, and $\psi \bmod q_1 q$, we have $F_{\chi_1, \chi, \psi}(\beta) = \zeta(\beta)\cdot 0\cdot L(\beta, \chi)\,L(\beta, \psi) = 0$, so $\Re F_{\chi_1, \chi, \psi}(\sigma) \le 0$.
- **Zero-free branch (`¬ hex` holds, `:38–64`).** Choose the fixed witness $(q_1, \chi_1) = (4, \chi_4)$ from Lemma 4.10.25.1(2) and set $\sigma := \sigma_0 \in [7/8, 1)$. For *every* $m \ge 1$ and *every* real nonprincipal $\varphi \bmod m$, $L(t, \varphi) \neq 0$ holds for $t \in [\sigma_0, 1)$ by `¬ hex` and for $t \ge 1$ by `LFunction_ne_zero_of_one_le_re`; hence `LRealPos` at $\sigma_0$ gives $\Im L(\sigma_0, \varphi) = 0$ and $\Re L(\sigma_0, \varphi) > 0$ (`:41–50`). Given any real nonprincipal $\chi \bmod q$ and product $\psi \bmod q_1 q$ with $\psi \neq 1$, Lemma 4.10.25.1(3) gives $\psi^2 = 1$, so $L(\sigma_0, \chi_1)$, $L(\sigma_0, \chi)$, and $L(\sigma_0, \psi)$ are all positive real numbers, whereas `ZetaNegReal` gives $\zeta(\sigma_0) \in (-\infty, 0)$. Their product is strictly negative, so again $\Re F_{\chi_1, \chi, \psi}(\sigma) \le 0$ (`:52–64`).

**Part 2: Unified deduction for all $(q, \chi)$ from $(q_1, \chi_1, \sigma)$ (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean:106–183`).** With $(q_1, \chi_1, \sigma)$ fixed above (satisfying $7/8 \le \sigma < 1$, $K(1 - \sigma) \le \delta/2$, and $\Re F_{\chi_1, \chi, \psi}(\sigma) \le 0$ whenever $\psi \neq 1$), note that $L_1 := \lVert L(1, \chi_1) \rVert > 0$ by `LFunction_apply_one_ne_zero` (`:121–122`). Define (`:133–136`)
$\displaystyle c_\delta := \min\left(\frac{1 - \sigma}{2\max(C, 1)\,L_1\,(\lvert C_L \rvert + 1)\,(2/\delta)\,(3q_1)^\delta},\ \frac{L_1}{\bigl(\frac{2}{\delta\log 2} + 1\bigr)^2\,(3q_1)^\delta}\right) > 0.$
Now let $q \ge 1$ and let $\chi \bmod q$ satisfy $\chi^2 = 1$ and $\chi \neq 1$. Construct $\psi \bmod q_1 q$ satisfying `IsProdChar χ₁ χ ψ` by Lemma 4.10.25.1(1), and split on whether $\psi = 1$ (`:148`):

- **Case B: $\psi = 1$ (`:149–153`).** By Lemma 4.10.25.1(3), $\chi_1(n) = \chi(n)$ whenever $\gcd(n, q_1 q) = 1$, so Lemma 4.10.25.4 gives $L_1 \le (\omega(q_1 q) + 1)^2 \lVert L(1, \chi) \rVert$. For any integer $n \ge 1$, every prime divisor of $n$ is at least $2$, so $2^{\omega(n)} \le \prod_{p \mid n} p \le n$ (`two_pow_card_primeFactors_le_self`, `:46–50`). Taking logarithms and applying $\log n \le \frac{n^{\delta/2}}{\delta/2}$ together with $1 \le n^{\delta/2}$ gives $\omega(n) + 1 \le \bigl(\frac{2}{\delta\log 2} + 1\bigr)n^{\delta/2}$, and squaring gives (`card_primeFactors_add_one_sq_le_rpow`, `:51–72`)
  $\displaystyle \bigl(\omega(q_1 q) + 1\bigr)^2 \le \Bigl(\frac{2}{\delta\log 2} + 1\Bigr)^2 (q_1 q)^\delta \le \Bigl(\frac{2}{\delta\log 2} + 1\Bigr)^2 (3q_1)^\delta\,q^\delta.$
  Dividing $L_1 \le (\omega(q_1 q) + 1)^2 \lVert L(1, \chi) \rVert$ by the positive coefficient of $q^\delta$ (`div_le_mul_of_chain_caseB`, `:97–104`) gives $\lVert L(1, \chi) \rVert \ge c_\delta q^{-\delta}$.

- **Case A: $\psi \neq 1$ (`:154–183`).** Combining `BqKey` at $\sigma$ with $\Re F_{\chi_1, \chi, \psi}(\sigma) \le 0$ and $\lVert \lambda_{\chi_1, \chi, \psi} \rVert = L_1\,\lVert L(1, \chi) \rVert\,\lVert L(1, \psi) \rVert$ gives (`:156–165`)
  $\displaystyle \frac{1 - \sigma}{2} \le C\,\bigl(L_1\,\lVert L(1, \chi) \rVert\,\lVert L(1, \psi) \rVert\bigr)\,(q_1 q)^{K(1 - \sigma)} \le \max(C, 1)\,L_1\,\lVert L(1, \chi) \rVert\,\lVert L(1, \psi) \rVert\,(q_1 q)^{K(1 - \sigma)}.$
  Because $\psi \neq 1$, `LFunctionOneUpperBound` and $\log u \le \frac{u^{\delta/2}}{\delta/2}$ at $u = 3q_1 q \ge 3$ give (`:166–175`)
  $\displaystyle \lVert L(1, \psi) \rVert \le (\lvert C_L \rvert + 1)\log(3q_1 q) \le (\lvert C_L \rvert + 1)\,\frac{2}{\delta}\,(3q_1 q)^{\delta/2}.$
  Meanwhile $K(1 - \sigma) \le \delta/2$ and $q_1 q \ge 1$ imply $(q_1 q)^{K(1 - \sigma)} \le (q_1 q)^{\delta/2} \le (3q_1 q)^{\delta/2}$ (`:176–178`). Multiplying the two factors of $(3q_1 q)^{\delta/2}$ yields $(3q_1 q)^\delta = (3q_1)^\delta q^\delta$ (`:179–181`), so
  $\displaystyle \frac{1 - \sigma}{2} \le \max(C, 1)\,L_1\,(\lvert C_L \rvert + 1)\,\frac{2}{\delta}\,(3q_1)^\delta\,q^\delta\,\lVert L(1, \chi) \rVert.$
  Dividing (`div_le_mul_of_main_bound_caseA`, `:74–95`) gives $\lVert L(1, \chi) \rVert \ge c_\delta q^{-\delta}$.

Finally, for any real nonprincipal $\chi \bmod q$, `LFunction_ne_zero_of_one_le_re` gives $L(t, \chi) \neq 0$ for all $t \ge 1$, so `LRealPos` applied at $\sigma_0 = 1$ gives $\Im L(1, \chi) = 0$ and $\Re L(1, \chi) > 0$; thus $L(1, \chi) = \lVert L(1, \chi) \rVert \ge c_\delta q^{-\delta}$. When $\chi$ is primitive, its modulus $q$ equals $\operatorname{cond}(\chi)$, giving $L(1, \chi) \ge c_\delta\operatorname{cond}(\chi)^{-\delta}$. $\square$

#### 4.10.25.6 Notes and source map

[Source register](../sources/SOURCES.md#chapter-4-real-zeros-and-the-siegel-product)

**Editorial correction on effectiveness.** The draft inferred that the existence of an exceptional reference character is undecidable and that no positive numerical constant can be computed. The proof uses excluded middle across all moduli and gives no uniform effective way to select the branch or bound the reference data for arbitrary $\delta>0$. Given a certified exceptional character and a certified interval for its zero with upper endpoint below $1$, the displayed formula can give a numerical lower bound using bounds for $L_1$ and $1-\sigma$. The argument establishes existence of $c_\delta$ and leaves the uniform effective construction unproved. The same limitation passes to the separation and the counting threshold. [Montgomery and Vaughan, §11.2, p. 373](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/15.0_pp_358_396_Primes_in_arithmetic_progressions_II.pdf)

**Historical sources [Paper].** Siegel establishes his classical result through quadratic and biquadratic fields and fixes a reference discriminant in the proof. Montgomery and Vaughan present the related pole-subtracted Taylor argument and fixed-reference dichotomy (Lemma 11.13 and Theorem 11.14). They credit Estermann for the method. The constants and the direct comparison of imprimitive characters here follow the cited Lean declarations. The Estermann citation identifies the historical paper at the bibliographic level. [Siegel1935, pp. 83–86](https://doi.org/10.4064/AA-1-1-83-86) · [MontgomeryVaughan2007, Ch. 11](https://doi.org/10.1017/CBO9780511618314.013) · [Estermann1948](https://doi.org/10.1112/jlms/s1-23.4.275)

**Consumers and reading scope.** `siegelLower` (`src/Formalism/LandauZeroFreeBounds/FinalSiegel.lean:17`) has two direct calls in `SiegelWalfiszAPOfSiegelLower.lean`: `excBound` (`src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:32`, feeding `count_a` at $\delta = 1/3$ via $\delta_{\mathrm{Exc}} = 1$ as proved in [§4.9](#49-counting-enough-candidates-before-the-sieve) and [§4.10.24](#41024-separating-a-real-zero-from-1)) and `siegelWalfisz` (`:34`). `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean:1` imports `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelBoundSameCharacter.lean` (`siegel_bound_key_rearrange`, `siegel_bound_same_character`), which proves a close variant of the Case A/B algebra, but `siegel_product_character_inequality` uses its own private helpers (`:46–104`) instead.

All archive paths below are relative to the `lean/` root of the [pinned release](../sources/SOURCES.md#1-the-lean-archive-primary-source), SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, with Mathlib pinned at `0df444a360eaa60ab8c11dca51a86af692955474`.

| Role and read status | Declaration and archive / Mathlib location |
|---|---|
| Target statement and consumers [Lean] | `SiegelLower`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean:29–31`; `excBound_of_siegelLower`, `siegelWalfisz_of_siegelLower`, `excBound`, `siegelWalfisz`, `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:26–34` |
| Product-$L$ interfaces [Lean] | `IsProdChar`, `Fbq`, `lamBq`, `ProdCharExists`, `BqCoeff`, `BqEntire`, `BqGrowth`, `LFunctionOneUpperBound`, `BqKey`, `ZetaNegReal`, `LRealPos`, `SameCharacterLFunctionOne`, `RealCharExists`, `BqKeyOf`, `SiegelOf`, `src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:10–75` |
| Product character and mod-$4$ witness [Lean, read] | `isProdChar_changeLevel_mul`, `exists_product_character`, `characterModFour`, `exists_real_nontrivial_character`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean:7–56` |
| Nonnegative biquadratic coefficients [Lean, read] | `convolution_nonneg_of_divisors`, `character_convolution_eq`, `prime_power_coefficient_nonneg`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean:10–70`; `dirichlet_product_coefficients`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean:10–93` |
| Taylor expansion at $s = 2$ and `BqKeyOf` [Lean, read] | `iteratedDeriv_inv_sub_one_at_two`, `iteratedDeriv_lseries_at_two`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivInvSubOneAtTwo.lean:10–26`; `one_le_lseries_at_two`, `iteratedDeriv_lseries_alternating_nonneg`, `lseries_taylor_lower_bound`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean:10–151`; `norm_le_of_log_bound`, `exists_taylor_truncation_order`, `two_sub_pow_le_exp`, `product_lfunction_key_inequality`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean:10–152` |
| Same-character Euler-factor bound [Lean, read] | `prod_one_sub_inv_ge_inv_card_succ`, `changeLevel_eq_of_agree_coprime`, `lfunction_one_same_character`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean:9–144` (unused variant in `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelBoundSameCharacter.lean:9–106`) |
| Unified two-branch inequality and dichotomy [Lean, read] | `real_character_apply_sq_eq_one`, `product_real_characters_sq_eq_one`, `agree_coprime_of_product_principal`, `siegel_product_character_inequality`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean:10–183`; `siegel_theorem_of`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelOf.lean:9–64` |
| Upper bound at $1$ and real positivity [Lean, read]. Final wiring [Lean] | `lfunction_one_upper_bound`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LFunctionOneUpperBound.lean:10–17` (from §4.10.24); `real_lfunction_real_on_reals`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRealPos.lean:10–44`; `bqKey`, `siegelLower`, `src/Formalism/LandauZeroFreeBounds/FinalSiegel.lean:14–19` |
| Named deeper analytic and library inputs [Lean] | `dirichlet_product_entire`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqEntire.lean:31–50`; `product_lfunction_growth_bound`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqGrowth.lean:48–82` (with `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:53–71` and `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaGrowth.lean:78–95`); `zeta_negative_real_axis`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZetaNegReal.lean:29–66`; `realCharConj`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TrivReal.lean:60–79`; pinned Mathlib `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:106,398,406`, `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:75,98,150`, `Mathlib/NumberTheory/LSeries/Positivity.lean:40`, `Mathlib/Analysis/Complex/TaylorSeries.lean:129` |

Local `R3` (`[Lean, read]`) applies strictly to the listed direct production proofs from `BqCoeff` through `BqKeyOf`, the same-character comparison, the two-branch inequality, the conditional Siegel theorem, real positivity and the upper bound at $1$. The complete `siegelLower` supplier, negative-real-$\zeta$ and the deeper Mathlib dependencies retain R2 [Lean].

### 4.10.26 Regularizing the four-factor product and bounding its Taylor remainder

#### 4.10.26.1 Motivation

The argument of [§4.10.25](#41025-the-siegel-lower-bound-from-biquadratic-product-series) uses a circle of radius $3/2$ about $2$. This circle encloses $1$. The Dirichlet series identifies the product to the right of $1$, while Cauchy's estimate requires a function holomorphic across $1$. In this section we construct that function and derive the modulus-uniform bound passed to the Taylor argument. The analytic construction works for arbitrary nonprincipal complex characters at the three indicated levels. Reality and the product-character identity enter the coefficient and branch arguments of [§4.10.25](#41025-the-siegel-lower-bound-from-biquadratic-product-series).

#### 4.10.26.2 Two hand calculations [Expository]

**An odd character times an even character.** Take the odd character $\chi_4$, with values $1,-1$ at $1,3\bmod 4$, and the even quadratic character $\chi_5$, with values $1,-1,-1,1$ at $1,2,3,4\bmod 5$. Their product $\psi$ at level $20$ takes value $+1$ at $1,3,7,9$, value $-1$ at $11,13,17,19$, and zero on nonunits. It is odd and nonprincipal. By the coprime-modulus decomposition of the unit group, each nontrivial local component forces its prime-power level, so the conductor of $\psi$ is $20$.

Integrating the geometric blocks term by term gives
$L(1,\chi_4)=\int_0^1 (1+t^2)^{-1}\,dt=\pi/4$ and
$L(1,\chi_5)=\int_0^1 (1-t)(1-t^2)/(1-t^5)\,dt$.
For $\psi$ the block polynomial is $(1-t^{10})(1+t^2+t^6+t^8)$, so
$L(1,\psi)=\int_0^1 (1+t^2+t^6+t^8)/(1+t^{10})\,dt$.
Indeed, a block ending at level $q$ contributes its polynomial times $t^{jq}$, and integrating a monomial gives the corresponding reciprocal integer. The integrated partial blocks converge by dominated convergence because the quotients after cancellation are bounded on $[0,1]$. Their limits equal the continued values by the summation formula below. All three values are positive. The four-factor product therefore has a simple pole with residue $(\pi/4)L(1,\chi_5)L(1,\psi)$, and subtracting this residue divided by $s-1$ gives the entire function used at $N=20$.

**A principal product from the same primitive character.** Induce $\chi_4$ to level $12$ and call the resulting character $\chi_{12}$. On units modulo $48$ the characters agree and their product is $1$. At every nonunit modulo $48$ at least one factor vanishes. Thus $\psi$ is principal at level $48$, with conductor $1$, and both input characters have conductor $4$. Since $\chi_4(3)=-1$,
$L(s,\chi_{12})=(1+3^{-s})L(s,\chi_4)$.
The principal factor is $\zeta(s)(1-2^{-s})(1-3^{-s})$ off $1$. The coefficient of $(s-1)^{-2}$ in the four-factor product is accordingly
$(\pi/4)^2(1+1/3)(1-1/2)(1-1/3)=\pi^2/36$.
This double pole rules out the simple-pole subtraction in this branch. This branch uses the same-character comparison of Lemma 4.10.25.4, where the exact ratio is $L(1,\chi_{12})/L(1,\chi_4)=4/3$. The Euler-factor identities follow on $\Re s>1$ by removing the multiples of the added primes, then extend by uniqueness to the common holomorphic domain. For the two nonprincipal factors this includes $1$.

#### 4.10.26.3 Definitions and analytic inputs

Let $q_1,q_2$ be positive integers, put $N=q_1q_2$, and take $\chi_i\bmod q_i$ and $\psi\bmod N$. The analytic lemmas below assume all three characters are nonprincipal. Write
$P(s)=L(s,\chi_1)L(s,\chi_2)L(s,\psi)$, $F(s)=\zeta(s)P(s)$ and $\lambda=P(1)$.
Use $x^{-s}=\exp(-s\log x)$ for positive real $x$. The principal character at level $q$ is $1$ on units and $0$ elsewhere. The conductor is the least inducing modulus. Each $L$-function here is evaluated at its displayed level, with the Euler factors at primes dividing that level omitted. In particular, the growth and residue bounds below use $q_1,q_2,N$ even if the corresponding conductors are smaller.

We use the classical continuation of $\zeta$ and $L(s,\chi)$, their agreement with their series on $\Re s>1$, and the Laurent expansion of $\zeta$ with residue $1$ and constant term $\gamma$. In the archive, entire continuation for nonprincipal characters enters through Mathlib's `DirichletCharacter.differentiable_LFunction`. The zeta input enters through differentiability off $1$ and the limit of $\zeta(s)-1/(s-1)$ at $1$. For the classical statements see [DLMF §25.2(i)–(ii)](https://dlmf.nist.gov/25.2) and [DLMF §25.15(i)](https://dlmf.nist.gov/25.15).

#### 4.10.26.4 Lemma (entire continuation of the regularized product) [Lean, read]

There is a unique entire $G$ such that $F(s)=G(s)+\lambda/(s-1)$ for $s\ne 1$. At the removed point, $G(1)=\gamma P(1)+P'(1)$.

*Proof.* Define $Z(s)=\zeta(s)-1/(s-1)$ for $s\ne 1$ and $Z(1)=\gamma$. The punctured-plane function is holomorphic, and its finite limit at $1$ supplies the removable extension. Each nonprincipal $L$-factor is entire, hence so is $P$. Define $D_P(s)=(P(s)-P(1))/(s-1)$ off $1$ and $D_P(1)=P'(1)$. This divided difference is holomorphic off $1$ and its removable value follows from differentiability, or by cancelling the first power in the Taylor expansion of $P(s)-P(1)$. Set $G=ZP+D_P$, exactly the archive's construction with `zetaSubPole` and `dslope`. Substitution off $1$ yields the claimed decomposition and evaluation at $1$ gives the stated value. Any entire function agreeing with $F-\lambda/(s-1)$ even on the open half-plane $\Re s>1$ agrees with $G$ on the connected plane by the identity theorem. The residue is forced by the limit of $(s-1)F(s)$ at $1$. If it vanishes, $F$ itself has a removable singularity there. The formula uses Laurent data independently of any value assigned to a meromorphic function at its pole in a total-function formalization. ◻

#### 4.10.26.5 Lemma (the two growth inputs) [Lean, read]

For $\sigma=\Re s\ge 1/2$ and $\chi\bmod q$ nonprincipal,
$|L(s,\chi)|\le 9q(1+|s|)$.
For $\sigma>0$ and $s\ne 1$,
$|\zeta(s)|\le 1+1/|s-1|+|s|(1+1/\sigma)$.

*Proof of the character bound.* Multiplication by a unit $u$ with $\chi(u)\ne 1$ permutes the complete residue system, and multiplies its character sum by $\chi(u)$. The sum is therefore zero. Splitting an initial sum starting at $0$ into complete periods and a final block bounds its norm by $q$, since each value has norm at most $1$. Removing the term at $0$ gives the archive's bound $B=q+1$ for $A(m)=\sum_{1\le n\le m}\chi(n)$.

Finite summation by parts gives the identity
$\sum_{n=1}^{m}\chi(n)n^{-s}
=\sum_{n=1}^m A(n)(n^{-s}-(n+1)^{-s})+A(m)(m+1)^{-s}$.
By integrating the derivative of $x^{-s}$ on $[n,n+1]$, the difference has norm at most $(|s|/\sigma)(n^{-\sigma}-(n+1)^{-\sigma})$, and also at most $|s|n^{-\sigma-1}$. The second bound gives locally uniform convergence of the difference series on $\Re s>0$ by comparison on compact subsets with a constant times $n^{-1-\eta}$ for some $\eta>0$. Its summands are entire in $s$. The endpoint term tends to zero, so on $\Re s>1$ the limit agrees with the ordinary Dirichlet series. Both functions are holomorphic on the connected half-plane $\Re s>0$, and the identity theorem identifies the limit with $L(s,\chi)$ throughout it.

For the error at an integer cutoff $m\ge 1$, the first difference bound telescopes from $n=m+1$ and gives $B(|s|/\sigma)(m+1)^{-\sigma}$. Including the endpoint gives $B(1+|s|/\sigma)(m+1)^{-\sigma}$, which is bounded by the archive's $2B(1+|s|/\sigma)m^{-\sigma}$. At $m=1$, $\chi(1)1^{-s}=1$. For $\sigma\ge 1/2$ we obtain
$|L(s,\chi)|\le 1+2(q+1)(1+2|s|)\le 9q(1+|s|)$, using $q+1\le 2q$ and $1\le q$.

*Proof of the zeta bound.* For integers $n\ge 1$ define
$d_n(s)=n^{1-s}-(n+1)^{1-s}-(s-1)(n+1)^{-s}$.
Integrating the derivative of $x^{1-s}$ expresses this as
$(s-1)\int_n^{n+1}(x^{-s}-(n+1)^{-s})\,dx$.
The inner difference is $s\int_x^{n+1}t^{-s-1}\,dt$. Taking norms and using $t\ge n$ on that interval gives
$|d_n(s)|\le |s-1||s|n^{-\sigma-1}$.
Consequently $D(s)=\sum_{n\ge 1}d_n(s)$ is holomorphic on $\Re s>0$, by the same locally uniform majorant argument. Summing the definition through $m$ gives
$1-(m+1)^{1-s}-(s-1)\sum_{n=2}^{m+1}n^{-s}$.
For $\Re s>1$ the limit is $s-(s-1)\zeta(s)$. The holomorphic function $s-D(s)$ therefore agrees there with $(s-1)\zeta(s)$, extended by $1$ at $1$. The identity theorem on the connected half-plane gives equality throughout $\Re s>0$.

For $\sigma>0$, integrating the decreasing function $x^{-\sigma-1}$ on successive unit intervals bounds $\sum_{n\ge 1}n^{-\sigma-1}$ by $1+1/\sigma$. Equivalently, the archive telescopes $\sigma(n+1)^{-\sigma-1}\le n^{-\sigma}-(n+1)^{-\sigma}$. Thus $|D(s)|\le |s-1||s|(1+1/\sigma)$. For $s\ne 1$, divide $|s-D(s)|\le |s-1|+1+|D(s)|$ by $|s-1|$. ◻

#### 4.10.26.6 Proposition (circle, disk and the constants passed to Taylor) [Lean, read]

Put $R=3/2$ and let $C_g=14(81/2)^3$ and $K_g=3$. Then $|F(s)|\le C_gN^3$ for $|s-2|=R$. With $C_L=38\exp(3/2)$ from the existing bound at $1$, put $c_0=C_g+54C_L^3+1$ and $B=c_0N^3$. Then $|G(s)|\le B$ for $|s-2|\le R$, and this $B$ is the one passed to the Taylor remainder estimate of [§4.10.25](#41025-the-siegel-lower-bound-from-biquadratic-product-series).

*Proof.* On the circle we have $\Re s\ge 1/2$, $|s|\le 7/2$ and $|s-1|\ge 1/2$ by the triangle and reverse triangle inequalities. Hence $|\zeta(s)|\le 1+2+(7/2)3=27/2\le 14$, and each nonprincipal factor at level $q$ is bounded by $(81/2)q$. Multiplying gives $14(81/2)^3q_1q_2N$. Since $q_i\le N$, the archive bounds the three levels by $N$ separately and obtains $C_gN^3$. The product $q_1q_2N=N^2$ also gives an available sharper circle bound. The constants below use the archived exponent $3$.

At $1$ the available estimate $|L(1,\chi)|\le C_L\log(3q)$ and $\log(3q)\le 3q$ give $|\lambda|\le 27C_L^3 N^2$. On the circle the pole term is at most twice this, so $|G|\le C_gN^3+54C_L^3N^2\le B$. In the general form of the consumer the constants are $|C_g|+54|C_L|^3+1$ and $\max(K_g,2)$, so the present witnesses give the claimed $c_0$ and exponent. The maximum modulus principle applied to the entire $G$ supplies the same bound on the closed disk, including its removable point. The raw product bound applies on the circle. In the simple-pole case $F$ is unbounded as $s$ approaches $1$ inside the disk.

The existing Taylor lemma consumes the sphere estimate for $G$, and the circle lies in its holomorphic domain. For $7/8\le \sigma<1$, the distance ratio is $(2-\sigma)/R\le 3/4$. Cauchy bounds each coefficient $|G^{(j)}(2)|/j!$ by $B/R^j$. The previously proved Taylor estimate uses the geometric remainder bound $4B(3/4)^M$, with $4=1/(1-3/4)$. With $\ell=\log(4/3)$ and $T=8B\ge 1$ the consumer takes $M=\lceil\log T/\ell\rceil+1$. Thus $T(3/4)^M\le 1$, so the remainder allowance is at most $1/2$. The same choice satisfies $M\le 2+\log(8c_0)/\ell+(3/\ell)\log N$. Using $2-\sigma\le e^{1-\sigma}$, $1-\sigma\le 1/8$ for the $\log(8c_0)$ term, and $1-\sigma\le 1$ for the additive $2$, gives the constants $C=e^2\exp(\log(8c_0)/(8\ell))$ and $K=3/\ell$ in $(2-\sigma)^M\le C N^{K(1-\sigma)}$. These are the constants passed to the pole term in Proposition 4.10.25.3. ◻

#### 4.10.26.7 Remarks and source map

[Source register](../sources/SOURCES.md#chapter-4-real-zeros-and-the-siegel-product)

The word “product” in the analytic lemmas refers to the product of functions. The archive's hypotheses on the three characters are nonprincipality, with levels $q_1,q_2,N$. The real-character application further requests a product character $\psi$ at level $N$. If that character is principal, its $L$-factor supplies another possible pole, and the actual consumer redirects to `SameCharacterLFunctionOne`. All uniqueness arguments use an open region of agreement and a connected common domain. The removable value at $1$ is determined by the punctured neighborhood.

The following paths are relative to the fixed archive root `lean/` in `lean.tar.gz`, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Reading level R3 applies to the cited local production bodies. The maximum-modulus step that extends the sphere bound to the closed disk is an expository addition. The theorem labels refer to the archived assertions used in the Siegel argument.

| Declaration or consumer | Source and role |
|---|---|
| `Fbq`, `lamBq`, `BqEntire`, `BqGrowth`, `BqKeyOf` | `src/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean:14–46,72` defines the interfaces. |
| `zeta_sub_pole_differentiable`, `dirichlet_product_entire` | `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqEntire.lean:9–50` constructs the entire regular part. |
| `lfunction_polynomial_growth` | `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:10–71` gives the period bounds and the witness $9$. |
| `norm_tail_le`, `l_function_partial_sum`, `LFunction_eq_G` | `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean:12–169` and `src/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean:11–244` give the finite cutoff, tail and half-plane identification. |
| `norm_dz_le`, `Dz_differentiableOn`, `riemannZetaOne_eq_one_sub_of_re_pos`, `growthBound` | `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean:11–75`, `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RiemannZetaOneEqOneSubOfRePos.lean:11–87` and `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaGrowth.lean:10–95` provide the zeta estimate. The unit-interval identity and bounds are in `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormCpowSubLePoint.lean:11–78`. |
| `product_lfunction_growth_bound` | `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqGrowth.lean:11–82` supplies the boundary geometry and growth witnesses. |
| `lfunction_one_upper_bound`, `product_lfunction_key_inequality`, `bqKey` | `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LFunctionOneUpperBound.lean:10–17`, `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean:10–152`, and `src/Formalism/LandauZeroFreeBounds/FinalSiegel.lean:14–19` fix the residue budget, Cauchy input and assembly. |
| `lseries_taylor_lower_bound`, `siegel_product_character_inequality` | `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean:30–151` consumes the sphere bound, and `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean:106–183` selects the legal branch. See [§4.10.25](#41025-the-siegel-lower-bound-from-biquadratic-product-series) for those proofs. |

**Named inputs retained at their existing reading levels.** At pinned Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:75,98,150` supplies series agreement, entire continuation and change of level. The library boundaries are the underlying residue-class continuation, the change-of-level auxiliary identity, `differentiableAt_riemannZeta` and `zeta_eq_tsum_one_div_nat_add_one_cpow` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:139,214`), `tendsto_riemannZeta_sub_one_div`, `differentiable_riemannZeta₁`, `Complex.differentiableOn_compl_singleton_and_continuousAt_iff`, `Complex.differentiableOn_dslope`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `Complex.differentiableOn_tsum_of_summable_norm`, `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` and `Complex.hasSum_taylorSeries_of_entire`. The nonvanishing input `DirichletCharacter.LFunction_apply_one_ne_zero` in `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:406` remains at its prior reading level. The underlying near-one estimate `lfunction_norm_le_near_one` in `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean:89` is imported from [§4.10.24](#41024-separating-a-real-zero-from-1). The separate `ZetaNegReal` input, `zeta_negative_real_axis` in `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZetaNegReal.lean:29–66`, remains [Lean] at R2, as does `realCharConj` in `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TrivReal.lean:60–79`.

### 4.10.27 From the real-zero gap to primes in a progression {#p13-siegel-relative-pnt}

#### Motivation

For moduli bounded by a power of $\log x$, the contribution of a real exceptional zero can be absorbed into the error around $x/\varphi(q)$. In [the wider range](#410-joining-the-two-ranges-of-the-relative-progression-estimate), one keeps the contribution and measures the error relative to the resulting main term. A lower bound on $1-\beta$ makes the exceptional term small in the first estimate and supplies a minimum scale for absorbing the Abel summation and prime-power errors in the second.

#### Two hand calculations [Expository]

**Modulus $3$.** The nonprincipal character $\chi_3$ takes values $(0,1,-1)$ at residues $(0,1,2)$. Its sum over a period is zero. It is primitive since the units $1,2$ have different values and the only proper divisor of $3$ is $1$. For real $s>0$ the nonzero terms of its Dirichlet series alternate with strictly decreasing magnitudes. The series represents $L(s,\chi_3)$ there by partial summation and continuation. Every successive pair contributes positively, so
$$
L(s,\chi_3)=\sum_{k\ge0}\big((3k+1)^{-s}-(3k+2)^{-s}\big)>1-2^{-s}.
$$
At $s=1$ the first four nonzero terms sum to $1-1/2+1/4-1/5=11/20$. The next term is $1/7$, so $11/20<L(1,\chi_3)<97/140$. For $s\ge3/4$ the first pair alone exceeds $1/4$, since $(3/4)^4=81/256>1/8$. In particular there is no real zero on $[3/4,1]$. At $x=8$ the prime powers in class $1$ are $4,7$, with weights $\log2,\log7$. In class $2$ they are $2,5,8$, with weights $\log2,\log5,\log2$. The class sums are $\log14$ and $\log20$. Their difference is $\psi_{\chi_3}(8)=\log(7/10)$ and their sum is the principal character's $\log280$. Adding and subtracting these last two values and dividing by $2$ recovers the class sums.

**Modulus $4$.** The nonprincipal character $\chi_4$ takes values $(0,1,0,-1)$ at residues $(0,1,2,3)$. Its period sum is zero. The units $1,3$ coincide modulo $2$ and have opposite values, so the character is primitive. The alternating series on the odd integers gives
$$
L(s,\chi_4)=\sum_{k\ge0}\big((4k+1)^{-s}-(4k+3)^{-s}\big)>1-3^{-s}\qquad(s>0).
$$
At $s=1$ the first four terms give $1-1/3+1/5-1/7=76/105$, and the next is $1/9$. Hence $76/105<L(1,\chi_4)<263/315$. For $s\ge3/4$ the first pair exceeds $1/2$, since $(1/2)^4=1/16>1/27$. This excludes real zeros throughout $[3/4,1]$. At $x=9$ class $1$ contains the prime powers $5,9$, and class $3$ contains $3,7$. Thus $\psi(9;4,1)=\log15$, $\psi(9;4,3)=\log21$, $\psi_{\chi_4}(9)=\log(5/7)$, and the principal sum is $\log315$. The inverse projection again gives the two class sums.

These interval exclusions cover the real segment at or below $1$ in a region with coefficient at most $1/20$, since $\log(2q)\ge\log2>1/2$. Both moduli illustrate the classical estimate. The wider-range interface requires $8\mid M$.

#### The gap and the logarithmic-power range

A character is extended by zero off the units. Write $\chi_0$ for the principal character, $\psi_\chi(x)=\sum_{n\le x}\Lambda(n)\chi(n)$ and $\psi(x;q,a)=\sum_{n\le x,\ n\equiv a\bmod q}\Lambda(n)$. Prefix sums include the upper endpoint. The classical Landau–Page theorem allows at most one primitive real character of conductor at most $Q$ with a real zero in $1-c/\log Q<\beta<1$ for a suitable absolute $c>0$ and $Q\ge2$. The zero, if present, is simple. The archive uses the fixed-modulus `ZFRDirichlet` to identify the possible simple exceptional zero at one modulus. [Page (1935)](https://doi.org/10.1112/plms/s2-39.1.116)

**Siegel's lower bound [Paper].** For every $\epsilon>0$ there exists $c_\epsilon>0$ such that $L(1,\chi)\ge c_\epsilon q^{-\epsilon}$ for every primitive real nonprincipal character of conductor $q$. Positivity at $1$ gives the usual statement without absolute values. The archive's `SiegelLower` uses the norm and ranges over real nonprincipal characters at every positive modulus, including induced characters. The level comparison for that version is proved in [§4.10.25](#41025-the-siegel-lower-bound-from-biquadratic-product-series). Siegel's 1935 class-number paper supplies the classical bound, and Walfisz applied it to the progression problem in 1936. [Siegel (1935), pp. 83–86](https://doi.org/10.4064/AA-1-1-83-86) · [Walfisz (1936), pp. 592–607](https://doi.org/10.1007/BF01218882)

**The real-zero supplier [Lean, read].** The proposition `ExcBound` says that for every $\epsilon>0$ there is $h_\epsilon>0$, uniform in the positive modulus $q$, the nonprincipal character $\chi$ with $\chi^2=\chi_0$, and its real zero $\beta$, such that $1-\beta\ge h_\epsilon q^{-\epsilon}$. The quantifiers include imprimitive characters and all their real zeros. The producer `excBound_of_siegelLower` applies `exceptional_zero_bound_of` to the given lower bound and `lfunction_deriv_near_one`. The proof in [§4.10.24](#41024-separating-a-real-zero-from-1) splits at $1-1/\log(3q)$. In the near segment the ordinary derivative estimate gives
$$
\|L(1,\chi)\|\le D(1-\beta)(\log(3q))^2.
$$
Taking the lower bound at $\epsilon/3$ and using $\log(3q)\le K q^{\epsilon/3}$ gives $h_\epsilon=\min(1/K,c_{\epsilon/3}/(DK^2))$. The first entry pays for the branch outside the derivative segment. The closed wrapper `excBound` plugs in `siegelLower` from `FinalSiegel.lean`. The book follows the conditional product argument in §§4.10.25–26 and takes the complete uniform lower bound as a named [Lean] input.

The classical proof chooses the uniform $c_\epsilon$ by alternatives that can depend on the existence and choice of a reference character with a sufficiently close real zero. The argument gives no effective unconditional rule for choosing between them. Once the witness is supplied, the derivative and logarithm estimates are quantitative. Its ineffectivity passes to $h_\epsilon$, to the Siegel-dependent decay rate below, and to the amplitude and counting thresholds in the wider range. See the discussion of reference data in [§4.10.25](#41025-the-siegel-lower-bound-from-biquadratic-product-series).

**Theorem (Siegel–Walfisz relative to the ordinary main term).** For each $A>0$ there exist $b_A,C_A>0$ such that uniformly for $x\ge2$, $1\le q\le(\log x)^A$ and $\gcd(a,q)=1$,
$$
\left|\frac{\varphi(q)}{x}\psi(x;q,a)-1\right|
\le C_A e^{-b_A\sqrt{\log x}}.
$$

*Proof.* Write $L=\log x$. The input `PsiChiBound` gives a per-character error $Cx e^{-c\sqrt L}$ for $q\le e^{c\sqrt L}$, with main term $\mathbf 1_{\chi=\chi_0}x-\sum_{\beta\in B}x^\beta/\beta$. Take the region coefficient to be the minimum of the `ZFRDirichlet` coefficient and $1/20$. The zero-free region gives an empty set or a singleton $B$, with a simple real zero of a real nonprincipal character in the singleton case. The region ensures $\beta\ge1/2$, since $\log(2q)>1/2$. At $\epsilon=1/(2A)$, `ExcBound` gives
$$
(1-\beta)L\ge h_{1/(2A)}q^{-1/(2A)}L\ge h_{1/(2A)}\sqrt L,\qquad
\frac{x^\beta}{\beta}\le 2x e^{-h_{1/(2A)}\sqrt L}.
$$
With $b=\min(c,h_{1/(2A)})$, the triangle inequality gives the character error around $\mathbf 1_{\chi=\chi_0}x$ with coefficient $\max(C,0)+2$ and rate $b$. If $L^A>e^{c\sqrt L}$, then $L\le U$ for some fixed $U\ge0$, by exponential growth in $\sqrt L$. Apply $\|\psi_\chi(x)-\mathbf 1_{\chi=\chi_0}x\|\le x(L+1)$, which follows from $|\chi(n)|\le1$ and $\Lambda(n)\le\log n$. Increasing the coefficient by $(U+1)e^{b\sqrt U}$ covers that whole bounded range. This is the argument of `siegel_walfisz_character_of`, whose inputs are `psiChiBound`, `zFRDirichlet` and the supplied `ExcBound`.

For a reduced class, orthogonality gives $\varphi(q)\psi(x;q,a)=\sum_\chi \chi(a^{-1})\psi_\chi(x)$. The principal coefficient is $1$ and each coefficient has modulus one. Dividing by $\varphi(q)$ gives the absolute progression error $O_A(xe^{-b\sqrt L})$. Dividing further by the main term $x/\varphi(q)$ costs at most $L^A$. The function $u^{2A}e^{-(b/2)u}$ is bounded on $u\ge0$, so the cost is absorbed by taking $b_A=b/2$. This relative normalization is a textbook deduction from the character theorem and the archive's orthogonality lemma. $\square$

#### Keeping the exceptional term in the wider range [Lean, read]

In [§4.10.2–4](#4102-the-common-normalization) take $l=\log M$, with $8\mid M$, and fix $e=eOf(M)$ once at the modulus $M$. For $e=\mathrm{none}$ take $\theta=0,\ \beta=1,\ \eta=1$. For $e=\mathrm{some}(\chi_1,\beta)$ take $\theta=\chi_1(b)$ for the reduced class $b$ and $\eta=\min(1,(1-\beta)l)$. Write
$$
F(t)=\frac{t-\theta t^\beta/\beta}{\varphi(M)},\qquad
P_b(X)=\frac{\operatorname{li}_2(X)-\theta\operatorname{li}_2(X^\beta)}{\varphi(M)},
\qquad
\operatorname{li}_2(u)=\int_2^u\frac{dt}{\log t}.
$$
The body of `pnt_progressions_relative_weak_holds` builds the far estimate with the smoothed formula `explicitS_proof'`, its differencing theorem `differenced_explicit_formula`, and `zero_sum_bound_lossy`. The last call takes the density and repulsion witnesses `logDensityM_proof'` and `deuringHeilbronnMB_proof'`. The density witness is assembled in [§4.10.28](#p13-spaced-zero-density). Next `glue_ranges` combines that estimate with `psi_relative_near_range`, using the same option and scale $\eta$ in both ranges. Finally `prime_count_of_psi` changes the weights. The splice and the final relative-error calculation are proved in [§4.10.3](#4103-conditional-splice-and-proof). The following proof of its Abel input comes from the same-source-reviewed conversion manuscript.

**Lemma (Abel summation on the last half of the logarithmic scale) [Lean, read].**

Suppose $0\le a_n\le\Lambda(n)$, and set $S(t)=\sum_{1\le n\le t}a_n$. Let $0\le K\le1$, $|\theta|\le1$, $1/2\le\beta\le1$, and $F(t)=K(t-\theta t^\beta/\beta)$. For $X\ge16$, put $L=\log X$. If $|S(t)-F(t)|\le Dt$ for all $\sqrt X\le t\le X$, with $D\ge0$, then
$$
\left|\sum_{2\le n\le X}\frac{a_n}{\log n}
-K\left(\operatorname{li}_2(X)-\theta\operatorname{li}_2(X^\beta)\right)\right|
\le 5DX/L+40\sqrt X .
$$

**Proof.** Write $f(t)=1/\log t$. For every index $2\le n\le X$, substitute $f(n)=f(X)-\int_n^X f'(t)\,dt$ and exchange the finite sum with the integral. Since $f'(t)=-1/[t(\log t)^2]$, the result is
$$
\sum_{2\le n\le X}\frac{a_n}{\log n}
=\frac{S(X)}{L}+\int_2^X\frac{S(t)}{t(\log t)^2}\,dt.
$$
The term at $2$ is included by construction. The step function is bounded on the compact interval and the kernel is continuous there. The smooth term satisfies
$$
\frac{F(X)}{L}+\int_2^X\frac{F(t)}{t(\log t)^2}\,dt
=\frac{F(2)}{\log2}+K\left[\operatorname{li}_2(X)-\theta\left(\operatorname{li}_2(X^\beta)-\operatorname{li}_2(2^\beta)\right)\right].
$$
Indeed, the product rule for $F(t)f(t)$ reduces the integral to $F'(t)f(t)$. In the exceptional contribution $F'$ contains $-K\theta t^{\beta-1}$. Substituting $u=t^\beta$ gives $t^{\beta-1}dt/\log t=du/\log u$. Thus the factor $1/\beta$ from the weighted prediction disappears, and the minus sign persists.

In the difference of these identities, the endpoint at $X$ costs $DX/L$. Over $[\sqrt X,X]$ the integral of the difference costs at most $4DX/L^2$, since $\log t\ge L/2$. On $[2,\sqrt X]$ use the elementary Chebyshev bound $\psi(t)\le(\log4+4)t\le6t$ and $|F(t)|\le3t$. As $\log2>1/2$, the integral there costs at most $36(\sqrt X-2)$. The lower endpoint term $F(2)/\log2$ has absolute value at most $12$. The term $K\theta\operatorname{li}_2(2^\beta)$ has absolute value at most $4$, since $2^\beta\in[\sqrt2,2]$ and $1/\log u\le4$ on this interval. Adding the bounds, using $L\ge1$, gives the claim.

**Removing powers and returning to the sieve.** In the lemma take $a_n=\Lambda(n)\mathbf 1_{n\equiv b\bmod M}$ and $K=1/\varphi(M)$. The new weight on a term indexed by $p^j$ is exactly $1/j$. The excess over the actual prime count is therefore
$$
\sum_{\substack{j\ge2,\ p^j\le X\\p^j\equiv b\bmod M}}\frac1j.
$$
Each summand is at most $2\log p$ since $\log(p^j)>1/2$. Summing the weights $\log p$ over all proper powers up to $X$ costs at most $\sqrt X\log X$, since each base $p\le\sqrt X$ contributes at most $\log X$. In particular the excess is at most $4\sqrt X\log X$, the looser bound used by the archive. For example, at $X=49$ the proper powers $9,25,49$ in class $1\bmod 8$ add $3/2$ to the two primes $17,41$ after division by the logarithms. The interval $(7,49]$ keeps both primes and counts no proper powers. In class $7\bmod 8$, the prime $7$ is counted in the prefix and removed from the interval by subtracting the inclusive prefix at $7$.

In the application, write $c,A_0,C_0$ for the constants of `PsiRel`, $L=\log X$, $d=\min(c/2,c^2/2)$ and $R=e^{-dL/l}+e^{-\sqrt{dL}}$. The condition $L\ge\max(2C_0,16)l\log(l+2)$ puts the entire interval $[\sqrt X,X]$ in range, with $D=|A_0|\eta R/\varphi(M)$. This gives the absolute error $5DX/L+44\sqrt X L$ in the prefix. The proof of [§4.10.3](#4103-conditional-splice-and-proof) compares it to $P_b(X)\ge X\eta/(2L\varphi(M))$. The second error, independent of $\eta$, uses `etaOf_lower` at exponent $1$. In the selected branch, $(1-\beta)l\ge (h_1/M)\log 3$, so $c_1/M\le\eta$ with $c_1=\min(1,h_1\log3)$. In the empty branch $\eta=1$ gives the same bound. The resulting relative error is at most
$$
\left(10|A_0|+\frac{5632e^{2d}}{c_1}\right)R.
$$
This is the witness in `prime_count_of_psi`, uniform over $X$ and $b$ with the same $eOf(M)$.

The [§4.9 count](#49-counting-enough-candidates-before-the-sieve) uses two inputs. The call to `count_a` in `StagePow.lean:56` passes the assembled `PNTAPRelW` and separately passes `excBound`. In `MSqMain.lean:55–59`, `meanSquareHypW_of_pnt` takes `PNTAPRelW` and supplies that same separation theorem to `count_a`. The latter extracts its own exponent-$1$ witness and passes it to `count_pos` for the main-term lower bound. The interval contains $\pi_b(X)-\pi_b(\sqrt X)$ primes. This explains both the use of the relative prefix estimate and the strict lower endpoint in the count. The progression package in [§17.4.5](17-behrends-sphere-lemma-and-host-geometry.md#1745-from-congruence-primes-to-a-usable-host-field-scale) uses the separate declarations `exceptionalDirichletZero_unique_zeroFreeRegion` and `chebyshevPsiProgression_relative_error` in its polynomial-threshold route. The ray-class analogue is discussed in [§17.4.10](17-behrends-sphere-lemma-and-host-geometry.md#17410-the-exceptional-zero-in-the-trivial-ray-class-interval).

#### What the estimates lose without a lower bound [Expository]

In the logarithmic-power range take the model $A=1$, $q=m$, $x=2^{m^2}$ and $\beta=1-1/m^2$ for integers $m\ge2$. The range condition holds since $\log x=m^2\log2>m^2/2\ge m$. The gap is smaller than a constant times $1/\log q$ for large $m$. Even if every other term in the weighted progression formula has zero error, in the class with $\chi(a)=1$ the relative correction around $x/\varphi(q)$ has absolute value
$$
\frac{x^{\beta-1}}{\beta}=\frac{1}{2(1-1/m^2)}\ge\frac12 .
$$
It cannot be bounded by $C e^{-b\sqrt{\log x}}$ for fixed positive $C,b$. For the wider-range conversion keep $M$ and an admissible $X$ fixed and let a model real zero tend to $1$ from below. In the subtractive class $\theta=1$,
$$
0<P_b(X)=\frac1{\varphi(M)}\int_{X^\beta}^{X}\frac{dt}{\log t}
\le \frac{X(1-\beta)}{\beta\varphi(M)}.
$$
Here $\log t\ge\beta\log X$ and $1-e^{-v}\le v$ for $v\ge0$. Thus $P_b(X)$ tends to zero, while the allowed additive error $44\sqrt X\log X$ does not shrink. Its quotient by $P_b(X)$ is unbounded at this fixed $X$. Both models test inferences from the estimates with the gap hypothesis removed. Their exponents are hypothetical.

#### Reading record

The [source register](../sources/SOURCES.md#chapter-4-siegel-and-relative-pnt) identifies each body used here. The direct real-zero wrappers, Siegel–Walfisz character proof and `PNTFinal` assembly have author-level local R3. The Abel summation and proper-power supply inherit the same-source preliminary review of the original conversion manuscript. The complete `siegelLower` proof and the deeper named inputs of the density, zero-free region and character-sum packages retain their reading boundaries. The rational checks of the two examples, local source reading, independent review and Lean kernel replay have separate scopes.

### 4.10.28 Spaced zeros by character and the density constant {#p13-spaced-zero-density}

#### Motivation

The weighted zero sum in [§4.10.11](#41011-finite-height-contours-and-weighted-zero-sums) uses a density bound on finite sets of pairs $(\chi,\rho)$. It selects spaced ordinates within each character's zeros. This distinction matters twice. For a count, two characters can each contribute a zero at the same height. For a Dirichlet-polynomial mean square, the inverse difference of ordinates occurs only when the character quotient is principal. The same spacing lemma controls the size of a fiber and the sum of those inverse differences.

We prove the two spacing estimates and assemble the density bound from the principal and nonprincipal count theorems. These two theorems are supplied by the archive with the same density exponents and potentially different modulus-height thresholds.

#### Two calculations [Expository]

**A. Four characters on the same two ordinates.** Modulo $5$, the units in powers of $2$ are $1,2,4,3$. For $j=0,1,2,3$, set $\chi_j(2^k)=i^{jk}$ and extend by zero off the units. On those four units the value lists are $(1,1,1,1)$, $(1,i,-1,-i)$, $(1,-1,1,-1)$ and $(1,-i,-1,i)$. For every $j$ take the two points $3/4-i/2$ and $3/4+i/2$. These are model points for the spacing hypotheses. At $T=1/2$, each character has ordinates $-1/2,1/2$ with gap $1$. After translation by $T$ their floors are $0,1$. The count in each fiber is $2$, the whole count is $8$, and the uniform bound is $5(2T+1)=10$. Using the actual totient gives $4(2T+1)=8$. The image of the entire set under the ordinate map has cardinality $2$ because it forgets the labels. The principal fiber has size $2$, and its complement has size $6$. For a fixed pair there is one other point in its fiber, with reciprocal distance $1$. The three other characters at its own height contribute no inverse-distance term to its mean-square row.

**B. A two-sided model at unit separation.** Take $T=2$, $P=\{-2,-1,0,1,2\}$ and center $t=0$. The translated floors are $0,1,2,3,4$, so the cardinal bound is attained. The left distances are $2,1$ and the right distances are $1,2$. Both reciprocal sums are $1+1/2=3/2$, for a total of $3$. For an exact comparison with the stated bound, $\log 5=\int_1^5 du/u\ge4/5$, so $2(1+\log5)\ge18/5>3$. At the endpoint center $t=-2$ the left side is empty and the right distances are $1,2,3,4$, with sum $25/12$. More generally $P=\{-m,\ldots,m\}$ at $T=m$ has $2m+1$ points and reciprocal sum $2H_m$ at its center, where $H_m=\sum_{k=1}^m 1/k$. Integrating $1/u$ over $[1,m+1]$ gives $H_m\ge\log(m+1)$, so two sides can both contribute on the logarithmic scale.

#### Definitions

Write $\mathcal X_M$ for the complex Dirichlet characters modulo a positive integer $M$, and $1$ for the principal character modulo $M$. Our finite sets $S$ contain pairs $p=(\chi,\rho)$. For each $\chi$, the fiber $S_\chi$ consists of the pairs whose first coordinate equals $\chi$. The same-character spacing condition is
$$
(\chi,\rho),(\chi,\rho')\in S,\quad \rho\ne\rho'
\quad\Longrightarrow\quad |\Im\rho-\Im\rho'|\ge1.
$$
The threshold parameter is the natural number $q_d(M,T)=\lceil MT\rceil_{\mathbb N}$. For the heights used in the density theorem this is the ordinary ceiling. The predicate `IsLZero` requires both $L(\rho,\chi)=0$ and $(\chi\ne1\ \text{or}\ \rho\ne1)$, excluding the principal pole from the formal zero predicate. We count distinct pairs. The weights recording multiplicities enter later through the consumer in §4.10.11.

The predicates `Spacing` and `Triv` require just the height window and spacing, with $T\ge0$. The first applies to finite subsets of the real line. The second applies to the sets of pairs above, regardless of the real parts and the zero predicate. In the archive $q_d$, `Spacing`, and `Triv` are defined in `PNTDensSt`, and `LogDensityM` is defined in `DeuringHeilbronnM`.

#### Spacing and the two bounds [Lean, read]

**Harmonic bound and floor separation.** For an integer $n\ge1$, each term $1/k$ for $2\le k\le n$ is at most $\int_{k-1}^k du/u$. Adding the first term yields $H_n\le1+\log n$. The empty sum is $H_0=0$. In `space_harm`, the positive case uses Mathlib's harmonic estimate with the rational harmonic sum cast to the reals. Lean sets $\log 0=0$ for the separate zero case. If $a,b\ge0$ have equal natural floor $k$, then $k\le a,b<k+1$. Each of $a-b$ and $b-a$ is strictly less than $1$, giving $|a-b|<1$. This is `floor_eq_close`.

**One side.** Let $Q$ be finite and let $f$ map its points to distances in $[1,2T]$. Assume $|f(x)-f(y)|\ge1$ for distinct $x,y\in Q$. Then $x\mapsto\lfloor f(x)\rfloor$ is injective by floor separation. Positivity gives $1/f(x)\le1/\lfloor f(x)\rfloor$. Thus
$$
\sum_{x\in Q}\frac1{f(x)}
\le \sum_{k\in\{\lfloor f(x)\rfloor:x\in Q\}}\frac1k
\le H_{\lfloor2T\rfloor}
\le 1+\log(2T+1).
$$
The middle inequality uses inclusion in the integers from $1$ to $\lfloor2T\rfloor$. If $\lfloor2T\rfloor=0$, the sum is empty and $\log(2T+1)\ge0$. Otherwise apply the harmonic bound and monotonicity of the logarithm. This is `space_side`.

**The window and a deleted center.** Suppose $P\subset[-T,T]$ is finite and any two distinct points are at least one unit apart. The shifted floor map $x\mapsto\lfloor x+T\rfloor$ is injective, since translation preserves differences and the shifted arguments are nonnegative. Its image lies among the integers $0$ through $\lfloor2T\rfloor$, including both endpoints when $2T$ is integral. This proves
$$
|P|\le\lfloor2T\rfloor+1\le2T+1.
$$
For $t\in P$, erase $t$ and split into points strictly above and strictly below $t$. On each side, the distances $x-t$ or $t-x$ lie in $[1,2T]$. The absolute difference between two distances on the same side is the absolute difference of the original points. The one-sided estimate therefore applies twice and yields
$$
\sum_{x\in P\setminus\{t\}}\frac1{|t-x|}\le2(1+\log(2T+1)).
$$
This proves `zero_spacing`. At $T=0$ the packing bound allows at most the singleton $\{0\}$, whose deleted-center sum vanishes. If $P$ is empty, the center assertion is vacuous.

**The character count.** On each $S_\chi$, the map $(\chi,\rho)\mapsto\Im\rho$ is injective. An equal ordinate for distinct pairs in that fiber would give a gap of zero. Its image $P_\chi$ is unit spaced and lies in $[-T,T]$. The actual fibers partition $S$, including empty fibers, so
$$
|S|=\sum_{\chi\in\mathcal X_M}|S_\chi|
=\sum_{\chi\in\mathcal X_M}|P_\chi|
\le\varphi(M)(2T+1)\le M(2T+1).
$$
Mathlib supplies $|\mathcal X_M|=\varphi(M)$ over $\mathbb C$, which has enough roots of unity. The archive uses this in `space_card_char_le` and sums the fiber sizes in `trivial_bound`. Coincident ordinates in different fibers remain in their respective summands.

#### The harmonic weight in a mean-square row

Fix $p=(\chi,\rho)\in S$ in the block $U<n\le2U$. The exponent used in the pair estimate is determined by $w=(\rho-\sigma)+\overline{(\rho'-\sigma)}$, with $\Im w=\Im\rho-\Im\rho'$. Assume $T\ge2$, $U\ge1$ is an integer, and both real parts belong to $[\sigma,1]$ with $\sigma\ge1/2$. Then $0\le\Re w\le1$ and $|w|\le1+2T$. The character factor is $\chi\overline{\chi'}=\chi(\chi')^{-1}$. If $\chi'\ne\chi$, the named estimate `pair_cross_bound` for a nonprincipal quotient costs at most $4(M+1)(2+2T)$ even when $\Im w=0$. If $\chi'=\chi$ and $p'\ne p$, the gap makes $\Im w\ne0$. The named principal estimate `pair_same_bound` contributes the extra term $4U^{1-\Re w}/|\Im w|\le4U/|\Im w|$ for $U\ge1$. The diagonal costs at most $U$, by bounding each of the $U$ summands by one.

Sum the reciprocal term over the one fiber of $p$ with the center deleted. Formally `off_diagonal_bound` rewrites a sum that includes the diagonal using Lean's $1/0=0$, then uses the erased ordinate image. Define the matrix entry by
$$
K(p,p')=\sum_{U<n\le2U}\chi(n)\overline{\chi'(n)}\, n^{-w}.
$$
The row bound is
$$
\sum_{p'\in S}|K(p,p')|\le U\bigl(9+8\log(2T+1)\bigr)+|S|\,8(M+1)(2+2T).
$$
Indeed the diagonal and inverse-distance parts cost at most $U+4U\cdot2(1+\log(2T+1))$. The remaining bound per pair is $4(M+1)(2+2T)$, widened to $8(M+1)(2+2T)$ in the producer. The first component of `zero_spacing` bounds the fibers for the trivial count. Its second component bounds these matrix rows. The pair estimates, the duality argument for the mean square and the block-detection proofs remain named inputs.

#### Assembling LogDensityM [Lean, read]

**The two input counts.** Let $C_0,C_1\in\mathbb R$ and $q_0,q_1\in\mathbb N$ be the witnesses supplied, respectively, by `zero_count_first : Count0` and `zero_count_second : Count1`. In each case the witnesses precede the universal quantifiers over $M,T,\sigma$ and the finite set of pairs. Both inputs require $M\ge3$, $T\ge2$, $\sigma\ge3/4$, $q_i\le q_d(M,T)$, and $\sigma\le\Re\rho<1$, $|\Im\rho|\le T$ on their sets. Count0 requires the principal character everywhere, `IsLZero`, and spacing of all distinct pairs on its set. Count1 requires nonprincipal characters, the equation $L(\rho,\chi)=0$, and spacing within each character. The respective conclusions are $|S_i|\le C_i F$, where
$$
X=MT,\qquad F=X^{24(1-\sigma)}(\log X)^{10}.
$$

**The conclusion and its quantifiers.** There exist reals $A,B,C$ such that for every natural $M\ge3$ with the nonzero instance, every real $T\ge2$ and $\sigma\ge1/2$, and every finite set $S$ of pairs modulo $M$ satisfying same-character spacing, the conditions $\sigma\le\Re\rho$, $|\Im\rho|\le T$ and `IsLZero` on its members imply
$$
|S|\le C X^{A(1-\sigma)}(\log X)^B.
$$
In `log_density_bound` the witnesses are
$$
A=24,\qquad B=10,\qquad Q=\max(q_0,q_1),\qquad C=|C_0|+|C_1|+3+3Q.
$$
Here $Q$ is taken in $\mathbb N$ and cast to $\mathbb R$ in the constant. The quantifiers impose no upper bound on $\sigma$, no lower cutoff on $q_d$, and no positivity conditions on the existential witnesses. These particular witnesses are positive. Lean first proves the inequality with a natural tenth power and identifies it with the real-power expression at the witness $B=10$.

**Proof.** Since $X\ge6>e$, $\log X\ge1$. The character count gives $|S|\le M(2T+1)\le3X$. If $S$ is empty, the positive base $X$, the positive logarithm and $C\ge0$ give $0\le CF$ even for $\sigma>1$.

Suppose now that $S$ contains a pair. Mathlib's half-plane nonvanishing theorem applies at $\Re\rho\ge1$ under precisely the guard $(\chi\ne1\ \text{or}\ \rho\ne1)$. This would contradict the zero equation. The wrapper `re_lt_one_of_isLZero` therefore gives $\Re\rho<1$ for every pair. Using any one member we get $\sigma<1$, so $X^{24(1-\sigma)}\ge1$ and $F\ge1$.

- **Below the ceiling threshold** ($q_d(M,T)<Q$). Then $X\le q_d(M,T)<Q$. Hence $|S|\le3X<3Q\le3QF\le CF$.
- **Below the detector's real-part threshold** ($Q\le q_d(M,T)$ and $\sigma<3/4$). Then $24(1-\sigma)>6>1$ and $X>1$, so $X\le X^{24(1-\sigma)}\le F$. Thus $|S|\le3X\le3F\le CF$.
- **In the range of both counts** ($Q\le q_d(M,T)$ and $3/4\le\sigma$). Filter into $S_0$ with $\chi=1$ and $S_1$ with $\chi\ne1$. Both inherit the height and lower real-part conditions, and the wrapper gives the strict upper real-part bound. On $S_0$ every pair of distinct members has the same character, so the inherited spacing applies to all distinct members. Its zero predicate is retained. On $S_1$ keep the same-character spacing and project the predicate to $L(\rho,\chi)=0$. The ceiling bound implies both $q_i\le q_d(M,T)$. The filters are disjoint and exhaustive. Since $F\ge0$,
$$
|S|=|S_0|+|S_1|\le C_0 F+C_1 F\le (|C_0|+|C_1|)F\le CF.
$$
The three contributions to $C$ cover both counts, the low-$\sigma$ count and the bounded-$X$ count uniformly. Their witnesses depend only on the two existing count theorems, so the assembled constants can be chosen before $M,T,\sigma,S$. ◻

#### Remarks and reading boundary

**Deleting the same-character spacing hypothesis.** Modulo $5$, use just the principal character and the model points $3/4+i(j/n)$ for $0\le j\le n$. Their ordinates lie in $[0,1]$ and are distinct. At $T=2$ and $n\ge25$, there are $n+1>5(2T+1)=25$ pairs and $n+1>2T+1$ ordinates. At center $0$, the reciprocal sum is $nH_n\ge n$. The proposed upper bound is $2(1+\log5)\le10$, by integrating $1/u\le1$ from $1$ to $5$. The packing estimate and the reciprocal estimate both fail in this family, and no repeated ordinate or infinite term is needed. These are counterexamples to the geometric estimates with a hypothesis removed. The points in the calculations are prescribed complex locations.

**Where the witness is used.** `PNTFinal` names the assembled term `logDensityM_proof'` and passes it with the repulsion theorem to `zero_sum_bound_lossy`. That consumer calls `density_norm`, which expresses the bound in terms of the distance cut $v/\log(MT)$ from $1$, and passes the result to `zeroSum_core`. With the witnesses here the normalization gives $a=24$, $B=10$ and the same $C$, since it replaces the entries by $\max(A,1)$, $\max(B,0)$ and $\max(C,1)$. At the call to the normalized count in `zeroSum_core`, the height is $M^{A_1}+3$ and the layer parameter is $v=j+1$. This supplies the count for the spaced representatives used in the weighted zero sum of [§4.10.11](#41011-finite-height-contours-and-weighted-zero-sums).

**Classical context [Community].** Gallagher's large-sieve density estimate near $1$ and Tao's exposition of Linnik's theorem give context for using density estimates in progression theorems. The witnesses, the finite set of labeled pairs and the threshold proof here follow the pinned archive. [Gallagher 1970](https://doi.org/10.1007/BF01403187) · [Tao 2015](https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/)

**Source and status.** With $J$ the archive directory `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/`, the spacing and packing proofs are J/`PNTDensSpace.lean:11–177`, the harmonic row application is J/`PNTDensBlock.lean:14–156` with named pair estimates, and the nonvanishing wrapper and constant assembly are J/`PNTDens.lean:13–109`. These are author-level local R3. The deeper block counts in J/`ZeroCountFirst.lean:90` and J/`SecondBlockCount.lean:87` are [Lean] inputs whose detector and mean-square proofs remain [Open] in this reading. The Mathlib nonvanishing and character-cardinality theorems are inherited inputs. The worked examples have an exact arithmetic certificate. Independent review, Lean kernel replay and declaration-level reachability from Main remain [Open] for this section. [Pinned source ledger](../sources/SOURCES.md#ch04-spaced-zero-density-sources)

## 4.11 From separated inertia lines to residual irreducibility

### Motivation

The archive's bad-prime selection supplies two hosts with disjoint exceptional sets. Its two selectors use the bound `ChoiceCount` and a candidate count exceeding that bound. [§4.10.22](#41022-how-exceptional-prime-sets-avoid-each-other) proves the bound and gives both calls. The density and window estimates are separate inputs at those calls. At least one host therefore avoids the residue prime $\ell$. Its polynomial labels describe inertia eigenvalues of **one** residual representation. A subrepresentation has the same dimension at every label, and at each label that dimension must be a sum of lengths of Frobenius orbits. A different argument is needed on restriction to a normal subgroup. A sufficiently long prime cycle forces the minimal invariant pieces either to fill the space or to give a transitive permutation action forbidden by the solvable quotient. [A2 StatementI.lean:29–58 and StatementT.lean:19–52](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

### Two hand calculations [Expository]

**Two lines over $\mathbb F_5$.** Take $f=X^2+1$ over $\mathbb F_3$. With $a^2=-1$ in $\mathbb F_9$, its roots are $a$ and $a^3=-a$, interchanged by cubing. They have order four. For $\ell=5$ their prime-to-$5$ parts are the roots themselves. Send $a$ to $2$ in $\mathbb F_5$, so $a^3$ goes to $3$. The compatible root-of-unity construction below extends this multiplicative prescription. Use
$$
T=\begin{pmatrix}2&0\\0&3\end{pmatrix},
\qquad P=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$
Then $PTP^{-1}=T^3$ and the characteristic polynomial of $T$ is $(X-2)(X-3)=X^2+1$ in the target field. If $(u,v)$ lies in a $T$-stable subspace with $u\ne0$, then $(T-3)(u,v)=(-u,0)$ recovers the first line. Using $T-2$ recovers the second when $v\ne0$. The group generated by $T,P$ acts irreducibly, while its normal subgroup $\langle T\rangle$ has both invariant lines. The quotient has order two. The calculation survives over $\overline{\mathbb F}_5$. The transposition leaves no fixed points.

**Removing a nontrivial $2$-part.** Over $\mathbb F_{83}$ take $f=X^2-X+1$. A root $b$ has $b^3=-1$, and $b\ne-1$, so it has order six. Since $6$ does not divide $82$, neither root lies in $\mathbb F_{83}$. Its conjugate is $b^{83}=b^5$. The exponent for the prime-to-$2$ part is $2\cdot2=4$, since $2^{-1}=2$ modulo $3$. The two parts are $b^4$ and $b^2$, both of order three. Send $b^4$ to $\omega$ with $\omega^2+\omega+1=0$ in $\mathbb F_4$. Then $b^2$ goes to $\omega^2$, and the target characteristic polynomial is $X^2+X+1$. With $T=\operatorname{diag}(\omega,\omega^2)$ and the same swap $P$, we get $PTP^{-1}=T^{83}=T^5$. The difference $\omega-\omega^2=1$ in characteristic two makes $(T-\omega^2)(u,v)=(u,0)$. Together these operators act irreducibly on $\mathbb F_4^2$ and after extension to $\overline{\mathbb F}_2$. Over $\mathbb F_2$, multiplication by $\omega$ on the two-dimensional space $\mathbb F_4$ has minimal polynomial $X^2+X+1$ and no invariant line. After extension to $\mathbb F_4$ this cyclic action splits into two eigenlines. In these calculations $5\notin BB(2,3)=\{2,3\}$ and $2\notin BB(2,83)=\{41,83\}$. For the latter check $83-1=2\cdot41$ and $83^2-1=2^3\cdot3\cdot7\cdot41$, so in particular $2^{12}=4096<83^2$. Both examples illustrate local mechanisms at rank two. The restriction theorem's cycle inequalities require rank at least eight.

### Definitions and hypotheses

Let $BB(N,g)$ be $\{g\}$ together with the primes $s$ for which $g^d<s^{4v_s(g^d-1)}$ for some $1\le d\le N$. For a prime $\ell$ and $x\ne0$ in $\overline{\mathbb F}_g$, write its finite multiplicative order as $m=\ell^b m'$ with $\gcd(\ell,m')=1$. Define $x_{\ell'}=x^{\ell^b c}$, where $c$ is the inverse of $\ell^b$ modulo $m'$ and the exponent is zero when $m'=1$. This is the prime-to-$\ell$ part `primeToPart`. The exponent is $1$ modulo $m'$ and $0$ modulo $\ell^b$, so the operation projects onto the component of order prime to $\ell$. [A2 StatementI.lean:10–12, StatementT.lean:9–17 and IrreducibilityOfRestriction.lean:15–35](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

For a prime $g$, let $P$ be a type of labels and $J$ a type indexing units $c_{vj}\in\mathbb F_g^\times$. Write $R_v$ for the multiset of roots of $f_v\in\mathbb F_g[X]$ in $\overline{\mathbb F}_g$. The predicate `IsGood` requires:

1. Every $f_v$ is monic of degree $N$ and $f_v(0)\ne0$.
2. Every $f_v$ is squarefree.
3. For every prime $s\notin BB(N,g)$ and every $v$, the map $x\mapsto x_{s'}$ is injective on $R_v$.
4. For every prime $s\ne g$, every $v,j$ and every $x\in R_v$, we have $x_{s'}\ne(c_{vj})_{s'}$, with the unit viewed in the algebraic closure.
5. For every $a\ge1$ with $2a\le N$, some $f_v$ has no divisor of degree $a$ over $\mathbb F_g$.
6. Some $f_{v_0}$ has an irreducible divisor of prime degree $p$ with $N<2p$ and $p+3\le N$. [§4.10.18](#41018-counting-the-prime-degree-factor-exception) counts the labels that lack such a factor.

The label type $P$ may depend on $g$. Item 5 concerns the whole family. The label $v_0$ in item 6 can be reducible. [A2 StatementT.lean:19–29](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

### Lemma 1. Recovering coordinates from inertia [Lean, read]

Let $G$ be a group, $k$ a field, $V$ a $k$-space with basis $(e_i)$ indexed by $\Omega=\{1,\ldots,N\}$, and $\rho$ a representation of $G$ on $V$. Suppose $I\le G$ and $\rho(y)e_i=\chi_i(y)e_i$ for $y\in I$. The archive gives the scalar functions on $G$, and this lemma uses their restrictions to $I$. Assume that for every $i\ne j$ some $y\in I$ satisfies $\chi_i(y)\ne\chi_j(y)$.

**Diagonal coordinates.** Apply $\rho(y)$ linearly to $v=\sum_i v_i e_i$ and take coordinate $m$. This gives $(\rho(y)v)_m=\chi_m(y)v_m$. If $v$ transforms by $\chi_j$ on $I$, then for every $i\ne j$ a separating $y$ gives $(\chi_j(y)-\chi_i(y))v_i=0$. Division forces $v_i=0$ and leaves $v=v_j e_j$.

**Recovery in an invariant subspace.** Let $W$ be $I$-invariant and suppose $w\in W$ has $w_i\ne0$. Start with $u=w$. For each $j\ne i$, choose $y_j\in I$ with $\chi_i(y_j)\ne\chi_j(y_j)$ and replace $u$ by
$$
u'=\rho(y_j)u-\chi_j(y_j)u.
$$
Invariance and linearity keep $u'$ in $W$. Coordinate $l$ is multiplied by $\chi_l(y_j)-\chi_j(y_j)$. This kills coordinate $j$, leaves previously killed coordinates zero, and preserves a nonzero coordinate $i$. Induction over all $j\ne i$ leaves $u=u_i e_i$. Multiplication by $u_i^{-1}$ gives $e_i\in W$. Every $w\in W$ is then a sum along recovered basis lines, so $W$ is the span of the lines it contains. Its dimension equals their number. The construction permits a different $y_j$ at each step. [A2 RestrictionOfBlocksAndJordan.lean:14–86,105–115,136–152](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

### Lemma 2. Restriction through a solvable quotient [Lean, read]

Keep the data of Lemma 1 and assume $8\le N$. Let $H\triangleleft G$ contain $I$, with $G/H$ finite and solvable, and assume $\rho$ is irreducible over $k$. Suppose $\Phi\in G$ normalizes $I$ in both directions and $\pi\in\operatorname{Sym}(\Omega)$ satisfies
$$
\chi_{\pi(i)}(y)=\chi_i(\Phi^{-1}y\Phi)\qquad (y\in I).
$$
Assume $\pi$ contains a cycle of prime length $p$ with $N<2p$ and $p+3\le N$. Then $\rho|_H$ is irreducible over $k$.

The proof uses two finite permutation results at their archive interfaces.

- **`BlocksCycle` [Lean].** A group $K$ acts on a finite set $\Omega$ and preserves a finite family of equicardinal, pairwise disjoint subsets covering $\Omega$. If an element acts as a single nontrivial $p$-cycle with support size $p$, where $p$ is prime and $|\Omega|<2p$, the family has one block or $|\Omega|$ blocks.
- **`JordanTransitive` [Lean].** Suppose a group $K$ acts transitively on a finite set $\Omega$ and contains an element inducing a single nontrivial $p$-cycle of support size $p$, where $p$ is prime, $|\Omega|<2p$ and $p+3\le|\Omega|$. The action image contains $\operatorname{Alt}(\Omega)$ and $K$ is nonsolvable. The archive derives primitivity in this range and then invokes the primitive prime-cycle theorem.

The first group need only preserve the partition. To see the block bound, take the block containing a moved point. Its orbit under the single $p$-cycle has size one or $p$. In the first case it contains the whole moved orbit, so two blocks would require at least $2p$ points. In the second case there are at least $p$ blocks, so each must be a singleton. Transitivity is required of the quotient action in the second result. [A2 StatementI.lean:29–58 and Jordan.lean:8–118](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

**Proof.** Let $W_0$ be a nonzero $H$-invariant subspace. Choose a nonzero $H$-invariant $W$ of least dimension. Each translate $W_g=\rho(g)W$ is $H$-invariant because $g^{-1}hg\in H$ for $h\in H$, and has dimension $\dim W$. By Lemma 1, $W_g$ is the span of $B_g=\{i:e_i\in W_g\}$. If two such subsets share a point, the corresponding intersection is nonzero and $H$-invariant. Minimality and equality of dimensions give equality of the two subspaces. Thus distinct $B_g$ are disjoint and equicardinal. The sum of the $W_g$ is nonzero and $G$-invariant, so it is $V$ and the $B_g$ cover $\Omega$. This is a finite family even for infinite $G$. [A2 RestrictionOfBlocksAndJordan.lean:90–230,282–298](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

For $y\in I$ the identity $y\Phi=\Phi(\Phi^{-1}y\Phi)$ shows that $\rho(\Phi)e_i$ transforms by $\chi_{\pi(i)}$. By Lemma 1 it is a nonzero scalar multiple of $e_{\pi(i)}$. This gives $\pi B_g=B_{\Phi g}$. Iteration gives an action of $\langle\pi\rangle$ on the partition, since every power can be represented by a nonnegative power. With $M=\operatorname{ord}(\pi)$, we have $p\mid M$, so $\pi^{M/p}$ has order $p$. Its nontrivial cycles have length $p$ and exactly one fits because $N<2p$. Apply `BlocksCycle` to $\langle\pi\rangle$ and this element. [A2 RestrictionOfBlocksAndJordan.lean:231–315 and GaloisIrreducibilityProofs/PowerPCycle.lean:5–24](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

If there is one block then $W=V$ and minimality forces $W_0=V$. If there are $N$ blocks, each is a singleton. Every $g\in G$ now permutes the lines $k e_i$: each line is some $W_{g'}$ and $g$ sends it to $W_{gg'}$. Uniqueness of the target line gives a group action, transitive because the translates of $W$ cover all the lines. Every $h\in H$ fixes each line by invariance of the translates. The action thus factors through $G/H$, where $\Phi^{M/p}$ induces the same single $p$-cycle. `JordanTransitive` makes $G/H$ nonsolvable, a contradiction. These exhaust the two block outcomes, and $W_0=0$ is already allowed. [A2 RestrictionOfBlocksAndJordan.lean:316–433](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

### The GoodTuple criterion and its proof [Lean, read]

Let $g_0,g_1$ be primes, with families $(f_{iv},c_{ivj})$ satisfying `IsGood` at rank $N$ for both $i\in\{0,1\}$ and disjoint $BB(N,g_0),BB(N,g_1)$. Fix a prime $\ell$ and any $i$ with $\ell\notin BB(N,g_i)$. Put $g=g_i$ and $k=\overline{\mathbb F}_\ell$. Let $\rho:G\to\mathrm{GL}_N(k)$ be a group homomorphism. For each $v\in P_i$, give elements $\tau_v,\phi_v\in G$ and a multiplicative monoid homomorphism $\iota_v:\overline{\mathbb F}_g\to k$, injective on nonzero elements of order coprime to $\ell$. Require
$$
\rho(\phi_v\tau_v\phi_v^{-1})=\rho(\tau_v)^g,
\qquad
\det(X\operatorname{Id}-\rho(\tau_v))=\prod_{x\in R_v}(X-\iota_v(x_{\ell'})).
$$
Then $\rho$ is irreducible on $G$ and on every normal $H$ with $G/H$ finite solvable and every $\tau_v\in H$. Also, for every $v,j$, the transported unit $\iota_v((c_{ivj})_{\ell'})$ is excluded from the roots of the displayed characteristic polynomial. The subgroup need not contain the elements $\phi_v$. [A2 StatementT.lean:31–52](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

**Roots and Frobenius.** By conditions 1–2, $R_v$ consists of $N$ distinct nonzero roots. Frobenius $x\mapsto x^g$ is injective and preserves $R_v$. Index the roots $r_{va}$, with basis index $a$, so that $r_{v,\sigma_v(a)}=r_{va}^g$. A root on a cycle of length $d$ satisfies $r_{va}^{g^d-1}=1$. Frobenius preserves order, so the exponent defining the prime-to part commutes with this power. Put $L_{va}=\iota_v((r_{va})_{\ell'})$. The values are nonzero because monoid homomorphisms send units to units. They are distinct by condition 3 and the transport's restricted injectivity. We have $L_{v,\sigma_v(a)}=L_{va}^g$, so the transported values carry the same orbit permutation. [A2 IrreducibilityOfRestriction.lean:15–133,427–459](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

**Descent of a union of cycles.** For any union $S$ of $\sigma_v$-orbits, the product $\prod_{a\in S}(X-r_{va})$ is fixed coefficientwise by Frobenius. Its coefficients lie in $\mathbb F_g$, since $X^g-X$ already has the $g$ elements of $\mathbb F_g$ as roots and has degree $g$. The product divides $f_{iv}$ in the closure. Monic division over $\mathbb F_g$ gives the same remainder after extension, hence divisibility over $\mathbb F_g$ and a divisor of degree $|S|$. Conversely choose a root $r$ of an irreducible divisor $q$. Its Frobenius orbit consists of roots of $q$, so its length is at most $\deg q$. Its orbit product shares $r$ with $q$ and is divisible by $q$ by Bézout, giving the opposite inequality. In particular condition 6 gives a $p$-cycle. [A2 IrreducibilityOfRestriction.lean:135–255 and Lemmata/GeneralBFactSecondBis/Imports.lean:7–47](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

**Full-group irreducibility.** For each $v$, $A_v=\rho(\tau_v)$ has $N$ distinct eigenvalues in $k$ and a basis of eigenvectors. Independence follows by applying products of the operators $A_v-\lambda$ to isolate each eigenvector in a putative dependence. If $U$ is $G$-stable of dimension $d$, Lemma 1 at this label shows $U$ is spanned by a subset of the eigenlines. From $F_v A_v=A_v^g F_v$, where $F_v=\rho(\phi_v)$, the $a$-line maps to the $\sigma_v^{-1}(a)$-line, the unique eigenline of $A_v^g$ with value $L_{va}$. Because $F_v U=U$, both the subset and its complement are unions of cycles. If $0<d<N$, choose $a_0=\min(d,N-d)>0$, so $2a_0\le N$. At every $v$ the smaller union descends to a divisor of degree $a_0$, contradicting condition 5. The archive's `irred` uses characteristic-root multisets for $0\subset U$ and $U\subset V$. The second dimension is paid for by subtracting multisets, and power stability is preserved by cancellation. The simple spectrum here permits the complementary-set proof. The eigenbasis varies with $v$, while $U$ and its dimension refer to the same representation. [A2 IrreducibilityOfRestriction.lean:259–390,461–489 and GaloisIrreducibilityProofs/IrredOf.lean:12–44, LemmaAOf.lean:25–69](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

**Restriction on the same representation.** Use $v_0,p$ from condition 6. The inequalities force $p>3$ and $N\ge8$. Work in $\Gamma=\rho(G)$ on the original $k^N$, and put $H'=\rho(H)$. It is normal, and $G/H\twoheadrightarrow\Gamma/H'$ is onto, so $\Gamma/H'$ is finite solvable. Invariance under $G,H$ is equivalent to invariance under $\Gamma,H'$, respectively.

Set $T=\rho(\tau_{v_0})$, $\Phi=\rho(\phi_{v_0})$ and $I=\langle T\rangle\le H'$. A common multiple of the finite orders of $L_a=L_{v_0a}$ kills $T$ on the eigenbasis, so $I$ is finite. Conjugation by $\Phi$ sends $I$ into itself by $\Phi T\Phi^{-1}=T^g$, and is onto $I$ by finiteness and injectivity. The scalar functions on the image group can be taken as the indicated coordinates of $ye_a$. On $I$ they satisfy $\chi_a(T^n)=L_a^n$ and separate at $T$. If $\Phi^{-1}y\Phi=T^n$, then $y=T^{gn}$, and
$$
\chi_{\sigma_{v_0}^{-1}(a)}(y)
 =(L_{\sigma_{v_0}^{-1}(a)}^g)^n=L_a^n
 =\chi_a(\Phi^{-1}y\Phi).
$$
Thus $\pi=\sigma_{v_0}^{-1}$ satisfies Lemma 2, with the same cycle lengths as $\sigma_{v_0}$. The lemma yields irreducibility on $H'$, hence on $H$. Passage to the image turns finite order of a representing matrix into finite order of the group element used to define $I$. The original $\tau_{v_0}$ in $G$ may have infinite order. [A2 IrreducibilityOfRestriction.lean:394–423,506–636](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

**Unit exclusion.** The singleton in $BB(N,g)$ gives $\ell\ne g$. A root equality at the transported unit would identify it with some $L_{va}$. The two original prime-to-$\ell$ parts are nonzero with orders coprime to $\ell$. Transport injectivity would give equality before transport, contrary to condition 4. This proves the third projection. [A2 IrreducibilityOfRestriction.lean:491–504,636–641 and IrreducibilityOfGoodTuple.lean:17–19](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

### Remarks and consumers

**Deleting hypotheses [Expository].** Over $k=\overline{\mathbb F}_3$, take a primitive seventeenth root $z$ and an eight-dimensional basis indexed by $j\in\mathbb Z/8\mathbb Z$. Let $T e_j=z^{2^j}e_j$ and $P e_j=e_{j+1}$. Since $2^4=-1$ modulo $17$, the order of $2$ is eight. Thus $P^{-1}TP=T^2$ and $H=\langle T\rangle$ is normal in $G=\langle T,P\rangle$ with quotient cyclic of order eight. Coordinate recovery and the transitive shift prove irreducibility on $G$, while $H$ fixes each line. In Lemma 2 take $I=H$, $\Phi=P$, $\pi(j)=j+1$ and $p=5$. The scalar identity holds because $\chi_j(P^{-1}T^n P)=z^{2^{j+1}n}$. Both inequalities hold, while $\pi$ has no $5$-cycle. Deleting only prime-cycle membership invalidates Lemma 2, even with a transitive shift.

For deletion of separation, keep $G,H$ and take $I=1$, $\Phi=1$, $\chi_j(y)=1$, and $\pi=(0\,1\,2\,3\,4)$ with $p=5$. Every other hypothesis of Lemma 2 holds, including the character identity on $I$, and $H$ still fixes proper lines. For the transitivity premise in `JordanTransitive` itself, $C_5$ acting by a five-cycle and fixing three other points satisfies every numerical and cycle premise. This action is intransitive and $C_5$ is solvable.

**Nonempty criterion at rank eight [Expository].** Take $g_0=5,g_1=83$, $\ell=17$, and two labels at each $g$. Use the minimal polynomial of a primitive element of $\mathbb F_{g^8}$ and the product of the analogous degree-three and degree-five polynomials. Give $J$ one index, with unit $1$ at every label. Explicitly, take $f_{0,0}=X^8+X^2+2X+3$ and $f_{0,1}=(X^3+2X^2+4X+2)(X^5+X^4+X^3+3X+2)$ over $\mathbb F_5$, using the common $96844$th root $X^{(5^{15}-1)/96844}$ in $\mathbb F_5[X]/(X^{15}+X^2+2)$ for the second label, and take $f_{1,0}=X^8+X+8$ and $f_{1,1}=(X^3+68X^2+60X+17)(X^5+67X^4+38X^3+40X^2+25X+17)$ over $\mathbb F_{83}$, using $X^{(83^{15}-1)/27466930396666}$ in $\mathbb F_{83}[X]/(X^{15}+X+17)$. A primitive root of order $g^d-1$ has orbit length $d$ because $0<g^t-1<g^d-1$ for $0<t<d$. The first label excludes all proper positive divisor degrees and the second supplies $p=5$. The distinct orbits give squarefreeness and nonzero constant coefficients.

The exact factorizations of $g^d-1$ for $1\le d\le8$ give
$$
\begin{aligned}
BB(8,5)&=\{2,3,5,11,13,31,71,313,19531\},\\
BB(8,83)&=\{41,83,367,2269,19121,48037081,11411291417\}.
\end{aligned}
$$
For each label let $m$ be the least common multiple of $g^d-1$ over its constituent degrees. Use one primitive $m$th root, with exponents $E=(m/(g^d-1))g^t$ for $0\le t<d$. To test prime-to-$s$ parts reduce $E$ modulo the prime-to-$s$ factor of $m$. For $s\nmid m$ the original exponents are distinct and nonzero modulo $m$. For $s\mid m$ this finite test gives eight distinct residues at every $s\notin BB(8,g)$ and no zero residue at any $s\mid m$. A zero residue would give the unit $1$. At $g=83$ the degree-eight label loses a nontrivial $17$-part while retaining eight distinct values. The degree-three and degree-five label already has orders prime to $17$. [A2 StatementI.lean:10–12 and StatementT.lean:19–29 for the tested predicates](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

The complete check at the level of orders is summarized here. The third column is the set of primes dividing the order of the common primitive root. The last column lists all primes whose removal produces a root collision.

| $g$, degrees | $m$ | Prime divisors of $m$ | Collision primes |
|---|---:|---|---|
| $5$, $8$ | $390624$ | $2,3,13,313$ | none |
| $5$, $3+5$ | $96844$ | $2,11,31,71$ | $31$ |
| $83$, $8$ | $2252292232139040$ | $2,3,5,7,13,17,41,53,73,19121$ | none |
| $83$, $3+5$ | $27466930396666$ | $2,19,41,367,48037081$ | $48037081$ |

For example, the degree-three roots at $g=5$ have order $124=4\cdot31$. Removing $31$ leaves order four and $5\equiv1\bmod4$, so their orbit collapses. For a general pair of exponents $E,E'$ in this table, the quotient of the roots has order $m/\gcd(m,E-E')$. A collision at $s$ means that this nontrivial order is a power of $s$. This supplies the test for the last column. Each original root order $g^d-1$ has at least two prime factors, which also gives unit exclusion for every $s$.

Choose $i=1$. For each prime $s$ different from $g_i$ and $\ell$, match compatible towers of primitive $s^a$th roots in the two closures. Primary decomposition extends the match multiplicatively. Kill the $\ell$-primary component and send zero to zero. This is a monoid map injective on the required domain. Take a finite subfield $k_0\subset k$ containing the finitely many transported values and let $G=\mathrm{GL}_8(k_0)\times C_2$, with $\rho$ the projection followed by inclusion. Take $H=\mathrm{GL}_8(k_0)\times\{1\}$. Use as $\tau_v$ the diagonal matrix of transported values, and as $\phi_v$ the permutation matrix of $\sigma_v^{-1}$, both with trivial second component. Then $\rho(\phi_v\tau_v\phi_v^{-1})=\rho(\tau_v)^g$ entrywise and the characteristic identity holds by diagonality. All $\tau_v$ belong to $H$ and $G/H$ is cyclic of order two. This is an algebraic instance of the original criterion. [A2 StatementT.lean:36–52 for the realized interface](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

**Where the result goes.** In both direct consumers the representation is `redF(D,i,ρ)`, combining residue reduction of the given integral representation with the specified embedding into $\overline{\mathbb F}_{D.nd.l(i)}$. Each good signature supplies `IsGood` both for `chiT` and its inverse units. Both calls pass the direct unit family and the polynomials `items₂` at the same signature, with $\tau_v$ the prescribed generator `D.ntypes.tg`. Both project the full-group and restricted conclusions. Disjointness chooses an eligible host for full-group irreducibility. For restriction, the requested host already avoids the residue prime, openness gives the finite quotient, and containment of the relevant inertia groups puts every prescribed tame generator in the subgroup. Both consumers use `not_root_of` separately at the potentially different generator `gam0`, using the two signs from the local transport and the direct and inverse unit conditions. If the signs agree, invert both sides when necessary to reduce to the direct unit. If they differ, move the inverse to the unit side and use that taking prime-to parts commutes with inversion. The alternate branch passes its third-output hypothesis `hk` directly to that exclusion proof. [A2 AdmissibleThreePrime.lean:13–50, DataN.lean:1285–1290, ResidualIrreducibleOfTheoremThreePrime.lean:129–215 and TheoremThreePrimeHolds.lean:12–54](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

The archive conclusion concerns invariant subspaces over the algebraic closure of the residue field. The Galois source group can be infinite. The characteristic polynomial at any one inertia element splits in that field. The original label polynomials live over $\mathbb F_{g_i}$, and `IsGood` concerns divisor degrees across the family. In the rank-eight example the label with degrees three and five is reducible.

**Reading boundary.** Local R3 reaches `restriction_of_blocks_and_jordan`, `t1`, the exports and both direct calls. The permutation supplies have separate reading scopes. [§4.11.1](#4111-why-a-prime-cycle-forces-primitivity-in-small-degree) reads the small-degree primitivity producer used by `JordanTransitive`. [§4.11.2](#4112-why-three-fixed-points-suffice-in-jordans-theorem) reads the prime-cycle containment proof. The local–global production of the transport, the construction of good signatures, and the density and host supplies have their own reading scopes. The first squarefree count is developed in [§4.10.23](#41023-when-prime-to-parts-of-roots-collide). The other squarefree counts and the bad-prime selection enter at the evidence levels recorded in the declaration register. [Open] Kernel replay and independent mathematical review of this section remain separate evidence. [Declaration register](../sources/SOURCES.md#chapter-4-411-inertia-lines-and-goodtuple)

### 4.11.1 Why a prime cycle forces primitivity in small degree

In the singleton branch of §4.11, the quotient acts transitively on the coordinate lines. A single long prime cycle gives more information about that action. It rules out grouping the lines into proper blocks of size greater than one. This is the input used before the separate Jordan theorem. The earlier argument about a given partition uses `BlocksCycle`; here the question is whether the transitive permutation image admits *any* nontrivial block. [A2 Jordan.lean:97–118](../sources/SOURCES.md#chapter-4-4111-prime-cycle-primitivity)

**Two examples [Expository].** On $\{1,2,3\}$ take $S_3$ and $\sigma=(1\,2)$. The orbit of $1$ contains $1,2,3$ via $1,(1\,2),(1\,3)$, and the powers of $\sigma$ send $1$ to $1,2,1$. The support has size $p=2$ and $3<4$. Any proper subset of size at least two is a pair $\{a,b\}$. For the remaining point $c$, the swap $(b\,c)$ sends this pair to $\{a,c\}$. The two pairs intersect at $a$ and differ, so the pair fails to be a block.

On $\{1,2,3,4,5\}$ take $A_5$ and $\sigma=(1\,2\,3)=(1\,3)(1\,2)$, with products applied right to left. This even permutation sends $1$ successively to $2,3,1$ and fixes $4,5$. Here $p=3$ and $5<6$. For any distinct $i,j$, choose $k$ distinct from both. The even permutation $(i\,j\,k)$ sends $i$ to $j$, so the action is transitive. For any subset $B$ of size $2,3$ or $4$, choose $a,b\in B$ distinct and $z\notin B$. The $3$-cycle $(a\,b\,z)$ maps $B$ to $(B\setminus\{a\})\cup\{z\}$. The image differs from $B$ and still contains $b$, so $B$ fails to be a block. In both examples the degree is below $p+3$.

**Definitions.** Let a group $M$ act on a set $Y$ on the left, writing $g y$ for the action and $gB=\{gy:y\in B\}$ for the induced action on subsets. An action is transitive if for all $x,y\in Y$ there exists $g\in M$ with $gx=y$. A block is a subset $B$ such that for every $g\in M$, either $gB=B$ or $gB\cap B=\varnothing$. Equivalently any two distinct translates are disjoint, by applying the inverse of one translating element. A trivial block is a subsingleton (including the empty set) or all of $Y$. A primitive action here is a transitive action in which every block is trivial. This is Mathlib's `IsPreprimitive` convention. A single $p$-cycle moves exactly $p$ points in one cyclic orbit and fixes every other point. [Pinned definitions and cyclic order](../sources/SOURCES.md#chapter-4-4111-prime-cycle-primitivity)

**Lemma (distinct powers in a prime orbit) [Lean, read].** For every group $M$ acting on any set $Y$, every $s\in M$, every prime $p$, and every $y\in Y$, if $s^p=1$ in $M$ and $sy\ne y$, then for all integers $0\le i,j<p$, $s^iy=s^jy$ implies $i=j$.

**Proof.** If $0<d<p$ and $s^dy=y$, the stabilizer of $y$ contains $s^d$ and $s^p$. As $p$ is prime and $0<d<p$, there are integers $u,v$ with $ud+vp=1$. Closure of the stabilizer under products and integer powers then puts $s=(s^d)^u(s^p)^v$ in the stabilizer, contradicting $sy\ne y$. If $i<j<p$ and $s^iy=s^jy$, apply $s^{-i}$ and use $d=j-i$. If $j<i$, interchange $i,j$. This proves the lemma for points and, by taking $Y$ to be a set of subsets, for blocks. [A2 PrimitiveOfPCycle.lean:7–35](../sources/SOURCES.md#chapter-4-4111-prime-cycle-primitivity)

**Theorem (small-degree primitivity) [Lean, read].** For every finite set $\Omega$ of degree $n=|\Omega|$, every subgroup $G\le\operatorname{Sym}(\Omega)$, every $\sigma\in\operatorname{Sym}(\Omega)$ and every natural number $p$, suppose $p$ is prime, $\sigma\in G$, $\sigma$ is one nontrivial cycle with $|\operatorname{supp}(\sigma)|=p$, $n<2p$, and $G$ acts transitively on $\Omega$. Then the action of $G$ on $\Omega$ is primitive.

**Proof.** Suppose $B$ is a nontrivial block. Choose distinct $b,c\in B$ and $z\notin B$. The single cycle $\sigma$ has order $p$ and moves some $x\in\Omega$. Write $s=\sigma$ as an element of $G$, so $s^p=1$ in $G$. By transitivity choose $g$ with $gb=x$ and put $t=g^{-1}sg$. Then $t^p=1$. If $tb=b$, applying $g$ would give $sx=x$, so $tb\ne b$. The block property gives two mutually exclusive cases, since $B$ contains $b$.

1. **$tB=B$.** For $0\le i<p$ every $t^ib$ belongs to $B$, and the lemma says these $p$ points are distinct. Transitivity gives $h\in G$ with $hb=z$. Thus $hB$ contains $z$ and is disjoint from $B$. The points $ht^ib$ for $0\le i<p$ are distinct because $h$ is a bijection, and they belong to $hB$. The two lists together have $2p$ distinct points.
2. **$tB\cap B=\varnothing$.** Now $tB\ne B$. Apply the lemma to the induced action on subsets, with $y=B$. The $p$ translates $t^iB$ for $0\le i<p$ are distinct, hence pairwise disjoint by the block property. Each contains two distinct points $t^ib$ and $t^ic$, since $b\ne c$ and $t^i$ is a bijection. Different indices give points in disjoint translates. This again gives $2p$ distinct points.

In each case the two lists define an injection from the disjoint union of two copies of $\{0,\ldots,p-1\}$ into $\Omega$. It gives $2p\le n$, a contradiction. Therefore every block is trivial. [A2 Statement.lean:154–158 and PrimitiveOfPCycle.lean:37–147](../sources/SOURCES.md#chapter-4-4111-prime-cycle-primitivity)

**Sharpness and deletion of transitivity [Expository].** For every prime $p$ take $\Omega=(\mathbb Z/p\mathbb Z)\times\{0,1\}$. In the imprimitive action of the wreath product $C_p\wr C_2=(C_p\times C_p)\rtimes C_2$, $(a,b)$ translates the first and second fibres by $a$ and $b$, respectively, and the generator of $C_2$ interchanges the two fibres. Independent shifts reach any point within a fibre and the interchange moves between fibres, so the group acts transitively. The shift by $1$ on the first fibre alone is one $p$-cycle, fixing the second fibre pointwise. The two fibres are nontrivial blocks, and $n=2p$. Thus even allowing equality in the degree bound would invalidate the conclusion. To delete only transitivity, instead take $C_p$ generated by a $p$-cycle on $p$ points and fixing one extra point. It has degree $p+1<2p$ for every prime $p$. The support is a proper invariant block of size $p$ and the extra point forms a separate orbit.

**Primitivity, higher transitivity and the Jordan call.** An action is doubly transitive if it is transitive on the ordered pairs of distinct points. In a doubly transitive action a block containing distinct $a,b$ and missing $z$ would be moved by an element taking $(a,b)$ to $(a,z)$, which gives an intersection without equality. The regular action of $C_5$ on $\mathbb Z/5\mathbb Z$ satisfies the theorem with $n=p=5$, hence is primitive. Its point stabilizers are trivial, so the action cannot move $(0,1)$ to $(0,2)$. This group is solvable and has order $5$ while $A_5$ has order $60$. Also, $S_3$ contains $A_3$ and is solvable, since it has an abelian normal subgroup $A_3$ with abelian quotient of order two. Alternating containment yields nonsolvability in the archive through the additional theorem for degrees at least five.

In `jordan_transitivity` let $K$ be the image of the original action group on $\Omega$. An element $g_0$ of the original group maps to $\sigma\in K$, and transitivity passes to $K$ by using the same witnesses. The call at line 108 passes exactly primality, membership, single-cycle status, support size, the strict upper bound, and transitivity of $K$. Its result is `hprim`. The next call uses it with the *additional* inequality $p+3\le n$ to obtain $\operatorname{Alt}(\Omega)\le K$ via `jordanPrime`. The nonsolvability branch calls `noSolvableTransitive`, whose assembly independently invokes the primitive producer after extracting a power from its cycle-type premise. The original group surjects onto $K$, so solvability of the original group would imply solvability of $K$. [§4.11.2](#4112-why-three-fixed-points-suffice-in-jordans-theorem) proves the containment step. The nonsolvability assembly still uses the named supplier `alternating_group_not_solvable`. [A2 NoSolvableTransitive.lean:35–39, NoSolvableOf.lean:5–14 and Jordan.lean:97–118](../sources/SOURCES.md#chapter-4-4111-prime-cycle-primitivity)

Jordan's 1871 result starts with primitivity and a prime cycle and gives $(n-p+1)$-transitivity. His 1873 bound gives alternating containment for an odd prime $p$ in degree $p+k$ with $k>2$ when the action is more than $k$-transitive. In the range $p+3\le n<2p$, $p$ is automatically at least five. The elementary passage from transitivity to primitivity has an explicit antecedent in the block-size argument of Xia's Lemma 4.2. The two point-counting branches above follow Alpöge and Claude's archived proof. Local R3 covers those two proof bodies and their immediate handoff. The restriction and its GoodTuple consumers are covered in §4.11. A declaration path from the `riemannHypothesis` export reaches both proof bodies through the alternate ThreePrime consumer. The source register records the path and the status of kernel replay and independent review. [Primary references and reading ledger](../sources/SOURCES.md#chapter-4-4111-prime-cycle-primitivity)

### 4.11.2 Why three fixed points suffice in Jordan's theorem

In the singleton branch of §4.11, the solvable quotient acts on the coordinate lines through a permutation image. [§4.11.1](#4111-why-a-prime-cycle-forces-primitivity-in-small-degree) gives primitivity in strict small degree. To use the contradiction with solvability, we still need a subgroup large enough to contain all even permutations. In the archived proof, a single prime cycle produces a new permutation that moves just three of its fixed points. [Source register](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

**Two examples [Expository].** Write products as functions, so $(xy)(d)=x(y(d))$ and $(a\,b\,c)$ sends $a$ to $b$ to $c$ to $a$. If $a,b,c$ are fixed by a cycle $g$, the two swaps $(a\,b)$ and $(a\,c)$ have commutator $(a\,b\,c)$. To use this observation inside $G$, we need elements of $G$ that act like those swaps on the fixed points. For example, take $G=A_8$, $g=(0\,1\,2\,3\,4)$, and fixed points $5,6,7$. The swaps of these fixed points are odd. They admit even extensions by acting on $\{0,1,2,3,4\}$ at the same time. The extensions can leave an extra 5-cycle in the commutator, as the calculation below shows. For $G=S_5$ and $g=(0\,1)$, the fixed points are $2,3,4$, and the action of any extension on $\{0,1\}$ lies in a group of order two. Its contribution to the commutator is the identity.

**Definitions.** Let $\alpha$ be a finite set, $G\le \operatorname{Sym}(\alpha)$, $S=\operatorname{supp}(g)=\{d:g(d)\ne d\}$ and $\Gamma=\alpha\setminus S$. A primitive action is transitive and has only subsingleton or full blocks. The pointwise stabilizer $G_{(\Gamma)}$ consists of the elements of $G$ fixing each point of $\Gamma$. A group is $r$-transitive if it acts transitively on ordered $r$-tuples of distinct points, equivalently on injections from an $r$-element index set. In the degrees used here, $r$-primitivity means $r$-transitivity together with primitivity of the pointwise stabilizer of each $(r-1)$-element subset on its complement.

**Theorem (Jordan's prime-cycle theorem) [Lean, read].** For every finite $\alpha$, $G\le\operatorname{Sym}(\alpha)$, $g\in\operatorname{Sym}(\alpha)$ and $p\in\mathbb N$, suppose $p$ is prime, $g\in G$, $g$ is a single nontrivial cycle, $|S|=p$, $p+3\le|\alpha|$, and $G$ acts primitively on $\alpha$. Then $\operatorname{Alt}(\alpha)\le G$. [A2 Statement.lean:160–164 and JordanPrime.lean:188–284](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

**Proof.** Put $k=|\Gamma|$. Then $|\alpha|=p+k$ and $k\ge3$. The powers of $g$ belong to $G_{(\Gamma)}$ and act transitively on $S$. This action is primitive because its degree is prime: the translates of a nonempty block partition the transitive set into blocks of equal size, so the block size divides $p$. Apply Mathlib's `IsPreprimitive.isMultiplyPreprimitive` with $s=\Gamma$ and parameter $k-1$. The needed inequality is $k+1<|\alpha|$, which follows from $p\ge2$. We obtain $(k+1)$-primitivity, hence $(k+1)$-transitivity and then $k$-transitivity by restricting tuples. Enumerate $\Gamma$ as an injection $i\mapsto\gamma_i$. For any permutation $\pi$ of $\alpha$, $k$-transitivity sends the tuple $(\gamma_i)_i$ to $(\pi(\gamma_i))_i$, giving an element of $G$ that agrees with $\pi$ on every fixed point. [Pinned Mathlib lifting and A2 JordanPrime.lean:90–108,191–219](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

The lift itself starts by proving double primitivity. If a pointwise stabilizer fixes a set $T$ of more than one point and is primitive on $T^c$, primitivity of $G$ supplies a translate $hT$ for which $T\cap hT$ is nonempty and proper in $T$, while $T\cup hT$ misses a point. The proof chooses the translate by separating two points of $T$ when $2|T|<|\alpha|$, and two points of $T^c$ otherwise. The stabilizers of $T$ and $hT$ act on overlapping complements, so the stabilizer of their intersection is transitive there. Since $T^c$ is more than half of the new complement, a proper block meets $T^c$ in at most one point and must be a singleton. Induction shrinks to the stabilizer of one point. Double primitivity permits the outer induction to remove one fixed point at a time, using the action of a point stabilizer on the remaining points. [Pinned Mathlib lifting proof](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

**Sylow adjustment.** Let $\pi$ preserve $\Gamma$ and satisfy $\pi^2=1$. Choose an agreeing extension $x_0\in G$ as above. Its inverse agrees with $\pi$ on $\Gamma$ too, since $x_0(\pi(\gamma))=\pi^2(\gamma)=\gamma$. Put $F=G_{(\Gamma)}$. Restriction embeds $F$ into $\operatorname{Sym}(S)$, since an element of $F$ already fixes the complement pointwise. Thus $|F|\mid p!$. Both $g$ and $x_0 g x_0^{-1}$ belong to $F$. The second fixes every $\gamma\in\Gamma$ because $x_0^{-1}(\gamma)\in\Gamma$. Both have order $p$. The factor $p$ occurs exactly once in $p!$, so the two order-$p$ cyclic subgroups are Sylow $p$-subgroups of $F$. Conjugate the second subgroup to the first by an $f\in F$. Then $x=f x_0$ belongs to $G$ and $x g x^{-1}=g^u$ for some integer $u$. Left multiplication by $f$ preserves the action of $x_0$ on $\Gamma$, because $x_0(\Gamma)=\Gamma$ and $f$ fixes $\Gamma$ pointwise. Both $x$ and $x^{-1}$ therefore agree with $\pi$ there. [A2 JordanPrime.lean:110–184,223–237](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

**The commutator and cancellation.** Choose distinct $a,b,c\in\Gamma$. Apply the adjustment to $\pi=(a\,b)$ and $\pi=(a\,c)$ to get $x,y\in G$ and exponents $u,w$ with $xgx^{-1}=g^u$ and $ygy^{-1}=g^w$. These conjugations act on $\langle g\rangle$ by raising to powers. To see the archive's exponent argument, if $xgx^{-1}=g^u$, conjugation by $x^m$ sends $g$ to $g^{u^m}$ for $m\ge0$, by induction using the fact that conjugation commutes with integer powers. Since $x$ has finite order, $x^{-1}=x^{\operatorname{ord}(x)-1}$, so the inverse conjugation is also a power map, say with exponent $v$. Likewise write $v'$ for the inverse exponent for $y$. We have $g^{uv}=g$ and $g^{wv'}=g$. For $z=xyx^{-1}y^{-1}\in G$, conjugation sends $g$ to $g^{u w v v'}=g^{(uv)(wv')}=g$. Thus $z$ commutes with $g$.

Pick $d_0\in S$. Commutation and injectivity imply $z(d_0)\in S$, so $z(d_0)=g^j(d_0)$ for some integer $j$. Every $d\in S$ is $g^i(d_0)$ for some integer $i$. Then
$$
z(d)=g^i z(d_0)=g^{i+j}(d_0)=g^j(d).
$$
On $\Gamma$ the four factors of $z$, read from right to left, act as $(a\,c),(a\,b),(a\,c),(a\,b)$. With $t=(a\,b)(a\,c)=(a\,c\,b)$, this is $t^2=t^{-1}=(a\,b\,c)$. On $S$, left multiplication by $g^{-j}$ cancels $z$. On $\Gamma$ that power acts trivially. Consequently $g^{-j}z=t^{-1}$ on all of $\alpha$. Both factors on the left belong to $G$, giving an actual 3-cycle in the original group. Three fixed points supply the common point and the two distinct partners. If there are more fixed points, tuple agreement controls all of them, and the two prescribed swaps fix the extras. [A2 JordanPrime.lean:11–88,220–285](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

**The final Mathlib call.** The archive hands the original primitivity proof, the 3-cycle $t^{-1}$ and its membership to `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`. In our degree $n=|\alpha|\ge5$, that lemma applies the same lifting theorem to the complement of the three moved points. The pointwise stabilizer acts primitively on those three points by the prime-degree argument. The lift gives $(n-2)$-primitivity and then $(n-2)$-transitivity. The orbit of an ordered $(n-2)$-tuple has size $n!/2$, so the index of $G$ in the symmetric group is at most two. Mathlib's index lemma identifies the subgroup of index two with the alternating group and the subgroup of index one with the symmetric group. This proves the desired inclusion. [Pinned Mathlib containment proof](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

A separate Mathlib lemma, `closure_three_cycles_eq_alternating`, expresses the familiar generation argument. Even permutations are products of an even number of swaps. Pair successive swaps. Identical swaps cancel, two swaps with one common point give a 3-cycle, and disjoint swaps satisfy $(a\,b)(c\,d)=(a\,c\,b)(a\,c\,d)$. All 3-cycles are even, so their generated subgroup is exactly the alternating group. The archived final call uses the index proof above. [Pinned Mathlib generation proof](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

**The two calculations in full [Expository].** For $A_8$ use addition modulo five on $S=\{0,1,2,3,4\}$, with $g:s\mapsto s+1$ there. Put $D:s\mapsto 2s$, the odd 4-cycle $(1\,2\,4\,3)$ on $S$, extended by the identity on $\Gamma=\{5,6,7\}$. Take $f=(0\,1\,2)$, $h=(2\,3\,4)$ and choose the initial extensions
$$
x_0=f^{-1}D(5\,6),\qquad y_0=h^{-1}gD(5\,7).
$$
They are even, as are $f$ and $h$. The pointwise stabilizer of $\Gamma$ is $A_5$ on $S$, of order $60$. Conjugating $g$ by $x_0$ or $y_0$ gives $f^{-1}g^2f=(0\,3\,2\,1\,4)$ or $h^{-1}g^2h=(0\,4\,3\,1\,2)$ respectively. Neither is a power of $g$: the first sends $0$ to $3$ but $3$ to $2$, and the second sends $0$ to $4$ but $4$ to $3$ and $3$ to $1$. The adjustments $f,h\in F$ send both to $g^2$. On $S$ the adjusted $x$ and $y$ act as $s\mapsto 2s$ and $s\mapsto 2s+1$. The four applications for $z=xyx^{-1}y^{-1}$ are
$$
s\longmapsto 3(s-1)\longmapsto 4(s-1)
 \longmapsto 3s+3\longmapsto s+1\pmod 5 .
$$
Thus $z=g(5\,6\,7)$, $j=1$, and $g^{-1}z=(5\,6\,7)$. The action of $A_8$ is doubly transitive: any permutation matching two ordered points can have its sign corrected by a swap of two unused target points. Hence it is primitive, because an element taking $(a,b)$ to $(a,c)$ with $a,b$ in a proposed proper block and $c$ outside violates the block condition. Here $p=5$ and $n=8$.

For $S_5$ let $g=(0\,1)$, so $p=2$, $n=5$ and $\Gamma=\{2,3,4\}$. The group is doubly transitive by extension of bijections of pairs, hence primitive by the same block argument. Take $x_0=g(2\,3)$ and $y_0=(2\,4)$. The pointwise stabilizer is $F=\{1,g\}$ and both conjugates of $g$ are $g$. Choose $f=h=g$, giving $x=(2\,3)$ and $y=g(2\,4)$ with both conjugation exponents equal to one. The two support contributions of $g$ cancel in $xyx^{-1}y^{-1}$, and on $\Gamma$ the product is $(2\,3)(2\,4)(2\,3)(2\,4)=(2\,3\,4)$. Here $j=0$. This example uses the degree bound at equality and the same archive argument for the even prime.

**Deleting hypotheses [Expository].** To delete primitivity even with transitivity retained, let $C_3\wr C_2$ act on two fibres of size three by independent cyclic shifts and a fibre interchange, as in §4.11.1. A shift of just the first fibre is a single 3-cycle with three fixed points. The fibres are blocks and the group has order $18$, smaller than $|A_6|=360$.

To delete only the fixed-point bound, use $\operatorname{PGL}_2(\mathbb F_8)$ acting on $\mathbb P^1(\mathbb F_8)=\mathbb F_8\cup\{\infty\}$. A fractional linear map sends any ordered pair of distinct points to $(0,\infty)$: in the finite case use $(x-a)/(x-b)$ for the pair $(a,b)$, and for a pair involving $\infty$ use $x-a$ or $1/(x-b)$ as appropriate. Thus the action is doubly transitive and primitive. The permutation $x\mapsto\lambda x$ with $\lambda=X\bmod(X^3+X+1)\in\mathbb F_8^\times$ is a single 7-cycle on the nonzero field elements, because the multiplicative group has prime order seven. The polynomial $X^3+X+1$ has no root in $\mathbb F_2$ and is therefore irreducible. In the binary polynomial encoding, the orbit of $1$ has labels $1,2,4,3,6,7,5,1$. The permutation fixes exactly $0$ and $\infty$. The projective group has order $(8^2-1)(8^2-8)/(8-1)=504$, computed by choosing two independent columns and dividing by the scalar matrices. The action is faithful since fixing $\infty,0,1$ forces a scalar matrix. Its order is smaller than $|A_9|=181440$. This shows that even a two-fixed-point bound is insufficient in general.

For $p=2$ primitivity alone already suffices. Form the graph whose edges are the supports of the $G$-conjugates of the transposition. The components form a $G$-invariant partition, and one contains an edge. Primitivity forces the graph to be connected. Edge transpositions of a connected graph generate the symmetric group: given the transposition from the starting vertex to a vertex on a simple path, conjugate it by the swap along the next edge to obtain the transposition to the next vertex. Hence all transpositions lie in $G$. Deleting the fixed-point bound has no counterexample at this prime. [Pinned Mathlib transposition theorem](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

**Historical attribution [Paper].** In 1871 Jordan states that a primitive group containing a prime cycle with $k$ fixed points is at least $(k+1)$-transitive (p. 383, §1, with the cyclic case also on p. 384, Theorem I). In the 1872–1873 volume of the *Bulletin de la Société Mathématique de France*, Theorem I on pp. 42–43 deduces alternating containment for degree $p+k$, odd prime $p$, $k>2$, and more than $k$-transitivity. Jordan's argument there uses Sylow normalizers and constructs a three-letter cycle. The two historical results compose for odd $p$. The transposition argument above handles $p=2$. Jones states the full prime-cycle result as Theorem 1.1, and his §3 gives this attribution. The proof in this section follows Alpöge and Claude's archive and its pinned Mathlib supplies. [Primary texts and modern statement](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)

**Return to the coordinate lines.** In `jordan_transitivity` the original acting group maps onto its permutation image $K$ on $\Omega$. For the direct containment conclusion, line 108 derives primitivity of $K$ using §4.11.1 and $|\Omega|<2p$. Line 110 applies `jordanPrime` to that same $K$ and the same induced cycle, now with $p+3\le|\Omega|$. For the second conclusion, line 116 supplies cycle-type membership to `noSolvableTransitive`. That declaration assembles the power extraction, small-degree primitivity, the present theorem, and the named input `alternating_group_not_solvable` in degree at least five. It uses the extracted power inside $K$. A solvable original group would have a solvable image $K$, contradicting this output. It is this nonsolvability output that §4.11 uses on the solvable quotient acting on the coordinate lines. The restriction and GoodTuple criteria retain their other hypotheses. Local source reading, declaration-level reachability, kernel replay and review are recorded separately. [Consumers and evidence](../sources/SOURCES.md#chapter-4-4112-jordans-prime-cycle-theorem)
