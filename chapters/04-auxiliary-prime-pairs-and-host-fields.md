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
by us (`R3` / `[Lean, read]`); the classical analytic sub-packages imported at the bottom of the
sieve (a width-$1/400$ zero-density count, the prime number theorem in progressions modulo
divisible-by-$8$ moduli, Siegel's lower bound, and a Perron contour tail) were read at statement
level (`R2` / `[Lean]`), and we distinguish the two tags explicitly throughout.

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
  `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`) [Lean],
  among all primitive characters of conductor $\le Q$, at most $O(Q^{1/4})$ can have a zero in the
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

In the window predicate `WinPair` (`ExistsPageN.lean:27`), the archive enforces $(\frac{-d}{p}) = +1$
simultaneously for $p = q$ and for all small odd primes $p$ by the single clean divisibility
requirement $p \mid d + 1$ (`jac_neg_of_dvd`, `PairHyp.lean:5`) [Lean, read]: if $p \mid d + 1$,
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
     (`ExistsPageN.lean:24–25`):
     $$a \in H_E \iff a \equiv \pm 1 \pmod{16},\quad \psi(a) = 1,\quad
     \Bigl(\frac{a}{11}\Bigr) = 1,\quad \Bigl(\frac{a}{263}\Bigr) = 1.$$
     At $a = -1$, $(\frac{-1}{11}) = -1 \neq 1$ and $(\frac{-1}{263}) = -1 \neq 1$, so **$-1 \notin H_E$**,
     even if $\psi$ had been the trivial character $\psi = 1$! Better still, the product character
     $\psi^\flat(a) = \psi(a)(\frac{a}{11})$ satisfies $\psi^\flat(-1) = (-1)(-1) = +1$, so
     $E = F(\sqrt{-263})$ is a **CM extension** of the totally real field
     $$F = F_1\bigl(\sqrt{33}\bigr) = \mathbb Q(\zeta_{16})^+\bigl(\sqrt{(-3)(-11)}\bigr),$$
     with $\operatorname{Gal}(E/\mathbb Q) \cong (\{\pm 1\} \times \{\pm 1\}) \times \mathbb Z/4\mathbb Z$
     and complex conjugation acting as $((-1, -1), 1)$: trivial on $F$, negating $\sqrt{-263}$! And
     inside the character group of $\operatorname{Gal}(E/\mathbb Q)$, multiplying $\psi^\flat$ back
     by the host sign character $(\frac{\cdot}{11})$ recovers our original odd target character
     $\psi$!

### 4.2.2 Why $1/400$, $401$, $\lambda = 3/2$, and $\varepsilon < 1/52$?

A reader inspecting the Lean files encounters four concrete rational numbers: box width $1/400$,
Tate–Shafarevich exponent $401$, window exponent $3/2$, and $\varepsilon < 1/52$. Every one of them
comes from a two-line calculation we can verify on the back of an envelope [Lean, read]:

1. **Why width $1/400$ matches truncation $Z = x^{400}$ (`TailKExp.lean:23–28`).** To bound
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
   (`Kappa4Loglog.lean:9–25, 126–154`).** Apply that same zero-free box of width $1/400$ at a tiny auxiliary
   parameter $x_0 = (\log Q)^{10/4}$ (`s = (\log Q)^{1/4}`, `x = s^{10}`, `Kappa4Loglog.lean:10, 56`) [Lean, read].
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
   at `Kappa4Loglog.lean:135`), yielding $\lvert \frac{L'}{L}(1,\chi) \rvert \le 4\log Y$ cleanly!
   (A second place also uses $\varepsilon < 1/52$: in `EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5`,
   bounding all growth exponents using $\varepsilon < 1/52 < 0.02$ makes the Hodge–Tate/Selmer twist
   cutoff satisfy $R.t \le 10708\,x^{399.67} \le \lfloor x^{400} \rfloor$ for large $x$ [Lean, read].)
3. **Why $401 = 1 + 400$ and $\lambda = 3/2$ (`WinPairs.lean:40–81`).** The global Tate–Shafarevich
   theorem `VWin` (`ExistsPageN.lean:49`) is proved on **quadratic** windows $x' \in [W, W^2]$ at
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
   character $\chi \bmod N$, `ZeroBox H χ` (`PairGood.lean:12`, identical on $H = Q$ to
   `ZeroFreeBox Q χ` at `src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:44`)
   holds if for every $s \in \mathbb C$ [Lean, read]:
   $$1 - \frac{1}{400} < \Re s \quad\text{and}\quad \lvert \Im s \rvert \le H
   \implies L(s, \chi) \neq 0.$$
   For $(i, j) \in \{0, 1\}^2$, the box height assigned to $(q, d, i, j)$ is (`height`,
   `PairGood.lean:15`) [Lean, read]:
   $$\mathrm{height}(q, d, i, j) := \begin{cases} d & \text{if } j \neq 0,\\ q & \text{if } j = 0.\end{cases}$$
3. **Analytically good prime pair (`PairGood` and `PairEx`, `src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:18,28`).**
   Given $M \ge 1$ and reals $\varepsilon, Y, X$, a pair $(q, d)$ satisfies `PairGood M eps Y X q d`
   if `WinPair eps Y q d` holds, $\gcd(M, qd) = 1$, and for every $\chi_0 \bmod M$, every
   $(i, j) \in \{0, 1\}^2$ with $(i \neq 0 \lor j \neq 0)$, and every primitive character
   $\chi \bmod N$ (`[NeZero N]`) satisfying `An.Induces χ (tw χ₀ q d i j) (2 * M * q * d)` [Lean, read]:
   - **(`box`)** `ZeroBox (height q d i j) χ` holds; and
   - **(`bounds`)** for every real $x \in [Y, X]$,
     $$\lvert G_\chi(x) \rvert \le x^{1/2 + \varepsilon/2}
     \qquad\text{and}\qquad
     \Bigl\lvert \frac{L'}{L}(1, \chi) \Bigr\rvert \le 4 \log x,$$
     where $G_\chi = \mathrm{An.gChi}\,\chi$ is the normalized Riesz prime sum of Chapter 3
     (Definition 3.1).
   The global existence proposition `PairEx : Prop` (`PairGood.lean:28`) asserts that for every
   $M \ge 1$, every $0 < \varepsilon < 1/52$, and every $A \ge 1$, there exists $Y_0$ such that
   for every $Y \ge Y_0$, there exist $q, d \in \mathbb N$ satisfying `PairGood M eps Y (Y^A) q d`
   [Lean, read].

### 4.3.2 Classical sieve inputs (`ZeroDensityBox`, `MeanSq`, and arithmetic progressions)

Inside `MeanSquareBounds/` and `GL3MeanSquares/`, the two-stage sieve operates on prime sets in
arithmetic progressions modulo a multiple of $8$: for $m_0, a_0 \in \mathbb N$ and $U \in \mathbb R$,
$$\mathrm{PPset}(m_0, a_0, U) := \bigl\{q \in [1, \lfloor U \rfloor] : q\text{ prime},\ q > U^{1/2},\ q \equiv a_0 \pmod{m_0}\bigr\}$$
(`PPset`, `src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:50`) [Lean, read].
Notice the dyadic lower bound $q > U^{1/2}$, which means $\frac{1}{2}\log U < \log q \le \log U$.

**Definition 4.3 (Zero-density and mean-square interfaces).**

1. **Zero-density bound in boxes of width $1/400$ (`ZeroDensityBox`, `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean:7`).**
   `ZeroDensityBox : Prop` asserts that there exists a constant $C > 0$ such that for every real
   $Q \ge 2$, the finite set of pairs $(N, \chi)$ with $1 \le N \le \lfloor Q \rfloor$, $\chi \bmod N$
   primitive, and $\neg\mathrm{ZeroFreeBox}(Q, \chi)$ has cardinality at most $C\,Q^{1/4}$ [Lean, read].
   (Its proof term `zero_density_box : ZeroDensityBox` lives at `…/CountZAll.lean:13` [Lean].)
2. **Truncated Riesz prime sum and $L^2$ family hypothesis (`QH.S` and `QH.MeanSq`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:13,26`).**
   For an arithmetic weight $\kappa : \mathbb N \to \mathbb C$ with $\lvert \kappa(n) \rvert \le 1$,
   truncation $Z \in \mathbb R$, scale $y \in \mathbb R$, and integer $q \in \mathbb N$, define the
   truncated Jacobi-twisted prime sum [Lean, read]
   $$S(Z, y, q, \kappa) := \sum_{1 \le n \le \lfloor Z \rfloor} \frac{\Lambda(n)}{y}\,\min(n, y)\,\kappa(n)\,\Bigl(\frac{n}{q}\Bigr)
   = \sum_{1 \le n \le \lfloor Z \rfloor} \frac{\Lambda(n)}{n}\,\min\Bigl(1, \frac{n}{y}\Bigr)\,\kappa(n)\,\Bigl(\frac{n}{q}\Bigr).$$
   Observe the exact algebraic identity linking $\frac{\Lambda(n)}{y}\min(n, y)$ to the Riesz ramp
   $(y/n - 1)_+$: for $n \le y$ we have $\frac{y}{n} - (\frac{y}{n} - 1)_+ = 1 = \frac{\min(n, y)}{n} \cdot \frac{y}{n}$,
   and for $n > y$ we have $\frac{y}{n} - (\frac{y}{n} - 1)_+ = \frac{y}{n}$. Dividing by $y$ gives
   $\frac{1}{y}\min(n, y) = \frac{1}{n} - \frac{1}{y}(\frac{y}{n} - 1)_+$ for every $n \ge 1$, so
   multiplying $S(Z, y, q, \kappa)$ by $y$ yields
   $$y\,S(Z, y, q, \kappa) - y\sum_{1 \le n \le \lfloor Z \rfloor} \frac{\Lambda(n)\kappa(n)(\frac{n}{q})}{n}
   = -\sum_{1 \le n \le \lfloor y \rfloor} \Lambda(n)\Bigl(\frac{y}{n} - 1\Bigr)\kappa(n)\Bigl(\frac{n}{q}\Bigr)$$
   (`BoxOfS.lean:45–52`) [Lean, read]! That algebraic identity is why bounding $\lvert S(Z, y, q, \kappa) \rvert \le \frac{1}{2}y^{-1/2 + \varepsilon/2}$
   (multiplied by $y$) bounds the Riesz prime sum by $\frac{1}{2} y^{1/2 + \varepsilon/2}$! The
   proposition `MeanSq m₀ a₀ U Z y` (`PrimeSetTwoBounds.lean:26`) states that for every $\kappa : \mathbb N \to \mathbb C$
   with $\lVert \kappa(n) \rVert \le 1$ (`n ≥ 1`),
   $$\sum_{q \in \mathrm{PPset}(m_0, a_0, U)} \bigl\lVert S(Z, y, q, \kappa) \bigr\rVert^2
   \le \frac{64\,\log y}{y}\,\bigl\lvert \mathrm{PPset}(m_0, a_0, U) \bigr\rvert$$
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
   (`ExistsPageN.lean:49`) [Lean, read].

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
   and inline in `supplyOfAdmOf.lean:88–94`.)* [Lean, read]

*Proof.*

1. For each real $x \ge 1$, set $y := x^{2 + 8\varepsilon} \ge 1$ (since $2 + 8\varepsilon > 0$), and
   choose the minimal $k \in \mathbb N$ with $y \le 2^k$ (`ExistsPageN.lean:69–80`). For $y = 1$,
   $k = 0$ satisfies $1 \le 2^0 \le 2$; for $y > 1$, minimality gives $k \ge 1$ and $2^{k-1} < y \le 2^k$,
   hence $y \le 2^k < 2y$. Setting $e(x) := k$ gives $x^{2 + 8\varepsilon} \le 2^{e(x)} \le 2\,x^{2 + 8\varepsilon}$.
2. Let $(q, d)$ satisfy `WinPair eps Y q d`. By definition $q$ is prime with $q \equiv 3 \pmod 8$
   and $d$ is prime with $d \equiv 7 \pmod{16}$. For any odd prime $p$ dividing $d + 1$ (which
   includes both $p = q$, by `d_q`, and every odd prime $p \le Y^{\varepsilon/5}$, by `d_small`),
   we have $d + 1 \equiv 0 \pmod p$, so $-d \equiv 1 \pmod p$. Since $p$ is odd,
   $$\Bigl(\frac{-d}{p}\Bigr) = \Bigl(\frac{1}{p}\Bigr) = 1$$
   (`jac_neg_of_dvd`, `PairHyp.lean:5`). Taking $p = q$ gives `HostHyp q d`. Next, since
   $q \equiv 3 \pmod 8 \implies q \equiv 3 \pmod 4$ and $d \equiv 7 \pmod{16} \implies d \equiv 3 \pmod 4$,
   we have $q \neq d$ (they are incongruent modulo $8$) and $(\frac{-1}{q}) = (\frac{-1}{d}) = -1$.
   By quadratic reciprocity for distinct odd primes $q \equiv d \equiv 3 \pmod 4$,
   $$\Bigl(\frac{-q}{d}\Bigr) = -\Bigl(\frac{q}{d}\Bigr) = \Bigl(\frac{d}{q}\Bigr)
   = -\Bigl(\frac{-d}{q}\Bigr) = -1$$
   (`jac_neg_recip`, `PairHyp.lean:15`). Finally, if $Y^{\varepsilon/5} \ge 4$ (`4 * ψ.N ≤ b` in
   `supplyOfAdmOf.lean:45,88–94`), then $\log q > \frac{1}{2} Y^{\varepsilon/5} \ge 2$, so
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
   and `…/HostFacts.lean:254`; `UpperTheory.Top.isChiField`, `src/Development/AutomorphicArithmetic/CharacterBoxes/IsChiField.lean:5`.)* [Lean, read]
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
   of order $2$. By the defining axiom `gal_spec` of `HostRaw` (`ConjEMemHostFIff.lean:45`), under
   the cyclotomic embedding $\iota : E \hookrightarrow \mathbb C$, $\iota \circ \mathrm{gal}^{-1}(\mathrm{cc})$
   acts as complex conjugation on $\mathbb C$. Since $\sqrt{-d} \neq 0$ satisfies $(\sqrt{-d})^2 = -d < 0$,
   its image in $\mathbb C$ is purely imaginary, so $\mathrm{conj}(\sqrt{-d}) = -\sqrt{-d} \neq \sqrt{-d}$
   (`HostFacts.lean:254`). Every complex embedding of $F = E^{\langle\mathrm{conj}\rangle}$ commutes
   with $\operatorname{Gal}(E/\mathbb Q)$ (as $E/\mathbb Q$ is abelian!), so complex conjugation
   restricts to the identity under *every* complex embedding of $F$ (making $F$ totally real) and is
   nontrivial under *every* complex embedding of $E$ (making $E$ totally imaginary, hence CM over
   $F$, with $[E : \mathbb Q] = \lvert \varphi.\mathrm{GG} \rvert = 4\,\varphi.\mathrm{ord}$ and
   $[F : \mathbb Q] = 2\,\varphi.\mathrm{ord}$). Finally, if `KerChi ψ H` holds and $\tau(\zeta_{\mathrm{condN}}) = \zeta_{\mathrm{condN}}^a$,
   preserving primitive roots forces $\gcd(a, \mathrm{condN}) = 1$; by `art_spec`, $\tau$ fixes
   $\iota(E)$ if and only if $H.\mathrm{art}(a) = 1$, which `KerChi` equates to the four conditions
   of `IsChiField` (`IsChiField.lean:22–51`).
2. Recall from `Analytic.lean:92–94, 136` that among characters $\theta \in \widehat{\varphi.\mathrm{GG}}$
   trivial on the cyclic subgroup $A_0 \le A$, the plus-space $X_p$ consists of those with
   $\theta(\mathrm{iod}) = +1$, the minus-space $X_m$ consists of those with $\theta(\mathrm{iod}) = -1$,
   and `Bounded` is $(X_p \setminus \mathrm{Kept}) \cup X_m$. By `TwistForm ψ H`, there exist
   $\xi \in \langle \psi.\chi \rangle$ and $(i, j) \in \{0, 1\}^2$ such that $\theta(\mathrm{iod}) = (-1)^j$
   and $\theta(H.\mathrm{art}(a)) = \mathrm{tw}(\xi, q, d, i, j)(a)$ for all $\gcd(a, \mathrm{condN}) = 1$.
   Suppose for a contradiction that $(i, j) = (0, 0)$ (`BoundedTw.lean:19–32`). Then:
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
$C_{\mathrm{ZD}} > 0$. Let $F \ge 1$ and $U, Q \ge 2$ with $F < U^{1/2}$ and $FU \le Q$, and let
$(f_r, \xi_r)_{r \in I}$ be a family of at most $R + 1$ primitive characters with $1 \le f_r \le F$.
Suppose that for each $r \in I$ and each prime $q \in \mathrm{PPset}(m_0, a_0, U)$, we are given a
primitive character $\psi_{r, q}$ of conductor $f_r q$ (namely $\xi_r$ twisted by the primitive
quadratic character of prime conductor $q$, which is primitive because $q > U^{1/2} > F \ge f_r$ so
$\gcd(f_r, q) = 1$). Then the set of "zero-bad" primes*
$$B_1 := \bigl\{q \in \mathrm{PPset}(m_0, a_0, U) : \exists r \in I,\ \neg\mathrm{ZeroFreeBox}(Q, \psi_{r, q})\bigr\}$$
*has cardinality*
$$\lvert B_1 \rvert \le C_{\mathrm{ZD}}\,Q^{1/4}.$$
*(Lean: `QH.count_bad_core` and `QH.count_bad`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/CountBadCore.lean:18`
and `…/CountBad.lean:9`, invoking `zero_density_box` [Lean] at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`.)* [Lean, read]

*Proof.* Notice something even sharper than a naive $(R + 1)\,C_{\mathrm{ZD}}\,Q^{1/4}$ union bound:
the factor $R + 1$ **disappears completely** (`CountBadCore.lean:34–59`)! Why? For each $q \in B_1$,
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

*(Remark on `zero_density_box` [Lean].)* In the archive, `zero_density_box` (`CountZAll.lean:13`)
is proved unconditionally inside nine files of `JacobiCharacterSums/` (`CountAll.lean`, `CountRect.lean`,
`CountLargeT.lean`, `CountMedT.lean`, `CountLowT.lean`, `LargeSieveDuality.lean`, `MollifierDetect.lean`,
`DirichletPolyMean.lean`, `ZeroFreeWidth.lean`, import cone $\approx 250$ modules) by classical
Montgomery–Bombieri large-sieve duality and mollifier zero-detection; since we did not read those
nine internal proof files line by line, `zero_density_box` itself carries `[Lean]` (`R2`), while
the reduction `count_bad_core` / `count_bad` above is `[Lean, read]` (`R3`).

### 4.4.3 Splitting $G_\chi(y)$ at $Z = (Y^K)^{400}$ (`box_of_S`, `tailK`, `kappa4`)

Once $q \notin B_1$, every twist $\chi = \psi_{r, q}$ has no zeros in $\mathcal B(Q)$. The next two
lemmas show that inside $q \notin B_1$, bounding $G_\chi(y)$ and $\frac{L'}{L}(1,\chi)$ reduces
completely to bounding the finite Jacobi-twisted sum $S(Z, y, q, \kappa)$ at $Z = (Y^K)^{400}$.

**Lemma 4.4 (Explicit-formula tail and logarithmic-derivative bound from `ZeroFreeBox`).** *Let
$0 < \varepsilon < 1/52$ and $K \ge 1$.*

1. **(`QH.tailK`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/TailKExp.lean:92`, using
   `box_tail_bound` [Lean] at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailFinal.lean:13`.)**
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
   *Set $Z := (Y^K)^{400}$, and suppose $\chi(n) = \kappa(n)\,(\frac{n}{q})$ for all $n \ge 1$ not
   dividing $2Mqd$ (`GoodC κ q χ`, `PrimeSetTwoBounds.lean:32`). If $Y$ is large enough that
   $Y^\varepsilon + 2\log Y \le \frac{1}{2} Y^{1/2 + \varepsilon/2}$, and if
   $\lvert S(Z, y, q, \kappa) \rvert \le \frac{1}{2} y^{-1/2 + \varepsilon/2}$ for all
   $y \in [Y, Y^K]$, then under `ZeroFreeBox Q χ` we have*
   $$\lvert G_\chi(y) \rvert \le y^{1/2 + \varepsilon/2} \quad \forall y \in [Y, Y^K],
   \qquad\text{and}\qquad
   \Bigl\lvert \frac{L'}{L}(1, \chi) \Bigr\rvert \le 4 \log Y.$$
   [Lean, read]

*Proof.*

1. Set $x := Y^K$ and $Z := x^{400}$, with finite-difference step $\eta := x^{-2}$ (`TailFinal.lean:31–32`).
   Using the difference identity $\eta Z \cdot \mathrm{tailL}_\chi(Z) = -(S_\chi(Z + \eta Z) - S_\chi(Z) + \eta Z \frac{L'}{L}(1,\chi)) + (S_\chi(Z + \eta Z) - S_\chi(Z) - \eta Z \sum_{n \le Z} \frac{\Lambda(n)\chi(n)}{n})$,
   the contour estimate `tail_contour` (`TailFinal.lean:15` [Lean]) on $\mathcal B(Q)$ bounds the
   first term by $K_0 (\log Q)\bigl((\log Q)\eta Z^{1 - 1/400 + \varepsilon/(1600K)} + Z^2 / Q\bigr)$,
   while Mertens's bound controls the short sum over $(Z, Z + \eta Z]$. Dividing by $\eta Z$ and
   multiplying by $x = Y^K$ (`tailK_num`, `TailKExp.lean:23–89`), watch each of the three pieces:
   - The zero-free boundary term has size
     $$K_0 (\log Q)^2 \cdot x \cdot Z^{-1/400 + \varepsilon/(1600K)}
     = K_0 (\log Q)^2 \cdot x \cdot x^{-1 + \varepsilon/(4K)}
     = K_0 (\log Q)^2\,Y^{\varepsilon/4} \le K_0\,Y^{3\varepsilon/4} \le \frac{1}{3} Y^\varepsilon$$
     since $\log Q \le Y^{\varepsilon/4}$!
   - The horizontal contour height term has size
     $$K_0 (\log Q) \cdot x \cdot \frac{Z}{\eta Q} = K_0 (\log Q)\,\frac{Y^{403K}}{Q}
     \le K_0\,Y^{404K}\,\exp(-Y^{\varepsilon/6}) \le \frac{1}{3} \le \frac{1}{3} Y^\varepsilon$$
     since $Q \ge \exp(Y^{\varepsilon/6})$ crushes every power of $Y$ (`tailK_exp`, `TailKExp.lean:8`)!
   - The short interval $(Z, Z + \eta Z]$ has relative width $\eta = x^{-2}$, contributing
     $x \cdot O(\eta \log Z) = O(Y^{-K} \log Y) \le \frac{1}{3} Y^\varepsilon$.
   Since $y \le Y^K = x$, $\lvert y\,\mathrm{tailL}_\chi(Z) \rvert \le x\,\lvert \mathrm{tailL}_\chi(Z) \rvert \le Y^\varepsilon$.
2. For `kappa4`, set $s := (\log Q)^{1/4}$ and $x_0 := s^{10} = (\log Q)^{5/2}$ (`Kappa4Loglog.lean:10, 56`).
   Because $Q = \exp(s^4)$ grows superpolynomially in $s$, $(s^4)^{1006} \le Q$ for large $s$, so
   the exact same contour bound at $z_0 = x_0^{400} = (\log Q)^{1000}$ gives
   $\lvert \mathrm{tailL}_\chi(z_0) \rvert \le 2K_0 + 802$ (`kappa4_num`, `:9`). Adding Mertens's
   estimate $\sum_{n \le z_0} \Lambda(n)/n \le \log z_0 + C_M = 1000\log\log Q + C_M$ yields
   $$\Bigl\lvert \frac{L'}{L}(1, \chi) \Bigr\rvert \le 1000\log\log Q + C'$$
   (`kappa4_loglog`, `:44`). Substituting $\log Q \le A\,Y^{\varepsilon/5}(\log Y)^2$ gives
   $$1000\log\log Q + C' \le 200\varepsilon \log Y + 2000\log\log Y + 1000\log A + C'.$$
   Because $\varepsilon < 1/52$, we have $4 - 200\varepsilon > 4 - \frac{200}{52} = \frac{2}{13} > 0$,
   so for $Y$ large enough (`Kappa4Loglog.lean:133–153`), the right-hand side is $\le 4\log Y$.
3. For `box_of_S` (`BoxOfS.lean:28–61`), let $y \in [Y, Y^K]$ and $Z = (Y^K)^{400} \ge y$. For
   every $1 \le n \le \lfloor Z \rfloor$, we noted in Definition 4.3(2) that
   $$\frac{\Lambda(n)}{y}\,\min(n, y) = \frac{\Lambda(n)}{n} - \frac{1}{y}\,\Lambda(n)\Bigl(\frac{y}{n} - 1\Bigr)_+.$$
   Multiplying by $y\,\chi(n)$ and summing over $1 \le n \le \lfloor Z \rfloor$ (since $(y/n - 1)_+ = 0$
   for $n > y$, and primes dividing $2Mqd$ contribute at most $2\log Y$, `BoxOfS.lean:47–58`) gives
   $$S_\chi(y) + y\,\frac{L'}{L}(1,\chi)
   = y\sum_{1 \le n \le \lfloor Z \rfloor} \frac{\Lambda(n)\chi(n)}{n} - y\,S(Z, y, q, \kappa) + y\,\frac{L'}{L}(1,\chi) + O_{\le 2}(\log Y)
   = -y\,\mathrm{tailL}_\chi(Z) - y\,S(Z, y, q, \kappa) + O_{\le 2}(\log Y).$$
   By the triangle inequality,
   $$\lvert G_\chi(y) \rvert \le y\,\lvert S(Z, y, q, \kappa) \rvert + \lvert y\,\mathrm{tailL}_\chi(Z) \rvert + 2\log Y
   \le \frac{1}{2} y^{1/2 + \varepsilon/2} + Y^\varepsilon + 2\log Y
   \le y^{1/2 + \varepsilon/2}$$
   since $Y^\varepsilon + 2\log Y \le \frac{1}{2} Y^{1/2 + \varepsilon/2} \le \frac{1}{2} y^{1/2 + \varepsilon/2}$. $\square$

### 4.4.4 Mean-square bounds over primes and the Sobolev–Markov uniformization (`meanSqK`, `twistK`, `bad_share`)

Next we bound $\sum_{q \in \mathrm{PPset}} \lvert S(Z, y, q, \kappa) \rvert^2$ at a single point $y$,
and then upgrade that pointwise $L^2$ bound to a **simultaneous uniform bound for all $y \in [Y, Y^K]$**!

**Proposition 4.5 ($L^2$ mean-square bound over primes with at most one Landau–Page modulus).**
*Let $0 < \varepsilon \le 1/4$ and $K \ge 1$. Suppose $8 \mid m_0$, $\gcd(a_0, m_0) = 1$,
$Z = (Y^K)^{400}$, $U = \exp(u)$ with $Y^{\varepsilon/5} \le u \le 2\,Y^{\varepsilon/5}(\log Y)^2$
and $\frac{1}{4}(\log Y)^2 \log m_0 \le u$, and $\log m_0 \le 4\,Y^{\varepsilon/5}$. Then for all
sufficiently large $Y$ and every $y \in [Y, Y^K]$, `MeanSq m₀ a₀ U Z y` holds:*
$$\sum_{q \in \mathrm{PPset}(m_0, a_0, U)} \bigl\lvert S(Z, y, q, \kappa) \bigr\rvert^2
\le \frac{64 \log y}{y}\,\bigl\lvert \mathrm{PPset}(m_0, a_0, U) \bigr\rvert$$
*for every $\kappa : \mathbb N \to \mathbb C$ with $\lvert \kappa(n) \rvert \le 1$.*
*(Lean: `QH.twistK`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean:148`;
`QH.meanSqK`, `…/meanSqK.lean:51`; `QH.meanSq_abs`, `…/MeanSqAbs.lean:8`; `meanSquareHypW_of_pnt`,
`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMain.lean:55`, using
`pnt_progressions_relative_weak_holds` [Lean] at `…/PNTFinal.lean:22`, `excBound` [Lean] at
`src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:32`, and `page_across` [Lean]
via `…/MSqTwist.lean:26`.)* [Lean, read]

*Proof.* First (`meanSq_abs`, `MeanSqAbs.lean:8–59`), setting $c_n(y) := \frac{\Lambda(n)}{y}\min(n, y) \ge 0$,
expanding the square and applying $\lvert \kappa(n_1)\overline{\kappa(n_2)} \rvert \le 1$ gives
$$\sum_{q \in \mathcal P} \bigl\lvert S(Z, y, q, \kappa) \bigr\rvert^2
= \sum_{1 \le n_1, n_2 \le \lfloor Z \rfloor} c_{n_1}(y) c_{n_2}(y)\,\kappa(n_1)\overline{\kappa(n_2)}
\sum_{q \in \mathcal P} \Bigl(\frac{n_1 n_2}{q}\Bigr)
\le \sum_{1 \le n_1, n_2 \le \lfloor Z \rfloor} c_{n_1}(y) c_{n_2}(y)
\Bigl\lvert \sum_{q \in \mathcal P} \Bigl(\frac{n_1 n_2}{q}\Bigr) \Bigr\rvert,$$
where $\mathcal P := \mathrm{PPset}(m_0, a_0, U)$. Notice why taking absolute values *outside* the
$q$-sum works cleanly: **the inner character sum $\sum_{q \in \mathcal P} (\frac{n_1 n_2}{q})$ no
longer depends on $\kappa$ at all!**

Now factor each product $n_1 n_2$ ($1 \le n_1, n_2 \le \lfloor Z \rfloor$) into its $m_0$-part and
its coprime squarefree core (`MSqMain.lean:70–120`): write $n_1 n_2 = m' \cdot t^2 \cdot s$, where
every prime dividing $m'$ divides $m_0$ (remember $2 \mid m_0$, so $t^2 s$ is **odd**),
$\gcd(t s, m_0) = 1$, and $s \ge 1$ is odd, squarefree, and coprime to $m_0$, with
$$s \le n_1 n_2 \le Z^2 = Y^{800K}.$$
For every $q \in \mathcal P$, we have $q \equiv a_0 \pmod{m_0}$ (so $(\frac{m'}{q})$ is a fixed
sign $\pm 1$ determined by $a_0 \bmod m_0$, since $8 \mid m_0$ fixes $(\frac{2}{q})$ as well) and
$q > U^{1/2} = \exp(u/2) \ge \exp(\frac{1}{2} Y^{\varepsilon/5}) \gg Y^{800K} \ge n_1 n_2$, so the
prime $q$ never divides $t$, making $(\frac{t^2}{q}) = 1$. Finally, since $s$ is odd and $8 \mid m_0$
fixes $q \bmod 4$, quadratic reciprocity turns $(\frac{s}{q})$ into $\pm (\frac{q}{s})$ with a sign
independent of $q \in \mathcal P$:
$$\Bigl\lvert \sum_{q \in \mathcal P} \Bigl(\frac{n_1 n_2}{q}\Bigr) \Bigr\rvert
= \Bigl\lvert \sum_{q \in \mathcal P} \Bigl(\frac{q}{s}\Bigr) \Bigr\rvert.$$

Now `twistK` (`twistK.lean:148–354`, invoked at exponent parameter $B = 3K$ in `meanSqK.lean:62`)
splits the odd squarefree moduli $s \le Z^2$ coprime to $m_0$ into three regimes:

1. **The off-diagonal non-exceptional moduli ($s > 1$, $s \neq n_*$).** As a function of $q$,
   $q \mapsto (\frac{q}{s})$ is a non-principal real primitive character of conductor $s$ or $4s$,
   still non-principal on the progression $q \equiv a_0 \pmod{m_0}$ because $\gcd(s, m_0) = 1$ and
   $8 \mid m_0$. By the classical Landau–Page theorem across moduli $\le 4 Z^2$ (`page_across`,
   `MSqTwist.lean:26` [Lean]), among all real primitive characters of conductor $\le 4 Z^2$, **at
   most one** can violate the classical zero-free region. Hence there exists at most **one** odd
   squarefree integer $n_*$ such that for every $s \notin \{1, n_*\}$ ($s \le Z^2$, $\gcd(s, m_0) = 1$),
   the prime number theorem in progressions modulo $\operatorname{lcm}(m_0, 4s) \le 4 m_0 Z^2$ (note
   $\frac{1}{4}(\log Y)^2 \log m_0 \le u = \log U$ places $U$ inside the Siegel–Walfisz /
   Page-uniform range, with Siegel's bound `excBound` [Lean] guaranteeing $\lvert \mathcal P \rvert \ge U^{9/10}$)
   yields (`twistK.lean:151`)
   $$\Bigl\lvert \sum_{q \in \mathcal P} \Bigl(\frac{q}{s}\Bigr) \Bigr\rvert
   \le Y^{-(3K + 1)}\,\lvert \mathcal P \rvert.$$
   Since $\sum_{n \le Z} c_n(y) \le \frac{1}{y}\sum_{n \le y}\Lambda(n) + \sum_{n \le Z}\frac{\Lambda(n)}{n} \ll K\log Y$,
   multiplying $(\sum_{n \le Z} c_n(y))^2 \ll K^2 (\log Y)^2$ by $Y^{-(3K + 1)}\lvert\mathcal P\rvert$
   is $\ll \frac{1}{y}\lvert\mathcal P\rvert$.
2. **The diagonal ($s = 1$).** Recall $\Lambda(n)$ is supported on prime powers $p^a$. If
   $n_1 = p_1^{a_1}$ and $n_2 = p_2^{a_2}$ have coprime squarefree core $s = 1$, then either
   $p_1 = p_2$ (diagonal prime powers) or both $p_1, p_2$ divide $m_0$. On true diagonal prime powers,
   $$\sum_{n \le Z} c_n(y)^2 = \frac{1}{y^2}\sum_{n \le y} \Lambda(n)^2 + \sum_{y < n \le Z} \frac{\Lambda(n)^2}{n^2}
   \sim \frac{1}{y^2}\,(y \log y) + \frac{\log y}{y} = \frac{2\log y}{y},$$
   and primes dividing $m_0$ (at most $\omega(m_0) \ll Y^{\varepsilon/5}$ primes, handled via Cauchy–Schwarz
   in `MSqMain.lean:95–135`) also contribute $O((\log y)/y)\,\lvert\mathcal P\rvert$.
3. **The single Landau–Page modulus ($s = n_* > 1$).** If $n_1 = p_1^{a_1}$ and $n_2 = p_2^{a_2}$
   have squarefree odd core $s(n_1 n_2) = n_* > 1$, then since $n_*$ is squarefree and $> 1$ while
   $n_1, n_2$ are prime powers, $n_*$ can have **at most two prime factors**: either $n_* = p$ is
   prime or $n_* = p_1 p_2$ is a semiprime with $\{p_1, p_2\}$ fixed by $n_*$ (`abs_pair_sum_eq`,
   `MSqMain.lean:38`). Thus $n_*$ contributes at most $O((\log y)/y)\,\lvert\mathcal P\rvert$ as well.

Adding the diagonal $s = 1$, the single exceptional $s = n_*$, and the off-diagonal tail gives
$\sum_{q \in \mathcal P} \lvert S(Z, y, q, \kappa) \rvert^2 \le \frac{64\log y}{y}\lvert\mathcal P\rvert$. $\square$

How do we pass from a bound **at each fixed $y$** to a bound **simultaneously for all uncountably
many $y \in [Y, Y^K]$** without losing a factor of $Y$? Look at the archive's `bad_share`
(`BadShare.lean:1–320`), which we read in full (`R3`) — it is a textbook one-dimensional Sobolev
embedding ($W^{1,2} \hookrightarrow L^\infty$) on dyadic intervals!

**Lemma 4.6 (Dyadic Sobolev–Markov uniformization: `QH.bad_share`).** *Fix $Z \ge 1$, $q$-set
$\mathcal P = \mathrm{PPset}(m_0, a_0, U)$ nonempty, $\kappa : \mathbb N \to \mathbb C$ with
$\lvert \kappa(n) \rvert \le 1$, $\tau > 0$, $\eta > 0$, $R \in \mathbb N$, and $K \ge 1$. Assume
`MeanSq m₀ a₀ U Z y` holds for **every** $y \in [Y, 2 Y^K]$, where $Y \ge 3$ satisfies*
$$2^{14}\,(R + 1)\,K\,\frac{(\log(2 Y^K))^2}{\eta\,Y^{2\tau}} \le 1.$$
*Then the set of $q \in \mathcal P$ for which $\sup_{y \in [Y, Y^K]} y^{1/2 - \tau} \lvert S(Z, y, q, \kappa) \rvert > \frac{1}{2}$
has cardinality at most $\frac{\eta}{2(R + 1)}\,\lvert \mathcal P \rvert$.*
*(Lean: `QH.bad_share`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean:251`.)* [Lean, read]

*Proof.* Write $S_q(y) := S(Z, y, q, \kappa) = \sum_{1 \le n \le \lfloor Z \rfloor} c_n(y)\kappa(n)(\frac{n}{q})$,
where $c_n(y) = \frac{\Lambda(n)}{n}$ for $n > y$ and $c_n(y) = \frac{\Lambda(n)}{y}$ for $n \le y$.
Differentiating $y \mapsto c_n(y)$ for $y > 0$ (`bs_hasDeriv_min`, `BadShare.lean:48`):
- for $n > y$, $c_n(y) = \frac{\Lambda(n)}{n}$ is **constant** in $y$, so its derivative is $0$;
- for $n < y$, $c_n(y) = \frac{\Lambda(n)}{y}$ has derivative $-\frac{\Lambda(n)}{y^2} = -\frac{1}{y}\,c_n(y)$!
Therefore, away from the finitely many integers $n$, $S_q(y)$ is continuous and piecewise $C^1$ with
almost-everywhere derivative $D_q(y)$ satisfying (`bs_S_sub_S` and `bs_mul_D_eq_S`,
`BadShare.lean:76, 83`)
$$S_q(b) - S_q(a) = \int_a^b D_q(v)\,dv
\qquad\text{and}\qquad
y\,D_q(y) = -S\bigl(Z, y, q, \mathbf{1}_{n < y}\,\kappa\bigr)!$$
Pause to appreciate that identity (`bs_mul_D_eq_S`, `:83`): **$y\,D_q(y)$ is itself an instance of
$S(Z, y, q, \kappa_{<y})$** for the truncated weight $\kappa_{<y}(n) := -\mathbf{1}_{n < y}\,\kappa(n)$,
which still satisfies $\lvert \kappa_{<y}(n) \rvert \le 1$! Hence `MeanSq` applies **not only to
$S_q(y)$ itself, but also to $v\,D_q(v)$ at every point $v$**:
$$\sum_{q \in \mathcal P} \lvert S_q(a) \rvert^2 \le \frac{64\log a}{a}\lvert\mathcal P\rvert,
\qquad
\sum_{q \in \mathcal P} v^2 \lvert D_q(v) \rvert^2 \le \frac{64\log v}{v}\lvert\mathcal P\rvert!$$

Now cover $[Y, Y^K]$ by $M \le \lceil K \log_2 Y \rceil + 1$ dyadic blocks $[a_j, 2 a_j] \subseteq [Y, 2 Y^K]$
with $a_j = 2^j Y$ (`bs_block`, `:163`). On a single dyadic block $[a, 2a]$ ($a \ge Y$), for any
$y \in [a, 2a]$, Cauchy–Schwarz gives (`bs_sq_integral_le`, `:98`):
$$\begin{aligned}
\lvert S_q(y) \rvert^2
&\le 2\lvert S_q(a) \rvert^2 + 2\Bigl(\int_a^{2a} \lvert D_q(v) \rvert\,dv\Bigr)^2 \\
&\le 2\lvert S_q(a) \rvert^2 + 2a \int_a^{2a} \lvert D_q(v) \rvert^2\,dv \\
&\le 2\lvert S_q(a) \rvert^2 + \frac{2}{a}\int_a^{2a} v^2 \lvert D_q(v) \rvert^2\,dv.
\end{aligned}$$
The right-hand side is **independent of $y \in [a, 2a]$**! Taking $\sup_{y \in [a, 2a]} \lvert S_q(y) \rvert^2$
on the left, summing over $q \in \mathcal P$, and exchanging $\sum_q$ with $\int_a^{2a}$ by Tonelli's
theorem (`bs_sum_D_le`, `:146`) yields
$$\sum_{q \in \mathcal P} \sup_{y \in [a, 2a]} \lvert S_q(y) \rvert^2
\le \frac{128\log a}{a}\lvert\mathcal P\rvert + \frac{2}{a}\int_a^{2a} \frac{64\log v}{v}\lvert\mathcal P\rvert\,dv
\le \frac{256\log(2a)}{a}\,\lvert\mathcal P\rvert!$$
Look at that: **uniformity over the entire continuum $[a, 2a]$ cost only a factor of $4$!** Now if
$\sup_{y \in [a, 2a]} y^{1/2 - \tau} \lvert S_q(y) \rvert > \frac{1}{2}$, then since $y \le 2a$,
$\sup_{y \in [a, 2a]} \lvert S_q(y) \rvert^2 > \frac{1}{4}(2a)^{-1 + 2\tau} \ge \frac{1}{8}\,a^{-1 + 2\tau}$.
Markov's inequality on $[a, 2a]$ bounds the number of bad $q$ on block $j$ by
$8\,a_j^{1 - 2\tau} \cdot \frac{256\log(2a_j)}{a_j}\lvert\mathcal P\rvert = 2^{11}\,\frac{\log(2a_j)}{a_j^{2\tau}}\lvert\mathcal P\rvert$.
Summing over all $M \ll K \log Y$ dyadic blocks (`bs_markov` and `bad_share`, `:207–319`) bounds
the total number of bad $q$ across all of $[Y, Y^K]$ by
$2^{13}\,K\,\frac{(\log(2Y^K))^2}{Y^{2\tau}}\lvert\mathcal P\rvert \le \frac{\eta}{2(R+1)}\lvert\mathcal P\rvert$. $\square$

### 4.4.5 Assembling the two-stage sieve (`stage` and `pairEx`)

Combining Lemmas 4.3, 4.4, 4.5, and 4.6 immediately proves the single-stage sieve `QH.stage` and
then the two-stage prime-pair existence theorem `PairEx`.

**Theorem 4.7 (Single-stage and two-stage prime sieve: `QH.stage` and `PairEx`).**

1. **Single-stage sieve (`QH.stage`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:41`).**
   *Let $0 < \varepsilon \le 1/4$, $A \ge 1$, $K \ge 1$, $0 < \eta \le 1$, and $R \in \mathbb N$.
   There exists $Y_0 \ge 3$ such that for every $Y \ge Y_0$, whenever $8 \mid m_0$, $\gcd(a_0, m_0) = 1$,
   $\log m_0 \le 4\,Y^{\varepsilon/5}$, and $U = \exp(u)$ satisfies $Y^{\varepsilon/5} \le u \le A\,Y^{\varepsilon/5}(\log Y)^2$
   and $\frac{1}{4}(\log Y)^2 \log m_0 \le u$, and $(f_r, \xi_r)_{r \in I}$ ($\lvert I \rvert \le R + 1$)
   is a family of primitive characters of conductors $f_r \le \exp(\frac{1}{3} u)$ whose twists
   $\psi_{r, q}$ ($q \in \mathrm{PPset}(m_0, a_0, U)$) have conductor $f_r q$ and satisfy
   $\psi_{r, q}(n) = \kappa_r(n)(\frac{n}{q})$, the set of $q \in \mathrm{PPset}(m_0, a_0, U)$ failing
   either `ZeroFreeBox (exp((4/3)u)) ψ_{r,q}` or $\sup_{y \in [Y, Y^K]} y^{-1/2 - \varepsilon/2}\lvert G_{\psi_{r,q}}(y) \rvert \le 1$
   or $\lvert \frac{L'}{L}(1, \psi_{r,q}) \rvert \le 4\log Y$ for some $r \in I$ has cardinality at
   most $\eta\,\lvert \mathrm{PPset}(m_0, a_0, U) \rvert$.* [Lean, read]
2. **Two-stage existence (`QH.pairEx` / `PairEx`, `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112`).**
   *`PairEx` holds: for every $M \ge 1$, every $0 < \varepsilon < 1/52$, and every $A \ge 1$, there
   exists $Y_0$ such that for all $Y \ge Y_0$, there exist primes $(q, d)$ satisfying
   `PairGood M eps Y (Y^A) q d`.* [Lean, read]

*Proof.*

1. Set $Q := \exp(\frac{4}{3} u) = U^{4/3}$, so $f_r q \le U^{1/3} U = U^{4/3} = Q$ and
   $Y^{\varepsilon/6} \le \frac{4}{3} u = \log Q \le \frac{4}{3} A\,Y^{\varepsilon/5}(\log Y)^2 \le Y^{\varepsilon/4}$
   for large $Y$ (`stage_log`, `StagePow.lean:16`). Every bad $q \in B \subseteq \mathcal P$ either
   lies in the zero-box failure set $B_1$ (where `ZeroFreeBox Q ψ_{r,q}` fails for some $r$) or
   satisfies `ZeroFreeBox Q ψ_{r,q}` for all $r$ while failing the $G_\chi$ or $L'/L$ bound for
   some $r$. In `StagePow.lean:105`, so that Stage 2 can call `stage` at $\varepsilon' = \frac{6}{5}\varepsilon$
   and still deliver exponent $\frac{1}{2} + \frac{\varepsilon}{2} = \frac{1}{2} + \frac{5}{12}\varepsilon'$,
   `box_of_S` and `bad_share` are run at $\tau = \frac{5}{12}\varepsilon'$: any $q \in B \setminus B_1$
   must fail $\sup_{y \in [Y, Y^K]} y^{1/2 - \tau} \lvert S((Y^K)^{400}, y, q, \kappa_r) \rvert \le \frac{1}{2}$
   for some $r \in I$.
   - For $B_1$: Lemma 4.3 gives $\lvert B_1 \rvert \le C_{\mathrm{ZD}}\,Q^{1/4} = C_{\mathrm{ZD}}\,U^{1/3}$,
     while `count_a` (`PNTFinal.lean:22` + `excBound` [Lean]) gives $\lvert \mathcal P \rvert \ge U^{9/10}$
     (`stage_pow`, `StagePow.lean:29`). Since $\frac{1}{3} < \frac{9}{10}$, $C_{\mathrm{ZD}} U^{1/3} \le \frac{\eta}{2} U^{9/10} \le \frac{\eta}{2}\lvert \mathcal P \rvert$
     for large $Y$.
   - For $B \setminus B_1$: Proposition 4.5 supplies `MeanSq` on $[Y, 2 Y^K]$, so Lemma 4.6 (`bad_share`)
     gives at most $\frac{\eta}{2(R+1)}\lvert\mathcal P\rvert$ bad primes for each $r \in I$. Summing
     over the $\le R + 1$ indices $r \in I$ gives $\lvert B \setminus B_1 \rvert \le \frac{\eta}{2}\lvert\mathcal P\rvert$.
   Hence $\lvert B \rvert \le (\frac{\eta}{2} + \frac{\eta}{2})\lvert\mathcal P\rvert = \eta\,\lvert\mathcal P\rvert$.
2. Now fix $M \ge 1$, $0 < \varepsilon < 1/52$, and $A \ge 1$, and set $z := Y^{\varepsilon/5}$ and
   $z' := Y^{\varepsilon/5}(\log Y)^2$ (`pairEx.lean:112–170`, `PairExists.lean:9`, `PairShare.lean:26`).
   - **Stage 1 (`stage1`, `Stage1Succ.lean:36`):** Apply `QH.stage` (with $\eta = 1/4$) to
     $\mathcal P_1 := \mathrm{PPset}(8, 3, \exp(z))$, twisting all primitive characters dividing
     $2M$ ($R_1 + 1 \le 2M$ characters of conductor $\le 2M \ll \exp(z/3)$). Note $\log m_0 = \log 8$,
     so $\frac{1}{4}(\log Y)^2 \log 8 \ll Y^{\varepsilon/5} = z$ holds trivially. Because
     $\lvert \mathcal P_1 \rvert > 0$ and at most $\frac{1}{4}\lvert\mathcal P_1\rvert$ primes are
     bad, at least $\frac{3}{4}\lvert\mathcal P_1\rvert \ge 1$ primes $q \in \mathcal P_1$ satisfy
     every $(i = 1, j = 0)$ requirement of `PairGood` (`GoodQ`). Pick one such prime $q \equiv 3 \pmod 8$
     with $\frac{1}{2} z < \log q \le z$ (for large $Y$, $q > 2M$, so $\gcd(M, q) = 1$).
   - **Stage 2 (`stage2`, `CharOf.lean:61`):** With $q$ fixed, let
     $\mathrm{oddM}(z, q) := q \cdot \prod_{2 < p \le z,\,p\text{ prime}} p$ (`SecondEstimateOfIntervalHypothesis.lean:53`).
     By the Chebyshev primorial bound $\sum_{2 < p \le z} \log p \le 2z$ (`PrimorialBound`), the Stage 2
     progression modulus $m_0 := 16 \cdot \mathrm{oddM}(z, q)$ satisfies
     $$\log m_0 = \log 16 + \log q + \sum_{2 < p \le z} \log p \le \log 16 + z + 2z \le 4z = 4\,Y^{\varepsilon/5}.$$
     By the Chinese remainder theorem, since $16$ and $\mathrm{oddM}(z, q)$ are coprime, there is a
     residue class $a_0 \bmod m_0$ with $\gcd(a_0, m_0) = 1$ defined by
     $$a_0 \equiv 7 \pmod{16} \qquad\text{and}\qquad a_0 \equiv -1 \pmod{\mathrm{oddM}(z, q)}$$
     (`PrimeSetTwoBounds.lean:45`). Any prime $d \in \mathcal P_2 := \mathrm{PPset}(m_0, a_0, \exp(z'))$
     automatically satisfies $d \equiv 7 \pmod{16}$, $q \mid d + 1$, $p \mid d + 1$ for all odd
     primes $p \le z = Y^{\varepsilon/5}$, and $\frac{1}{2}z' < \log d \le z'$ — so **`WinPair eps Y q d`
     holds for every $d \in \mathcal P_2$**. Moreover, Stage 2 calls `QH.stage` at
     $\varepsilon' := \frac{6}{5}\varepsilon < \frac{6}{5}\cdot\frac{1}{52} < \frac{1}{4}$ (`CharOf.lean:71`)
     on $u = z' = z(\log Y)^2$ (or $u \ge \frac{1}{4}(\log Y)^2 \log m_0$ since $\log m_0 \le 4z$).
     Twisting all primitive characters of $\chi_0 \cdot (\frac{\cdot}{q})^i$
     ($i \in \{0, 1\}$, conductor $\le 2Mq \le 2M e^z \ll e^{z'/3}$) by $(\frac{\cdot}{d})$ and
     applying `stage` ($\eta = 1/4$) leaves at least $\frac{3}{4}\lvert \mathcal P_2 \rvert \ge 1$
     primes $d \in \mathcal P_2$ satisfying all $(i, 1)$ conditions (`GoodD`, `PairShare.lean:26`,
     `PairExists.lean:9`). Note finally that in `PairGood`, `height q d i 0` $= q \le \exp(\frac{4}{3}\log q)$
     and `height q d i 1` $= d \le \exp(\frac{4}{3}\log d)$, so `ZeroFreeBox Q` implies `ZeroBox (height q d i j)`
     (`pairEx_box`, `pairEx.lean:17`), completing `PairEx`. $\square$

### 4.4.6 Window rescaling (`winPairs`) and assembling the host supply (`supplyChi`)

With `PairEx` proved unconditionally, two short, fully read (`R3`) glue theorems connect `PairEx`
and `VWin` (`VWinAt ψ 401`) to the exact `HostExW (3 / 2)` window-supply hypothesis used by
`zeroFreeAll_of_topG` in Chapter 3 (Theorem 3.7)!

**Proposition 4.8 (Rescaling quadratic `VWinAt ψ 401` windows to $Z^{3/2}$ windows: `winPairs`).**
*Let $\psi \in \mathrm{PChar}$, $0 < \varepsilon < 1/52$, and $c \ge 1$. Assume `VWinAt ψ 401` and
`PairEx`. Then there exists $J \ge 1$ such that for every real threshold $y$, there exists $Z \ge y$
such that for every $x \in [Z, Z^{3/2}]$, there exist $Y \in \mathbb R$ and $q, d, e \in \mathbb N$
satisfying `WinDatum ψ eps J c x Y q d e` (`TwistForm.lean:19`), namely:*

1. $x^{1/J} \le Y \le x$ *and* `PairGood ψ.N eps Y x q d`;
2. $x^{2 + 8\varepsilon} \le c \cdot 2^e \le 2\,x^{2 + 8\varepsilon}$; *and*
3. *for every number field $E$ satisfying `IsChiField ψ e q d E`, we have
   `VVle E ⌊x^400⌋₊ (sqrt (exp (x^eps)))` (note $\sqrt{\exp(x^\varepsilon)} = \exp(x^\varepsilon / 2)$).*
*(Lean: `UpperTheory.Top.winPairs`, `src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean:5`.)* [Lean, read]

*Proof.* First choose $e : \mathbb R \to \mathbb N$ satisfying `PageN eps e` by Lemma 4.1(1).
Applying `VWinAt ψ 401` to $(\varepsilon, e)$ gives $J \ge 1$ and $X_0$, and applying `PairEx` to
$(\psi.N, \varepsilon, J)$ gives $Y_1$ (`WinPairs.lean:10–13`). Define the rescaling factor
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
  (`PairGood.mono`, `PairGood.lean:41`) gives `PairGood ψ.N eps Y x q d`.
- Applying `PageN` at $x' \ge 1$ gives $(x')^{2+8\varepsilon} \le 2^{e(x')} \le 2(x')^{2+8\varepsilon}$;
  multiplying by $c = k^{2+8\varepsilon}$ gives $x^{2+8\varepsilon} \le c \cdot 2^{e(x')} \le 2\,x^{2+8\varepsilon}$.
- Because $x' \in [W, W^2]$, `VAt ψ 401` gives `VVle E ⌊(x')^401⌋₊ (exp((x')^eps / 2))` for every $E$
  satisfying `IsChiField ψ (e x') q d E`. Since $k^{400} \le M \le W \le x'$ and $1 \le k$,
  $$x^{400} = k^{400}(x')^{400} \le x' \cdot (x')^{400} = (x')^{401}
  \qquad\text{and}\qquad
  \exp\bigl((x')^\varepsilon / 2\bigr) \le \exp(x^\varepsilon / 2) = \sqrt{\exp(x^\varepsilon)}.$$
  Monotonicity of `VVle` in both arguments (`VVle.mono`, `ExistsPageN.lean:51`) gives
  `VVle E ⌊x^400⌋₊ (sqrt (exp (x^eps)))`. $\square$

**Theorem 4.9 (Host supply on $Z^{3/2}$ windows: `supplyChi`).** *Assume `VWin` and `PairEx`. Then
for every primitive character $\psi \in \mathrm{PChar}$, there exists a window host supply at
exponent $\lambda = 3/2$:*
$$\mathrm{HostExW}\ \frac{3}{2}\ \Bigl(\text{producing }(s, R, H)\text{ with }\mathrm{EAtH}(\mathrm{Level.cyc}\,\psi, H.\mathrm{toHostRaw}, H.TT, s.x, s.\varepsilon, 4)\ \land\ \mathrm{VVle}\,H.E\,R.t\,\sqrt{s.b}\Bigr).$$
*(Lean: `UpperTheory.Top.supplyChi`, `src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean:8`,
via `fieldChi` (`…/FieldChi.lean:20`), `supplyOfAdmOf` (`src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:13`),
`eventually_rank_le_rpow_of_lt_one_div_fiftytwo` (`…/CharacterBoxes/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5`),
and the imported short-norm coset theorem `hostOfField` [Lean] (`…/CharacterBoxes/HostOfField.lean:8`)
and admissible-rank existence `admissible_ranks_of_CMDatum` [Lean] (`…/CoprimeRanks/AdmChi.lean:11`).)* [Lean, read]

*Proof.* Fix $\psi \in \mathrm{PChar}$ and $0 < \varepsilon < 1/52$. First, `fieldChi ψ`
(`FieldChi.lean:20`) fixes the constant factor $c \ge 1$ and threshold $e_0$ such that for any
$e \ge e_0$ and any $(q, d)$ obeying `HostHyp q d`, $q \neq 3$, $\gcd(\psi.N, qd) = 1$, and
$(\frac{-d}{p}) = 1$ for odd primes $p \le b$ ($b \ge 4\psi.N$), there exists a host field
`H0 : HostAx φ` with $\varphi.e = e$, $\varphi.\mathrm{ord} = c \cdot 2^e$, $\varphi.o = (\mathrm{Level.cyc}\,\psi).o$,
`KeptInXp`, `ExceptionalCharacterKept`, `KerChi ψ H0`, and `TwistForm ψ H0`.

Second, Proposition 4.8 (`winPairs`) supplies windows $[Z, Z^{3/2}]$ on which every $x \in [Z, Z^{3/2}]$
has `WinDatum ψ eps J c x Y q d e` (`supplyOfAdmOf.lean:58–80`). At each $x \in [Z, Z^{3/2}]$:

- Lemma 4.1(2) converts `WinPair eps Y q d` into `HostHyp q d`, $q \neq 3$, and $(\frac{-d}{p}) = 1$
  for odd primes $p \le \lfloor Y^{\varepsilon/5} \rfloor$, so `fieldChi` constructs `H0 : HostAx φ`
  with $x^{2+8\varepsilon} \le \varphi.\mathrm{ord} = c \cdot 2^e \le 2 x^{2+8\varepsilon}$
  (`supplyOfAdmOf.lean:88–103`).
- Lemma 4.2(1) (`isChiField`) deduces `IsChiField ψ e q d H0.E` from `KerChi ψ H0`, so Conclusion 3
  of `WinDatum` gives `VVle H0.E ⌊x^400⌋₊ (sqrt s.b)` (since $s.b = \exp(x^\varepsilon)$); by
  `eventually_rank_le_rpow_of_lt_one_div_fiftytwo` (`EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5`,
  using $\varepsilon < 1/52$ to check $R.t \le 10708\,x^{399.67} \le \lfloor x^{400} \rfloor$),
  monotonicity lowers $\lfloor x^{400} \rfloor$ to $R.t$.
- Lemma 4.2(2) (`boundedTw`) combines `TwistForm ψ H0` and `PairGood ψ.N eps Y x q d` to verify
  both `BoundedCharsPointwise (Level.cyc ψ).KEPT x eps` (`EAtH.bdG`) and the $4\log x$ bound on
  $\lvert \frac{L'}{L}(1, \chi) \rvert$ (`EAtH.bdL`, with $C = 4$!).
- Finally, the imported short-norm theorem `hostOfField` (`HostOfField.lean:8` [Lean]) equips `H0`
  with a finite set $TT \subset \varphi.A$ of Galois elements (Frobenius classes of split primes of
  norm $\le x^{\varepsilon}$) satisfying the weighted coset-equidistribution property
  `φ.Shares TT (x^{-1 + eps})` (`EAtH.shares`). Together with `KeptInXp`, `ExceptionalCharacterKept`,
  and $\varphi.o = (\mathrm{Level.cyc}\,\psi).o$, all six fields of `EAtH (Level.cyc ψ) H.toHostRaw H.TT x eps 4`
  hold (`supplyOfAdmOf.lean:123–134`). $\square$

---

## 4.5 Remarks

### 4.5.1 Why there is zero circularity here

Let us double-check the logical hygiene of Chapter 4 [Expository]:

1. **Which $L$-functions receive zero-free boxes in `PairGood`?** Only the primitive characters of
   $\mathrm{tw}(\chi_0, q, d, i, j)$ with **$(i \neq 0 \lor j \neq 0)$** (`PairGood.lean:23`)! When
   $(i, j) = (0, 0)$, the character $\chi_0 \bmod M$ sits inside $\mathrm{Level.cyc}(\psi)$, and
   **nothing in Chapter 4 ever asserts a zero-free box or a prime-sum bound for $(i, j) = (0, 0)$**.
   Instead, $(i, j) = (0, 0)$ is the *output* `Kept` family that Chapter 5 isolates on the left-hand
   side of $\Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}$, while $(i, j) \neq (0, 0)$
   is the `Bounded` parasitic family moved to the right-hand side!
2. **Why Siegel's theorem causes no ineffectiveness problem.** Classically, C. L. Siegel's lower
   bound $L(1, \chi_{\mathrm{real}}) \gg_\eta q^{-\eta}$ (*Acta Arith.* **1** (1935), 83–86) has an
   ineffective implied constant, which makes the threshold $Y_0(M, \varepsilon, A)$ in `PairEx`
   (`pairEx.lean:112`) existentially quantified rather than explicit. Look back at Chapter 3,
   Definition 3.4 (`HasWindows`, `Window.lean:7`): the Landau-window criterion only asks that
   $\forall y_0,\ \exists Y \ge y_0$ with a good window $[Y, Y^{3/2}]$ — a purely existential
   statement! Whether $Y_0(\varepsilon)$ is computable or not makes no difference to proving
   $L(s, \psi) \neq 0$ on $\Re s > 1/2$ [Expository].
3. **Resolving a community vacuity flag (`pair_share`).** The LUMI vacuity report
   (`aapolipponen/rh-lean-check-lumi`, `docs/reports/vacuity-check.md`) flagged `pair_share` for
   closer human reading because `PairShare.lean` takes existence hypotheses on Stage 1 and Stage 2
   as parameters [Community]. Having read `PairShare.lean`, `PairExists.lean`, `Stage1Succ.lean`,
   `CharOf.lean`, and `pairEx.lean` line by line (`R3`), we can report that `pair_exists`
   instantiates `pair_share` at $\eta = 1/4$ and deduces $\lvert G \rvert > 0$ from $\lvert \mathcal P \rvert > 0$
   (supplied unconditionally by PNT in progressions `count_a`) and $\lvert B \rvert \le \frac{1}{4}\lvert \mathcal P \rvert$:
   there is no vacuity at the seam [Lean, read].

### 4.5.2 Summary of the numerical constants

For quick reference in Chapters 5 and 7–11, the table below summarizes where each numerical constant
of this chapter originates [Lean, read]:

| Constant | Lean location | Mathematical role |
|---|---|---|
| $1/400$ and $400$ | `PairGood.lean:13`, `BoxOfS.lean:33`, `TailKExp.lean:26` | Zero-free box width $\Re s > 1 - 1/400$ paired with explicit-formula truncation $Z = x^{400}$ so $x \cdot (x^{400})^{-1/400} = 1$. |
| $401$ | `ExistsPageN.lean:49`, `WinPairs.lean:78` | Upstream Tate–Shafarevich twist cutoff $\lfloor (x')^{401} \rfloor$; absorbs $k^{400} \le x'$ under $x = k x'$ so $x^{400} \le (x')^{401}$. |
| $\lambda = 3/2$ | `WinPairs.lean:7,40`, `SupplyChi.lean:9` | Window exponent $[Z, Z^{3/2}]$ after rescaling $Z = kW$ inside a quadratic `VWin` window $[W, W^2]$ ($k^3 \le W \implies (kW)^{3/2} \le W^2$). |
| $\varepsilon/5$ | `ExistsPageN.lean:29–34`, `pairEx.lean:119` | Log-scale $\log q \asymp Y^{\varepsilon/5}$, $\log d \asymp Y^{\varepsilon/5}(\log Y)^2$: large enough that $q > Y^{800A}$, small enough that $1000\log\log d \approx 200\varepsilon \log Y$. |
| $\varepsilon < 1/52$ | `Kappa4Loglog.lean:126`, `EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5` | Ensures $200\varepsilon < 50/13 < 4$ (giving $\lvert L'/L(1,\chi) \rvert \le 4\log Y$, hence $C = 4$ in `EAtH`) and $R.t \le \lfloor x^{400} \rfloor$. |

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
  at $\sigma = 1 - 1/400$ and $T = Q$, any $c < 100/3$ gives exponent $< 3 \cdot \frac{100}{3} \cdot \frac{1}{400} = 1/4$,
  comfortably below the classical Ingham–Montgomery–Jutila constant $c \le 12/5$!).

### 4.5.4 Masullo's counterpart

Masullo's draft *The Music of the Primes* never introduces auxiliary prime pairs $(q, d)$, CM host
fields, character-family mean squares, or zero-density estimates: because his strategy works directly
with an arbitrary continuous Hecke character $\chi$ on the idele class group $C_F$ of the fixed
base field $F$, there are no parasitic twists to eliminate [Expository].

The nearest counterparts in Masullo's draft are the two classical analytic preparation sections in
**Appendix B ("Preparations from Analytic Number Theory", p. 587)** that supply unconditional a
priori control on $L_f(s, \chi)$ before the trace formula is invoked [Paper; Masullo pp. 587–591,
636–643]:

- **Appendix B.1 ("Convexity bound on $L_f(s, \chi)$", pp. 588–591):** proves Phragmén–Lindelöf
  convexity for meromorphic functions with finitely many simple poles (Lemma B.1.1.1, pp. 589–590)
  and deduces Proposition B.1.1.3 (p. 591), $L_f(\sigma + it, \chi) \ll_{F,\chi,\varepsilon} \lvert t \rvert^{[F:\mathbb Q](1-\sigma)/2 + \varepsilon}$
  uniformly for $\sigma \in [0, 1]$ [Paper; Masullo pp. 589–591].
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
subexponential height $Q \approx \exp(\frac{4}{3}Y^{\varepsilon/5})$ — impossible to prove a priori
for an individual character, and obtained only by discarding $O(Q^{1/4})$ exceptions out of a random
prime family!

---

## 4.6 Lean counterpart for this chapter

Every file in `CharacterBoxes/`, `MeanSquareBounds/`, `ShortNorms/supplyOfAdmOf.lean`,
`TotientGaloisClasses/`, and `FrobeniusOrbits/Statement.lean` cited below was read in full by us
(`R3` / `[Lean, read]`). The classical analytic sub-packages (`zero_density_box`, `box_tail_bound`,
`twist_bound`, `pnt_progressions_relative_weak_holds`, `excBound`) and the short-norm/rank packages
(`hostOfField`, `admissible_ranks_of_CMDatum`) were read at statement level (`R2` / `[Lean]`).

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
| `QH.box_of_S` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean:28` | Lemma 4.4(3): splits $G_\chi(y)$ at $Z = (Y^K)^{400}$ into $-y\,S(Z, y, q, \kappa)$ and $-y\,\mathrm{tailL}_\chi(Z)$. | [Lean, read] |
| `QH.meanSq_abs`, `QH.meanSqK`, `QH.twistK` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean:8`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean:51`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean:148` | Proposition 4.5: expands $L^2$ norm, strips $\kappa$, and bounds Jacobi character sums over primes outside at most one Landau–Page modulus $n_*$. | [Lean, read] |
| `QH.bs_S_sub_S`, `bs_mul_D_eq_S`, `bs_sq_integral_le`, `bs_sum_D_le`, `bs_markov`, `bad_share` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean:76,83,98,146,207,251` | Lemma 4.6: fundamental theorem of calculus $y D_q(y) = -S(Z, y, q, \mathbf{1}_{n<y}\kappa)$, dyadic Cauchy–Schwarz, and Markov uniformization on $[Y, Y^K]$. | [Lean, read] |
| `QH.stage_log`, `stage_pow`, `stage` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:16,29,41` | Theorem 4.7(1): single-stage prime sieve combining `count_bad`, `box_of_S`, `meanSqK`, and `bad_share`. | [Lean, read] |
| `QH.stage1`, `QH.stage2`, `QH.pair_share`, `QH.pair_exists`, `QH.pairEx` | `src/Development/AutomorphicArithmetic/MeanSquareBounds/Stage1Succ.lean:36`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/CharOf.lean:61`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairShare.lean:26`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean:9`; `src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112` | Theorem 4.7(2): Stage 1 ($q \equiv 3 \pmod 8$) + Stage 2 ($d \equiv 7 \pmod{16}$, $q \mid d+1$, small odd $p \mid d+1$) $\implies$ `PairEx`. | [Lean, read] |
| `ZeroDensityBox`, `zero_density_box` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean:7`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13` | Definition 4.3(1) (`[Lean, read]`) and imported proof (`[Lean]`, 9 internal large-sieve/mollifier files) of the $C Q^{1/4}$ zero-density bound on $\mathcal B(Q)$. | [Lean] |
| `meanSquareHypW_of_pnt` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMain.lean:55` | Diagonal $s=1$ and single exceptional modulus $s=n_*$ prime-power counting for `MeanSq`. | [Lean, read] |
| `box_tail_bound`, `twist_bound`, `pnt_progressions_relative_weak_holds`, `excBound` | `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailFinal.lean:13`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwist.lean:18`; `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:22`; `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:32` | Imported classical analytic packages: Perron contour tail on $\mathcal B(Q)$, Landau–Page character sum bound, PNT in progressions, and Siegel's lower bound. | [Lean] |

**Summary of the chapter.** Embedding a primitive Dirichlet character $\psi$ into a CM host field
$E \subset \mathbb Q(\zeta_N)$ of degree $4 c \cdot 2^e$ requires two auxiliary primes
$q \equiv 3 \pmod 8$ and $d \equiv 7 \pmod{16}$ (excluding complex conjugation so $E$ is CM over
$F = E^+$, splitting $2, q$ and all prime divisors of $\psi.N$ in $K = \mathbb Q(\sqrt{-d})$, and
providing an odd parity partner for odd $\psi$, Lemma 4.2) [Lean, read]. Choosing
$\log q \asymp Y^{\varepsilon/5}$ and $\log d \asymp Y^{\varepsilon/5}(\log Y)^2$ with $q \mid d + 1$
and small odd primes dividing $d + 1$ allows a two-stage unconditional sieve — combining a $Q^{1/4}$
zero-density bound (`zero_density_box` [Lean]), explicit-formula truncation at $Z = x^{400}$ matched
to box width $1/400$ (Lemma 4.4), $L^2$ Jacobi character-sum bounds with at most one Landau–Page
modulus (Proposition 4.5), and a dyadic Sobolev–Markov inequality (Lemma 4.6) — to produce a pair
$(q, d)$ whose parasitic twists satisfy $\lvert G_\chi(x) \rvert \le x^{1/2+\varepsilon}$ and
$\lvert L'/L(1,\chi) \rvert \le 4\log x$ on $[Y, Y^A]$ (Theorem 4.7) [Lean, read]. Rescaling
quadratic `VWin` windows from exponent $401$ to $400$ and from $[W, W^2]$ to $[Z, Z^{3/2}]$ yields
`supplyChi` (Proposition 4.8 and Theorem 4.9) [Lean, read], delivering the exact host-field package
`EAtH` consumed in Chapter 5.
