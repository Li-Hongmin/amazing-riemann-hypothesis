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
   $L'$ near $1$. The mean-value theorem is the classical route [Expository]. We read the assembly; `siegelLower`
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

**Remaining R2 [Lean].** The proof bodies of `TailContourA` and the consumed declarations of `TailContourB` are read locally. Section [4.8.7.6](#4876-source-map-and-reading-boundary) records the local R3 reading of `perron_formula_character` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean:283`), `rectangle_contour_shift_character` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RectShiftChi.lean:114`) and their direct suppliers. On the box side [§4.8.8](#488-local-zeros-and-the-logarithmic-derivative-in-tailbox) reads the local Landau expansion, the inverse bound `inverseBound` and the right-half-plane bound `l_log_deriv_right` through their direct production proofs, while [§4.10.9](#4109-uniform-polynomial-growth-in-the-half-plane-lfunction_polynomial_growth-and-exlf_growth) reads the polynomial-growth input `lfunction_polynomial_growth` (`src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:53–71`) at local R3. The zeta Laurent remainder bound and the deeper analytic dependencies retain R2 [Lean]. The unused Perron horizontal provider and the standalone kernel lemmas receive no promotion from this reading. The complete imported proof of `tail_contour` remains R2. The conditional proof here reads one estimate with its analytic inputs exposed.

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

Put $R=r/3$. The holomorphic function $h'/h$ has a primitive $g$ on $B(c,R)$ with $g(c)=0$. The derivative of $he^{-g}$ vanishes, so $h=h(c)e^g$. The bound on $h$ gives $\Re g\le\log H$. For $A>\log H$ put $u=g/(2A-g)$. The denominator is nonzero and $|u|\le1$ because $|2A-g|^2-|g|^2=4A(A-\Re g)>0$. Since $u(c)=0$, Schwarz's lemma gives $|u(w)|\le |w-c|/R$. The identity $g=2Au/(1+u)$ now gives the Borel–Carathéodory bound $|g(w)|\le 2A|w-c|/(R-|w-c|)$, at most $6A$ on $\overline{B}(c,3R/4)$. When $|s-c|\le R/2$, the circle of radius $R/4$ around $s$ stays in that closed disc. Cauchy's derivative formula gives $|g'(s)|\le6A/(R/4)=24A/R$. Letting $A$ decrease to $\log H$ gives $|h'(s)/h(s)|\le72\log H/r$, including when $H=1$.

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

The local R3 reading covers the bodies listed above, and [§4.10.9](#4109-uniform-polynomial-growth-in-the-half-plane-lfunction_polynomial_growth-and-exlf_growth) reads `lfunction_polynomial_growth` (`LandauZeroFreeBounds/ExceptionalZeroBounds/LGrowth.lean:53–71`) with witness $C=9$ (giving $B_C=1+\log420/\log2\approx9.7142$). The imported analytic proofs below them retain R2 [Lean], including the continuation and nonvanishing of Dirichlet $L$-functions, the Mathlib reciprocal and von Mangoldt identities (the call sites are LRight.lean:74–77,88–94,122–124), and the Laurent remainder bound `log_deriv_riemannZeta_add_inv_sub_bounded`. The Laurent bound is called at LogDerivRight.lean:12–13. The interfaces for the inverse, growth, and right-side estimates are NoZeroComplexOf.lean:25–35. The full `tail_contour` closure retains R2, with the exceptional-zero, zero-free-region and endpoint predecessors retaining their existing labels. The examples, holomorphic extension of the remainder, and the general distance corollary are [Expository]. See the [source ledger](../sources/SOURCES.md#p13-local-zero-expansion-in-tailbox).

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

**Reading status.** The complete proof bodies in `MSqCount`, including its direct counting suppliers, are [Lean, read] (local R3). The analytic inputs remain [Lean]: `pnt_progressions_relative_weak_holds` is assembled at `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTFinal.lean:16–24`, and `ExcBound` is stated at `src/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean:50–52` and supplied at `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:26–32`. The inner proofs of the relative progression estimate and the Siegel input remain [Open] for the book's reading record. The P13 dependency closure retains the corresponding R2 entries.

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
lossy Deuring–Heilbronn input `DeuringHeilbronnMB`. These named analytic
inputs and the partial-summation estimates cited below delimit the proof.
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

Take $\kappa=1/20$ and use model zero configurations. In the archive (`ex_negLD_bound`, `PNTExplNeg.lean:33`), $C_2=2C_0+100/7+C_3$, where §4.10.8 gives $C_0=180(\log(10100C_G)+3)$ and §4.10.9 reads the archive's actual growth witness $C_G=\max(9,6)=9$. Meanwhile `LogDerivRight.lean:14` defines $C_3=\max(\max(B,0),-\zeta'(1+\varepsilon/2)/\zeta(1+\varepsilon/2))>0$ from the retained R2 Laurent remainder bound, so $C_3=0$ is not realized by the archive's proof. Replacing $C_3>0$ by $0$ yields the explicit strict lower bound $C_2>C_2^{\mathrm{lb}}:=360(\log90900+3)+100/7\approx5204.59$. Because the four budget expressions below increase strictly with $(C_2,C_3)$, evaluating them at the baseline $(C_2^{\mathrm{lb}},0)$ gives explicit lower bounds for the archive's budgets at these parameters rather than admissible witnesses. With clearance $d$, left edge $\sigma$, height $H$, and $N=2C_2\log(8T)/d$, the four normalized budgets to be derived are
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

**What the constant means for §4.10.7.** The numerator constant of §4.10.7 is $C_2=2C_{\mathrm{loc}}+100/7+C_3$ (`ex_negLD_bound`, `PNTExplNeg.lean:33`). Section 4.10.9 reads the archive's actual witness $C_G=\max(9,6)=9$, which fixes $C_{\mathrm{loc}}=180(\log90900+3)\approx2595.15$. Meanwhile `LogDerivRight.lean:14` defines $C_3=\max(\max(B,0),-\zeta'(1+\varepsilon/2)/\zeta(1+\varepsilon/2))$ from the retained R2 Laurent remainder bound, and since $-\zeta'(\sigma)/\zeta(\sigma)=\sum_{n\ge1}\Lambda(n)n^{-\sigma}>0$ for $\sigma>1$, one has $C_3>0$ strictly. Consequently
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
| Retained deeper analytic suppliers | `log_deriv_riemannZeta_add_inv_sub_bounded` (called in `ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivRight.lean:12–14` for $C_R,C_3$); `ZeroSum` (`PNTZSumL`) with `LogDensityM` (`PNTDens`) and `DeuringHeilbronnMB` (`PNTDHB`); `twist_bound`, `zFRDirichlet`, `excBound`/`siegelLower` | Retained R2 [Lean] |

Reading `exLF_growth`, `lfunction_polynomial_growth` and `growthBound` closes the last `R2` supplier of `ex_local` (§4.10.8) and the polynomial-growth supplier of `TailBox` (§4.8.8), without promoting the remaining `R2` inputs tabulated in the final row. Local R3 records human-assisted source reading of the pinned archive, not a Lean kernel check. See the [source ledger](../sources/SOURCES.md#chapter-4-4109-uniform-polynomial-growth).

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
