# Chapter 7. Chains of theta lifts

In Chapter 6 we saw why Stepanov's proof over $\mathbb F_q(C)$ produces the exponent $1/2$: applying
$m \asymp \sqrt{Q}$ Hasse–Schmidt derivations $D_t^{(0)}, \dots, D_t^{(m-1)}$ to a Frobenius-power
polynomial creates $m$ independent layers of vanishing at rational points without multiplying the
leading pole degree by $m$, balancing $\frac{Q}{m} + m$ at $Q^{1/2}$ (Theorem 6.3) `[Stepanov1969]`,
`[Bombieri1973]` [Expository]. We also proved `each_unit_bound_statement`
(`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`, Theorem 6.6) [Lean, read],
showing that *if* a chain datum of length $m \asymp \sqrt{x}$ satisfies the 11 clauses of `SizeData₂`
(`src/Formalism/SizeWindowBrackets/SChain.lean:17`), then the exact same balance yields the Chebyshev
prime-sum bound of `core_gm`.

Now we face the central structural question of Part II: **what replaces $m$ derivatives when the
base is a number field $E$, and how can $m \approx \sqrt{x}$ automorphic operations be composed in a
chain with controlled analytic, spectral, and arithmetic behavior?**

Alpöge's timeline summarizes the mechanism in a single line (`remark.pdf` p. 4, item 8) [Paper;
remark p. 4]:

> "11/15/26: Iterated theta lifts $U(X_0) \to U(X_1) \to \dots \to U(X_m)$ between totally definite
> unitary groups, $\pi \mapsto \pi \boxplus \mu_j[t]$, wins multiplicity $m$. Time to take $m$ like
> $\sqrt{X}$..."

This chapter introduces **theta kernels and chains of theta lifts** from the ground up and connects
the classical theory directly to node `P17` (and its interface with `P7` and `P4`) of the Lean archive:

1. **Classical harmonic analysis and representation theory (`[Expository]`, citing `[Jacobi1829]`,
   `[Riemann1859]`, `[Tate1967]`, `[Weil1964]`, `[Howe1979]`, `[Rallis1984]`, `[KudlaRallis1994]`,
   `[GanTakeda2016]`):** Starting from Jacobi's theta series and Poisson summation, we work out
   explicit finite-field quadratic Gauss sums and binary quadratic Hecke theta lifts by hand, define
   bilinear kernel transforms, reductive dual pairs $(U(V), U(V')) \subset \mathrm{Sp}(W)$, the Weil
   representation, and the Howe correspondence, and prove in full detail the **two-step and $m$-step
   chain rule for integral kernel composition** — stating every sigma-finiteness, joint measurability,
   and Tonelli/Fubini absolute-integrability hypothesis explicitly rather than sweeping convergence
   under the rug.
2. **Formal P17/P7 chain architecture (`[Lean, read]` on the assembly and kernel-transfer layer,
   honestly auditing `structure` bundles):** We read line by line the archive's Weil-tensor model
   `WeilTensorModels.lean`, convergence and rapid-decay proofs `ThetaKernelFundamentalProperties.lean`,
   `TwistedThetaKernelMulCuspFormIntegrableOn.lean`, `LiftConvContGrowth.lean`, and
   `IntegrableThetaKernelProduct.lean`, spectral/Hecke parameter transfer along the chain
   (`ThetaChainUpwardLiftHeckeParamTransferred.lean`, `PairLiftOfHoweDualityBernstein.lean`,
   `FirstOccurrenceRuleThetaChainStepBothDirections.lean`, `ThetaChainUpwardInductionFixedMetric.lean`,
   `EvenCeil.lean`), and the top-level `P17` $\to$ `P7` $\to$ `P4` assembly
   (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean`, `LiftLambdaBound.lean`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean`,
   `SiegelEisensteinSecondTermHypotheses.lean`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean`, `DesWin.lean`, `TopPlug.lean`),
   mapping out where every remaining obligation of Chapters 8–11 plugs in.

---

## 7.1 Motivation

### 7.1.1 From Jacobi's theta series and Poisson summation to bilinear automorphic kernels

Every theta lift in modern automorphic forms descends from a single nineteenth-century identity of
Jacobi `[Jacobi1829]`: for $\tau = x + i y$ in the upper half-plane $\mathcal H = \{\tau \in \mathbb C : \Im\tau > 0\}$,
the classical **Jacobi theta series**
$$\vartheta(\tau) := \sum_{n \in \mathbb Z} e^{\pi i n^2 \tau}$$
satisfies the modular transformation law
$$\vartheta\Bigl(-\frac{1}{\tau}\Bigr) = \sqrt{-i\tau}\,\vartheta(\tau)$$
(with principal branch $\sqrt{y} > 0$ along $\tau = iy$, $y > 0$) [Expository]. Why does summing
$e^{\pi i n^2 \tau}$ over the lattice $\mathbb Z \subset \mathbb R$ produce a function invariant
(up to a half-integral weight factor) under $\tau \mapsto -1/\tau$? Because on the real line
$\mathbb R$, the Gaussian $\phi_y(t) := e^{-\pi y t^2}$ ($y > 0$) has Fourier transform
$$\widehat{\phi}_y(\xi) = \int_{-\infty}^{\infty} e^{-\pi y t^2 - 2\pi i t \xi}\,dt
= y^{-1/2}\,e^{-\pi \xi^2 / y} = y^{-1/2}\,\phi_{1/y}(\xi),$$
and **Poisson summation** $\sum_{n \in \mathbb Z} \phi_y(n) = \sum_{m \in \mathbb Z} \widehat{\phi}_y(m)$
turns the lattice sum at scale $y$ into the dual lattice sum at scale $1/y$!

In 1859, Riemann `[Riemann1859]` took one further step that revealed $\vartheta$ as an **integral
kernel coupling two groups**: integrating $\frac{1}{2}(\vartheta(iy) - 1) = \sum_{n=1}^\infty e^{-\pi n^2 y}$
against the multiplicative character $y^{s/2}\,\frac{dy}{y}$ of $\mathbb R_{>0} \cong O(1) \setminus \mathrm{GL}_1(\mathbb R)$
produces the completed zeta function $\pi^{-s/2}\Gamma(s/2)\zeta(s)$, transferring the modular
symmetry $y \leftrightarrow 1/y$ on $\mathcal H$ into the functional equation $s \leftrightarrow 1 - s$
on $\mathrm{GL}_1$! Look at what just happened in modern language (`[Weil1964]`, `[Howe1979]`):

1. We had **two commuting symmetry groups** acting on the same Schwartz space $\mathcal S(\mathbb R^d)$:
   - the **orthogonal (or unitary) group $G$** preserving a quadratic or Hermitian form $Q(v)$ on $V$,
     acting geometrically by $(\omega(g)\Phi)(v) = \Phi(g^{-1} v)$ (which commutes with summing over
     a $G(\mathbb Z)$-stable lattice $L \subset V$!); and
   - a **symplectic (or partner unitary) group $G'$** acting Fourier-analytically by scaling,
     quadratic phase multiplication $e^{\pi i b Q(v)}$, and partial Fourier transforms $\Phi \mapsto \widehat{\Phi}$
     (which preserve the lattice sum $\sum_{v \in L} (\omega(g, g')\Phi)(v)$ modulo $G'(\mathbb Z)$
     by **Poisson summation**!).
2. Forming the lattice sum
   $$\theta_\Phi(g, h) := \sum_{\xi \in V(F)} \bigl(\omega_\psi(g, h)\Phi\bigr)(\xi),
   \qquad (g, h) \in G(\mathbb A_F) \times G'(\mathbb A_F),$$
   produces a **bilinear automorphic kernel** left-invariant under $G(F) \times G'(F)$!
3. Integrating an automorphic form $f$ on $[G] := G(F) \setminus G(\mathbb A_F)$ against $\theta_\Phi(g, h)$,
   $$\Theta_\Phi(f)(h) := \int_{[G]} \theta_\Phi(g, h)\,\overline{f(g)}\,dg,$$
   transports $f$ from $G$ to an automorphic form $\Theta_\Phi(f)$ on $G'$!

### 7.1.2 Why iterate $m$ theta lifts between definite unitary groups?

Now ask how a theta lift $\Theta_{\Phi_j} : \mathcal A\bigl(U(X_j)\bigr) \to \mathcal A\bigl(U(X_{j+1})\bigr)$
can play the role of a single Hasse–Schmidt derivative $D_t^{(1)}$ in Stepanov's method (`remark.pdf`
pp. 1, 4) [Paper; remark pp. 1, 4] [Expository]:

1. **Compact quotients on the definite side (`DefiniteSideCondition`):** Suppose $E / F$ is our CM
   host extension from Chapter 4 ($F = E^+$ totally real of degree $2n$, $E = F(\sqrt{-d})$) and
   $X_j$ is a **totally positive-definite** Hermitian space over $E$ of rank $r_j$ (`HasSig ... r_j 0`
   at every infinite place $w$ of $F$, `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:172,184` [Lean, read]). Then at every
   archimedean place $w \mid \infty$, the real Lie group $U(X_j)(F_w) \cong U(r_j)$ is **compact**!
   Consequently, the global automorphic quotient
   $$[U(X_j)] := U(X_j)(F) \setminus U(X_j)(\mathbb A_F)$$
   is **compact** (in fact, at any open compact finite-adele level $K_f \subset U(X_j)(\mathbb A_{F,f})$,
   the double coset space $U(X_j)(F) \setminus U(X_j)(\mathbb A_{F,f}) / K_f$ is a **finite set** of
   Hermitian lattice classes, and automorphic forms of fixed archimedean weight are finite-dimensional
   algebraic spaces of functions on that finite genus!). Compactness buys two decisive analytic
   simplifications:
   - **Automatic absolute convergence:** Every continuous function on a compact space $[U(X_j)]$ is
     bounded and $L^1$ with respect to finite Haar measure, so iterating $m$ theta integrals along
     $U(X_0) \to U(X_1) \to \dots \to U(X_m)$ never diverges at cusps on the definite chain itself!
   - **Integral / $\mathcal O_E$-lattice structure:** Spaces of algebraic modular forms on definite
     unitary groups carry natural $\mathcal O_E$-lattices (`NuLat`, `src/Formalism/LocalRingCardinality/DataParams₂.lean:134` [Lean, read])
     and positive-definite Petersson/Hermitian metrics (`IsMet`, whose Schur uniqueness `ip_unique` is
     proved at `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainUpwardInductionFixedMetric.lean:25` [Lean, read]), making them ready-made
     inputs for Bost's Arakelov slope inequality!
2. **Rank growth $r_{j+1} = r_j + t$ and spectral splicing $\pi \mapsto \pi \boxplus \mu_j[t]$:**
   In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:25,33,35` and `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainUpwardLiftHeckeParamTransferred.lean:42` [Lean, read],
   the base space $X_0$ has rank $r_0 = r := k + m - 1$, each step adds a fixed odd rank increment
   $t = \mathrm{tAt} > 3m$ (`Ranks.t_odd`, `three_m_lt_t`, `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:52,56`), so
   $$\operatorname{rank}_E(X_j) = r + j\,t \qquad (0 \le j \le m),$$
   and step $j \to j + 1$ twists the Weil representation by an algebraic Hecke character $\mu_j$ of
   $E^\times \setminus \mathbb A_E^\times$ whose archimedean Harish-Chandra weights `(b_j, e_j)` sit
   in pairwise non-interlacing windows (`HCIn.hc`, `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:109` [Lean, read]:
   $b_j = B + 2 j\,\mathrm{hh}$, $e_j = b_j + \mathrm{hh}$ with $2\,\mathrm{hh} \ge t + 3$!). Under
   local Howe correspondence at split/unramified places (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PairLiftOfHoweDualityBernstein.lean:17`
   [Lean, read]), lifting from $U(r_j)$ to $U(r_j + t)$ sends a base-change Arthur/Langlands
   parameter $\Pi_j$ to $\Pi_j \boxplus \mu_j[t]$ (`speh`, `:57`), adjoining one fresh character-twisted
   block per lift!
3. **Seesaw / adjointness and non-vanishing:** Under the chain rule for integral kernels (Theorem 7.2
   and Proposition 7.3 below), the $m$-fold upward lift $x_m = (\Theta_m \circ \dots \circ \Theta_1)(u)$
   is dual with respect to the Petersson inner products to the composite downward adjoint
   $\Theta = \Theta_1^\ast \circ \dots \circ \Theta_m^\ast$:
   $$\langle y, x_m \rangle_{U(X_m)} = \langle \Theta(y), u \rangle_{U(X_0)}$$
   (`thetaChain_upward_induction_fixed_metric`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainUpwardInductionFixedMetric.lean:41–63`
   [Lean, read]), while Rallis's inner-product formula `[Rallis1984]`, `[KudlaRallis1994]` relates the
   norm-squared of each step to shifted Hecke $L$-values at the right of the critical strip (non-zero
   by `LNe`, `:43`) and, at primes inert in $K = \mathbb Q(\sqrt{-d})$, produces one additive unit of
   $p$-adic divisibility per step!

---

## 7.2 Worked examples

We work out two completely explicit low-dimensional calculations before giving the general definitions:
first, one-dimensional quadratic Gauss sums and the finite-field Weil transform over $\mathbb Z/3\mathbb Z$
and $\mathbb Z/5\mathbb Z$ (matching `gauss` and `eps` in `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:125,131`); second,
binary quadratic / rank-$1$ unitary theta lifts on $\mathbb Z[i] \subset \mathbb Q(i)$, illustrating
both Siegel–Weil ($L$-value matching) and Hecke spectral-parameter transfer.

### 7.2.1 One-dimensional Gauss sums and the finite Weil kernel over $\mathbb Z/3\mathbb Z$ and $\mathbb Z/5\mathbb Z$

Let $p$ be an odd prime and $\psi_p(x) := e^{2\pi i x / p}$ the standard additive character of
$\mathbb F_p = \mathbb Z/p\mathbb Z$. On the $p$-dimensional Hilbert space $\mathbb C[\mathbb F_p]$
with inner product $\langle f_1, f_2 \rangle = \sum_{x \in \mathbb F_p} f_1(x)\overline{f_2(x)}$,
consider the two basic unitary operators generating the finite metaplectic/Weil representation of
$\mathrm{SL}_2(\mathbb F_p)$ `[Weil1964]`, `[IwaniecKowalski2004]` [Expository]:

- **Quadratic phase (chirp) multiplication** by $T_b$ ($b \in \mathbb F_p$): $(M_b f)(x) := \psi_p(b x^2)\,f(x)$,
  with diagonal kernel $K_{M_b}(x, y) = \psi_p(b x^2)\,\delta_{x,y}$;
- **Normalized finite Fourier kernel** $F_p$:
  $$(F_p f)(y) := \frac{1}{\sqrt{p}} \sum_{x \in \mathbb F_p} \psi_p(x y)\,f(x),
  \qquad K_{F_p}(x, y) := \frac{1}{\sqrt{p}}\,\psi_p(x y).$$

Check unitarity and two-step kernel composition by hand:

1. **Two-step kernel of $F_p^2$:** Summing over the intermediate variable $y \in \mathbb F_p$ (the
   finite prototype of Theorem 7.2!) gives
   $$K_{F_p^2}(x, z) = \sum_{y \in \mathbb F_p} K_{F_p}(x, y)\,K_{F_p}(y, z)
   = \frac{1}{p} \sum_{y \in \mathbb F_p} \psi_p\bigl(y(x + z)\bigr) = \delta_{x, -z},$$
   so $(F_p^2 f)(z) = f(-z)$ and $F_p^\ast = F_p^{-1} = F_p^3$!
2. **Three-step Gauss-sum composition $F_p \circ M_1 \circ F_p$:** Composing $K_{F_p}(x, y) = p^{-1/2}\psi_p(xy)$,
   $M_1(y) = \psi_p(y^2)$, and $K_{F_p}(y, z) = p^{-1/2}\psi_p(yz)$ produces the composite kernel
   $$K(x, z) = \frac{1}{p} \sum_{y \in \mathbb F_p} \psi_p\bigl(y^2 + (x + z)y\bigr)
   = \frac{1}{p}\,\psi_p\bigl(-4^{-1}(x + z)^2\bigr) \sum_{y \in \mathbb F_p} \psi_p\Bigl(\bigl(y + 2^{-1}(x + z)\bigr)^2\Bigr)
   = \frac{G(1; p)}{p}\,\psi_p\bigl(-4^{-1}(x + z)^2\bigr),$$
   where $G(a; p) := \sum_{u \in \mathbb F_p} \psi_p(a u^2)$ ($a \in \mathbb F_p^\times$) is the
   **quadratic Gauss sum**! Notice how completing the square factored out the scalar Weil constant
   $\gamma_p := p^{-1/2} G(1; p)$ (`gauss` and `eps` in `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:125,131` [Lean, read]).
   Let us evaluate $G(1; p)$ explicitly at $p = 3$ and $p = 5$ (`[Davenport2000]`, Ch. 2):
   - **$p = 3$ ($p \equiv 3 \pmod 4$):** With $\omega = e^{2\pi i/3} = -\frac{1}{2} + i\frac{\sqrt{3}}{2}$,
     the squares mod $3$ are $0^2 = 0$, $1^2 = 1$, $2^2 \equiv 1$, so
     $$G(1; 3) = \omega^0 + \omega^1 + \omega^1 = 1 + 2\Bigl(-\frac{1}{2} + i\frac{\sqrt{3}}{2}\Bigr) = i\sqrt{3},
     \qquad \gamma_3 = \frac{G(1; 3)}{\sqrt{3}} = i!$$
   - **$p = 5$ ($p \equiv 1 \pmod 4$):** With $\zeta_5 = e^{2\pi i/5}$, the squares mod $5$ are
     $0^2 = 0$, $(\pm 1)^2 = 1$, $(\pm 2)^2 = 4$, so
     $$G(1; 5) = 1 + 2\zeta_5 + 2\zeta_5^4 = 1 + 4\cos\Bigl(\frac{2\pi}{5}\Bigr)
     = 1 + 4 \cdot \frac{\sqrt{5} - 1}{4} = \sqrt{5},
     \qquad \gamma_5 = \frac{G(1; 5)}{\sqrt{5}} = +1!$$
   In general, $\lvert G(1; p) \rvert^2 = \sum_{u, v \in \mathbb F_p} \psi_p(u^2 - v^2) = \sum_{s, v} \psi_p(s(s + 2v)) = p$
   (the $s = 0$ slice gives $p$ and every $s \neq 0$ slice sums to $0$), and Gauss's sign evaluation
   gives $G(a; p) = \bigl(\frac{a}{p}\bigr)\varepsilon_p\sqrt{p}$ with $\varepsilon_p = 1$ for
   $p \equiv 1 \pmod 4$ and $\varepsilon_p = i$ for $p \equiv 3 \pmod 4$ `[Davenport2000]`, `[IwaniecKowalski2004]`.

### 7.2.2 Binary quadratic norm form on $\mathbb Q(i)$: Siegel–Weil and Hecke theta lifts

Now step up to a rank-$1$ positive-definite Hermitian space $V = E$ over the imaginary quadratic CM
field $E = \mathbb Q(i)$ ($F = \mathbb Q$, involution $\sigma(z) = \bar z$), with Hermitian form
$\langle z, w \rangle = z\bar w$ and self-dual $\mathbb Z[i]$-lattice $L = \mathbb Z[i]$ (`Spc.IsHerm`
at $n = 1$, proven in the archive's own sanity check `example : HasSig (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 0 ∧ IsCartan 1 1`
at `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:596–602` [Lean, read]!) [Expository].

Here the definite unitary group at $\infty$ is the compact circle
$$U(1)(\mathbb R) = \{u \in \mathbb C^\times : u\bar u = 1\} = S^1,$$
and globally $[U(1)] = E^1 \setminus \mathbb A_E^1$ (where $E^1 = \{\alpha \in \mathbb Q(i)^\times : \alpha\bar\alpha = 1\}$
by Hilbert's Theorem 90 is isomorphic to $\mathbb A_E^\times / E^\times \mathbb A_{\mathbb Q}^\times$).
Pair $U(1)$ with $\mathrm{SL}_2$ (or $U(1, 1)$) via the norm form $N(a + b i) = a^2 + b^2$ on
$L = \mathbb Z[i]$:

1. **Trivial input $f = 1$ on $[U(1)]$ (the Siegel–Weil prototype):** For $\tau = x + iy \in \mathcal H$
   and the standard Gaussian $\Phi_\infty(z) = e^{-2\pi \lvert z \rvert^2}$ at $\infty$ times
   $\mathbf{1}_{\widehat{\mathbb Z}[i]}$ at finite primes, summing over $\lambda = a + bi \in \mathbb Z[i]$ gives
   $$\Theta_{\Phi}(1)(\tau) = \sum_{\lambda \in \mathbb Z[i]} e^{2\pi i (\lambda\bar\lambda)\tau}
   = \bigl(\vartheta(2\tau)\bigr)^2 = 1 + \sum_{n = 1}^{\infty} r_2(n)\,q^n \qquad (q = e^{2\pi i\tau}),$$
   where $r_2(n) = \#\{(a, b) \in \mathbb Z^2 : a^2 + b^2 = n\}$. Because $\mathbb Z[i]$ is a unique
   factorization domain with $\lvert \mathbb Z[i]^\times \rvert = 4$ ($1, -1, i, -i$) in which primes
   $p \equiv 1 \pmod 4$ split, $p \equiv 3 \pmod 4$ stay **inert** ($p \parallel n$ with odd exponent
   forces $r_2(n) = 0$!), and $2 = -i(1+i)^2$ ramifies, unique factorization of ideals in $\mathbb Z[i]$ gives
   $$r_2(n) = 4 \sum_{d \mid n} \chi_{-4}(d) \qquad (n \ge 1),$$
   where $\chi_{-4}$ is the primitive character mod $4$ (`[IwaniecKowalski2004]`, §14.1)! Taking the
   Mellin transform gives
   $$\sum_{n = 1}^{\infty} \frac{r_2(n)}{n^s} = 4\,\zeta_{\mathbb Q(i)}(s) = 4\,\zeta(s)\,L(s, \chi_{-4}).$$
   Look at two phenomena here that echo throughout Part II:
   - **Siegel–Weil identity (`[Weil1964]`, `[KudlaRallis1994]`):** Integrating the theta kernel against
     the constant function $1$ on $[U(1)]$ produces an **Eisenstein series** whose Fourier coefficients
     encode $L(s, \chi_{-4})$ (compare `dlogL` and `logDerivative_at_one_eq` for $L'/L(1, \chi_{-d})$ in
     `src/Formalism/LocalRingCardinality/DataParams₂.lean:69,127` [Lean, read]!);
   - **Inert-prime vanishing:** At every prime $p \equiv 3 \pmod 4$ **inert** in $\mathbb Q(i)$, the
     $p$-th Fourier coefficient $r_2(p) = 4(1 + (-1)) = 0$ vanishes identically!
2. **Nontrivial Hecke input $\chi_k$ on $[U(1)]$ (cuspidal lift and spectral-parameter transfer):**
   Replace $\Phi_\infty(z)$ by the harmonic polynomial Schwartz function $\Phi_{\infty,k}(z) = z^k e^{-2\pi\lvert z \rvert^2}$
   ($k \ge 4$ a multiple of $4$, say $k = 4$) and integrate against the unitary Hecke character on
   $\mathbb Q(i)$ (associated to the algebraic Hecke character $\psi_k((\lambda)) = \lambda^k$) given on
   nonzero principal ideals $(\lambda)$ ($\lambda \in \mathbb Z[i] \setminus \{0\}$; since $4 \mid k$,
   $u^k = 1$ on $\mathbb Z[i]^\times = \{\pm 1, \pm i\}$, so $\chi$ is everywhere unramified!)
   by $\chi((\lambda)) = (\lambda / \lvert \lambda \rvert)^k$. The constant term at $\lambda = 0$ vanishes
   ($0^k = 0$), and the theta lift
   $$\Theta_{\Phi_k}(\chi)(\tau) = \frac{1}{4}\sum_{\lambda \in \mathbb Z[i] \setminus \{0\}} \lambda^k\,e^{2\pi i (\lambda\bar\lambda)\tau}
   \in S_{k+1}\bigl(\Gamma_0(4), \chi_{-4}^{k+1}\bigr)$$
   is a **holomorphic cusp form** of weight $k + 1$ whose $L$-function equals the shifted Hecke
   $L$-function $L(s, \Theta_{\Phi_k}(\chi)) = L_{\mathbb Q(i)}(s, \psi_k)$ ($\psi_k((\lambda)) = \lambda^k$)!
   In Langlands parameters, the $1$-dimensional parameter of $\psi_k$ on $U(1)$ has been lifted to the
   $2$-dimensional dihedral cuspidal parameter $\operatorname{Ind}_{W_{\mathbb Q(i)}}^{W_{\mathbb Q}}(\psi_k)$
   on $\mathrm{GL}_2$ — the rank-$1 \to 2$ prototype of $\pi \mapsto \pi \boxplus \mu_j[t]$!

---

## 7.3 Definitions

We now give precise definitions of (1) general bilinear kernel integral transforms and classical
unitary dual pairs / Howe correspondence, and (2) the exact P17 and P7 Lean data structures that
represent them inside the archive.

### 7.3.1 Bilinear kernel integral transforms, unitary dual pairs, and the Howe correspondence

**Definition 7.1 (Bilinear kernel integral operators and formal adjoints).** Let $(X, \mathcal M_X, \mu)$
and $(Y, \mathcal M_Y, \nu)$ be sigma-finite measure spaces, and let $K : X \times Y \to \mathbb C$ be
a $(\mathcal M_X \otimes \mathcal M_Y)$-measurable function [Expository]:

1. For any measurable function $f : X \to \mathbb C$, the **domain of absolute convergence** of the
   integral transform $T_K f$ is the measurable set
   $$\Omega_{K, f} := \Bigl\{y \in Y : \int_X \lvert K(x, y)\,f(x) \rvert\,d\mu(x) < \infty\Bigr\},$$
   and we define the measurable function $T_K f : Y \to \mathbb C$ unconditionally by zero-extension off
   $\Omega_{K, f}$ (matching Mathlib's Bochner integral convention):
   $$(T_K f)(y) := \begin{cases} \displaystyle\int_X K(x, y)\,f(x)\,d\mu(x) & \text{if } y \in \Omega_{K, f},\\[6pt] 0 & \text{if } y \notin \Omega_{K, f}.\end{cases}$$
2. The **dual (seesaw / adjoint) kernel** is $K^{\ast}(y, x) := \overline{K(x, y)}$ on $Y \times X$, with
   integral operator $T_K^{\ast} := T_{K^{\ast}}$ given by $(T_K^{\ast} g)(x) = \int_Y \overline{K(x, y)}\,g(y)\,d\nu(y)$
   for $x \in \Omega_{K^{\ast}, g}$ and $0$ for $x \notin \Omega_{K^{\ast}, g}$.

**Definition 7.2 (Unitary reductive dual pairs, Weil representation, and global/local theta lifts).**
Let $F$ be a totally real number field, $E / F$ a quadratic CM extension with nontrivial Galois
involution $\sigma \in \operatorname{Gal}(E/F)$, $\mathbb A_F$ and $\mathbb A_E = \mathbb A_F \otimes_F E$
their adele rings, and $\psi : F \setminus \mathbb A_F \to \mathbb C^1$ the standard nontrivial
additive character (`IsStd`, `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:98` [Lean, read]) `[Weil1964]`, `[Howe1979]`,
`[KudlaRallis1994]` [Expository]:

1. **Hermitian / skew-Hermitian dual pair (`Spc.IsHerm`, `Spc.IsSkew`, `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:182,192`):**
   Let $(V, \langle \cdot, \cdot \rangle_V)$ be an $a$-dimensional $\sigma$-Hermitian space over $E$
   ($\sigma\langle x, y \rangle_V = \langle y, x \rangle_V$) and $(V', \langle \cdot, \cdot \rangle_{V'})$
   an $a'$-dimensional $\sigma$-skew-Hermitian space over $E$ ($\sigma\langle x', y' \rangle_{V'} = -\langle y', x' \rangle_{V'}$;
   multiplying by $\sqrt{-d} \in E^\times$ with $\sigma(\sqrt{-d}) = -\sqrt{-d}$ identifies any
   Hermitian space $X'$ with a skew-Hermitian space $V'$ having the exact same unitary group
   $U(V') = U(X')$!). On the $2aa'$-dimensional $F$-vector space $W := V \otimes_E V'$, the trace form
   $$\langle\!\langle v_1 \otimes v_1',\,v_2 \otimes v_2' \rangle\!\rangle_W
   := \operatorname{Tr}_{E/F}\bigl(\langle v_1, v_2 \rangle_V \cdot \sigma\langle v_1', v_2' \rangle_{V'}\bigr)$$
   is nondegenerate $F$-alternating, embedding the commuting isometry groups
   $$\bigl(U(V),\,U(V')\bigr) \subset \mathrm{Sp}(W)$$
   as a **reductive dual pair** (two subgroups of $\mathrm{Sp}(W)$ that are each other's full centralizers!).
2. **Splitting of the metaplectic cover and the theta kernel:** Choosing a pair of conjugate-symplectic
   / conjugate-orthogonal Hecke characters $(\chi_V, \chi_{V'})$ of $\mathbb A_E^\times / E^\times$
   whose restrictions to $\mathbb A_F^\times$ are $\eta_{E/F}^{a'}$ and $\eta_{E/F}^a$ splits Weil's
   metaplectic $\mathbb C^1$-cover $\mathrm{Mp}(W)(\mathbb A_F) \to \mathrm{Sp}(W)(\mathbb A_F)$ over
   $U(V)(\mathbb A_F) \times U(V')(\mathbb A_F)$ (`isUSplitting`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaKernelFundamentalProperties.lean:16`
   [Lean, read]), yielding a genuine **Weil representation** $\omega_{\psi, \chi}$ on the adelic
   Schwartz–Bruhat space $\mathcal S(\mathbb X(\mathbb A_F))$ for a Lagrangian polarization
   $W = \mathbb X \oplus \mathbb Y$. For any $\Phi \in \mathcal S(\mathbb X(\mathbb A_F))$, the
   **global theta kernel** is the absolutely convergent sum
   $$\theta_\Phi(g, h) := \sum_{\xi \in \mathbb X(F)} \bigl(\omega_{\psi, \chi}(g, h)\Phi\bigr)(\xi),
   \qquad (g, h) \in U(V)(\mathbb A_F) \times U(V')(\mathbb A_F),$$
   which is continuous and left-invariant under $U(V)(F) \times U(V')(F)$ (`theta_kernel_basic_properties`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaKernelFundamentalProperties.lean:14` [Lean, read]).
3. **Global theta lift and local Howe correspondence (`[Howe1979]`, `[Rallis1984]`, `[GanTakeda2016]`):**
   For a cusp form (or automorphic form on compact $[U(V)]$) $f$ on $[U(V)]$, whenever
   $g \mapsto \theta_\Phi(g, h)\,\overline{f(g)}$ is integrable on $[U(V)]$ with respect to Tamagawa /
   Haar measure $dg$, the **global theta lift** is
   $$\Theta_\Phi(f)(h) := \int_{[U(V)]} \theta_\Phi(g, h)\,\overline{f(g)}\,dg \qquad \bigl(h \in U(V')(\mathbb A_F)\bigr).$$
   Locally at each place $v$ of $F$, for any irreducible admissible representation $\pi_v$ of
   $U(V)(F_v)$, let $\Theta(\pi_v)$ be the maximal $\pi_v$-isotypic quotient $\bigl(\omega_{\psi_v, \chi_v} \otimes \widetilde{\pi}_v\bigr)_{U(V)(F_v)}$
   as a smooth $U(V')(F_v)$-representation; the **Howe duality theorem** (conjectured by Howe `[Howe1979]`,
   proved at archimedean places by Howe, for $p \neq 2$ by Waldspurger, and in all residue characteristics
   by Gan–Takeda `[GanTakeda2016]`) states that whenever $\Theta(\pi_v) \neq 0$, $\Theta(\pi_v)$ has a
   **unique irreducible quotient** $\theta(\pi_v)$, and $\pi_v \mapsto \theta(\pi_v)$ is injective on
   its non-vanishing domain!

### 7.3.2 Formal P17 and P7 structures (`WeilTensorModels`, `UnitaryGroupThirdPlaceHypotheses`, `HypsAlt`, `TopG`)

Let us inspect the exact declarations in `RH-lean-archive` that formalize node `P17` and wire it to `P7` and `P4`:

**Definition 7.3 (The Lean archive's P17 theta-correspondence and chain-family structures).**

1. **Adelic unitary groups, Witt towers, and Rallis/Siegel–Weil step relations (`src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:48,160,182,532,559,571,581,585`):**
   Over number fields `F, E` with involution `σ : E →ₐ[F] E`, `UA σ J` (`:48`) is the adelic unitary
   group of a matrix `J` over `AE F E = AF F ⊗[F] E`, with height `ht` and quotient height `qht` (`:57, 59`).
   `Spc F E n` (`:160`) packages `(J, L, θ, bas)` (form matrix, $\mathcal O_E$-lattice, archimedean
   Cartan involution, split local bases), verified Hermitian of signature $(r, s)$ by `Spc.IsHerm` (`:182`).
   `Plane.IsAdapted σ B H Y Y₁ i₀ i₁` (`:532`) records an orthogonal Witt decomposition $n = n_1 + 2$
   splitting off a hyperbolic plane `H.x, H.y` ($\langle x, x\rangle = \langle y, y\rangle = 0$,
   $\langle x, y\rangle = 1$) at both lattice and Cartan levels! On top of this, `LocalMatching` (`:581`)
   asserts local test-vector matching for admissible triples, and `ThetaIntegralsAgree` (`:585`)
   conjoins decay, nonzero proportionality-constant uniqueness and coinvariant vanishing (`OneConst` at
   `:503`, `Coinv` at `:508`), and the inductive
   rank-$+2$ $L$-factor recursion clauses `StepBeta` (`:559`) and `StepAlpha` (`:571`) involving
   `charL` and local Gauss/epsilon factors `stepFac` (`:552`, built from `gauss`, `:125`, and `eps`, `:131`) [Lean, read].
2. **Named-literature bundle (`UnitaryGroupThirdPlaceHypotheses`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:22–82`):**
   A `Prop`-valued `structure` bundling **60 fields**, mostly named literature propositions in
   `GlobalTheory.Published.*` — including `weilSiegelFormulaUnitary` (`:32`),
   `siegelWeilUnitaryConvergent` (`:33`), `doublingMethod` (`:34`), `bernsteinZelevinskyFiniteness` (`:36`),
   `bernsteinUnitaryProductIrreducible` (`:38`), `cuspRapidDecay` (`:31`), `casselmanWallach` (`:59`),
   `weilRepresentationUnitaryPair` (`:60`), `discreteSeriesClassification` (`:62`), `strongApproxSU` (`:63`),
   `greenRegularCharacters` (`:50`), and local Galois cohomology (`localFiniteness`, `localTateDuality`,
   `localEulerChar`, `:80–82`) [Lean, read].
3. **Definite-chain hypothesis bundle (`GlobalTheory.Fc.HypsAlt`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22–90`):**
   A `Type 1` `structure` parameterized by a residual class condition `N : FamClass → Prop` (instantiated
   as `Closed 𝒞 fun Fm _ => LinkN Fm`!) and `DefiniteSideCondition`. It packages **46 fields**: a family
   class `𝒜 : FamClass` of `FamP eps` families, a raw level/row selector `σ`, constants `cT, c30, cIc`,
   and **41 operational/structural clauses**
   connecting indefinite/definite realizations (`hRB`, `selJ`, `rRows`), twist compatibility (`hTw`),
   inert-prime row divisibility (`hDivG`, `hDcPtG`), class-number / Siegel–Minkowski mass formulas
   (`hn4`, `hInstR`, `hU`, `hG`), spectral decay (`hWu`), Weyl period bounds (`aPer0`, `aPerTw`),
   level-projection surjectivity (`zL`), and `nRest : N (D3 3 𝒜)` [Lean, read].
4. **Top-level connection predicate (`UpperTheory.Top.TopG`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:12`):**
   Asserts that for every window exponent $\lambda > 1$ (instantiated at $\lambda = 3/2$) and family
   requirement `G : FReq` (instantiated at `GChi ψ`), given host window supply `HostExW la G.req`
   (proved by `supplyChi` in Chapter 4!) and the $Ш^1$-hypothesis `HypV` on the class, the family
   class is `FamilyClassConnected (G.cls la)` — i.e., there exist uniform exponents `(eD, eL, ε₁)`
   such that for every $0 < \varepsilon < \varepsilon_1$, some `Fm : FamP eps` in `G.cls la` satisfies
   `ChainTied Fm eD eL K cHH eK CL x` across all large scales $x \in \mathrm{Fm.Win}$ [Lean, read]!

---

## 7.4 Lemmas and proofs

We now prove four load-bearing results with complete mathematical rigor:
(1) $d$-dimensional Poisson summation and lattice theta inversion;
(2) the **two-step and $m$-step chain rule for bilinear integral kernels** with explicit Fubini–Tonelli
integrability conditions, together with its specialization to compact definite unitary quotients and
to rapid-decay cusp forms (`lift_conv_cont_growth`, `integrable_core`);
(3) **spectral / Harish-Chandra parameter transfer and adjoint inner-product induction** along an
$m$-step chain (`HCIn.hc`, `upPar_of_transfer`, `thetaChain_upward_induction_fixed_metric`); and
(4) the top-level **P17 $\to$ P7 $\to$ P4 assembly** (`nonempty_hyps_definite_side_of_closed_bound`
$\to$ `every_character_of_green_v_win`).

### 7.4.1 Lattice Poisson summation and theta inversion

**Lemma 7.1 ($d$-dimensional Poisson summation and positive-definite lattice theta inversion).**
*Let $d \ge 1$, and let $f \in C(\mathbb R^d)$ satisfy the pointwise moderate-decay bounds*
$$\lvert f(x) \rvert \le C_1\,(1 + \lVert x \rVert)^{-d - \delta}, \qquad
\lvert \widehat{f}(\xi) \rvert \le C_2\,(1 + \lVert \xi \rVert)^{-d - \delta}$$
*for some constants $C_1, C_2 > 0$ and $\delta > 0$, where $\widehat{f}(\xi) := \int_{\mathbb R^d} f(x) e^{-2\pi i x \cdot \xi}\,dx$*
`[Jacobi1829]`, `[Weil1964]`, `[IwaniecKowalski2004]` [Expository]:

1. *(Poisson summation)* *Both series below converge absolutely and satisfy*
   $$\sum_{n \in \mathbb Z^d} f(n) = \sum_{m \in \mathbb Z^d} \widehat{f}(m).$$
2. *(Lattice theta transformation)* *Let $\Lambda = A \mathbb Z^d \subset \mathbb R^d$ ($A \in \mathrm{GL}_d(\mathbb R)$)
   be a full-rank lattice of covolume $\operatorname{vol}(\mathbb R^d/\Lambda) = \lvert \det A \rvert$,
   with dual lattice $\Lambda^\ast := \{\eta \in \mathbb R^d : \eta \cdot \lambda \in \mathbb Z\ \forall \lambda \in \Lambda\} = (A^\top)^{-1}\mathbb Z^d$.
   For every $y > 0$ and shift $v \in \mathbb R^d$, the lattice theta series
   $\Theta_\Lambda(y; v) := \sum_{\lambda \in \Lambda} e^{-\pi y \lVert \lambda + v \rVert^2}$ satisfies*
   $$\Theta_\Lambda(y; v) = \frac{y^{-d/2}}{\operatorname{vol}(\mathbb R^d / \Lambda)}
   \sum_{\eta \in \Lambda^\ast} e^{2\pi i v \cdot \eta}\,e^{-\pi \lVert \eta \rVert^2 / y}.$$

*Proof.*
(1) For $x \in [0, 1]^d$ and $n \in \mathbb Z^d$, the triangle inequality $1 + \lVert n \rVert \le 1 + \sqrt{d} + \lVert n + x \rVert \le (2 + \sqrt{d})(1 + \lVert n + x \rVert)$
gives $\lvert f(n + x) \rvert \le C_1 (2 + \sqrt{d})^{d+\delta} (1 + \lVert n \rVert)^{-d-\delta}$.
Comparing with $\int_{\mathbb R^d} (1 + \lVert u \rVert)^{-d-\delta}\,du < \infty$ in spherical coordinates
($\int_0^\infty (1 + r)^{-d-\delta} r^{d-1}\,dr < \infty$ since $\delta > 0$), the Weierstrass $M$-test
shows that $P(x) := \sum_{n \in \mathbb Z^d} f(n + x)$ converges **absolutely and uniformly** on $[0, 1]^d$
to a continuous $\mathbb Z^d$-periodic function! For each $m \in \mathbb Z^d$, uniform convergence on
the compact cube $[0, 1]^d$ justifies interchanging $\int_{[0,1]^d}$ and $\sum_{n \in \mathbb Z^d}$:
$$\widehat{P}(m) = \int_{[0, 1]^d} \Biggl(\sum_{n \in \mathbb Z^d} f(n + x)\Biggr) e^{-2\pi i m \cdot x}\,dx
= \sum_{n \in \mathbb Z^d} \int_{[0, 1]^d + n} f(u)\,e^{-2\pi i m \cdot u}\,du
= \int_{\mathbb R^d} f(u)\,e^{-2\pi i m \cdot u}\,du = \widehat{f}(m),$$
since $\mathbb R^d = \bigsqcup_{n \in \mathbb Z^d} ([0, 1)^d + n)$ up to Lebesgue-null boundaries and
$f \in L^1(\mathbb R^d)$. Because $\sum_{m \in \mathbb Z^d} \lvert \widehat{P}(m) \rvert = \sum_{m \in \mathbb Z^d} \lvert \widehat{f}(m) \rvert \le C_2 \sum_{m \in \mathbb Z^d} (1 + \lVert m \rVert)^{-d-\delta} < \infty$,
the Fourier series $Q(x) := \sum_{m \in \mathbb Z^d} \widehat{f}(m) e^{2\pi i m \cdot x}$ also converges
absolutely and uniformly to a continuous function on $(\mathbb R / \mathbb Z)^d$ having the exact same
Fourier coefficients as $P$. By $L^2((\mathbb R/\mathbb Z)^d)$-completeness of $\{e^{2\pi i m \cdot x}\}_{m \in \mathbb Z^d}$
and continuity of $P - Q$, we have $P(x) = Q(x)$ everywhere; evaluating at $x = 0$ gives (1).

(2) Apply (1) to the Schwartz function $f(u) := e^{-\pi y \lVert A u + v \rVert^2}$ ($u \in \mathbb R^d$),
which decays super-polynomially (so $\delta > 0$ is arbitrary). Substituting $w = \sqrt{y}(A u + v)$
($dw = y^{d/2}\lvert \det A \rvert\,du$) and factoring the $d$-fold product of 1D Gaussian integrals
$\int_{\mathbb R} e^{-\pi w_j^2 - 2\pi i w_j \zeta_j}\,dw_j = e^{-\pi \zeta_j^2}$ gives
$$\widehat{f}(m) = \int_{\mathbb R^d} e^{-\pi y \lVert A u + v \rVert^2 - 2\pi i u \cdot m}\,du
= \frac{y^{-d/2}}{\lvert \det A \rvert}\,e^{2\pi i v \cdot (A^\top)^{-1} m}\,e^{-\pi \lVert (A^\top)^{-1} m \rVert^2 / y}.$$
As $m$ runs over $\mathbb Z^d$, $\eta = (A^\top)^{-1} m$ runs bijectively over $\Lambda^\ast$, giving (2). $\square$

### 7.4.2 The chain rule for bilinear kernel composition: Fubini conditions and unitary-group convergence

Why must an honest account of iterated theta lifts state its measure-theoretic interchange hypotheses
explicitly? Because for general kernels $K_1(x, y)$ and $K_2(y, z)$, the iterated integral
$\int_Y K_2(y, z) \bigl(\int_X K_1(x, y) f(x)\,d\mu(x)\bigr)\,d\nu(y)$ need **not** equal
$\int_X \bigl(\int_Y K_1(x, y) K_2(y, z)\,d\nu(y)\bigr) f(x)\,d\mu(x)$ without absolute integrability
(as classic counterexamples on $[0, 1]^2$ or non-convergent Siegel–Weil ranges $r + s \le n$ show!).
We state and prove the exact chain rule first for general sigma-finite spaces, and then verify the
hypotheses both for **compact definite unitary quotients** and for **non-compact rapid-decay cusp
forms** (matching `lift_conv_cont_growth`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LiftConvContGrowth.lean:22`, and `integrable_core`,
`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableThetaKernelProduct.lean:131` [Lean, read]).

**Theorem 7.2 (Two-step and $m$-step chain rule for bilinear kernel transforms, with explicit Fubini–Tonelli hypotheses).**
*Let $(X_0, \mu_0), (X_1, \mu_1), \dots, (X_m, \mu_m)$ ($m \ge 2$) be sigma-finite measure spaces,
and for each $1 \le j \le m$ let $K_j : X_{j-1} \times X_j \to \mathbb C$ be $(\mathcal M_{X_{j-1}} \otimes \mathcal M_{X_j})$-measurable*
[Expository]:

1. *(Pointwise two-step composition, $m = 2$)* *Let $f : X_0 \to \mathbb C$ be $\mathcal M_{X_0}$-measurable,
   and fix $z \in X_2$ satisfying the **iterated Tonelli domination hypothesis***
   $$I(z) := \int_{X_1} \Biggl(\int_{X_0} \bigl\lvert K_1(x, y)\,K_2(y, z)\,f(x) \bigr\rvert\,d\mu_0(x)\Biggr) d\mu_1(y) < \infty.$$
   *Then:*
   - *(a)* *for $\mu_0$-almost every $x \in X_0$ on $\{f \neq 0\}$, $y \mapsto K_1(x, y) K_2(y, z)$
     lies in $L^1(X_1, \mu_1)$, so the **composite kernel**
     $K_{12}(x, z) := \int_{X_1} K_1(x, y)\,K_2(y, z)\,d\mu_1(y)$ is well-defined $\mu_0$-a.e. on
     $\{f \neq 0\}$ and $x \mapsto K_{12}(x, z) f(x)$ lies in $L^1(X_0, \mu_0)$ with
     $\int_{X_0} \lvert K_{12}(x, z) f(x) \rvert\,d\mu_0(x) \le I(z) < \infty$;*
   - *(b)* *for $\mu_1$-almost every $y \in X_1$ on $\{K_2(\cdot, z) \neq 0\}$, $(T_{K_1} f)(y) = \int_{X_0} K_1(x, y) f(x)\,d\mu_0(x)$
     converges absolutely, $y \mapsto K_2(y, z) (T_{K_1} f)(y)$ lies in $L^1(X_1, \mu_1)$, and the
     **exact kernel-composition identity** holds:*
     $$\bigl(T_{K_2}(T_{K_1} f)\bigr)(z)
     = \int_{X_1} K_2(y, z) \Biggl(\int_{X_0} K_1(x, y)\,f(x)\,d\mu_0(x)\Biggr) d\mu_1(y)
     = \int_{X_0} K_{12}(x, z)\,f(x)\,d\mu_0(x) = (T_{K_{12}} f)(z).$$
2. *($L^1$-global $m$-step chain and seesaw / adjoint identity)* *Suppose $f : X_0 \to \mathbb C$ and
   $h : X_m \to \mathbb C$ are measurable and satisfy the **$m$-fold joint Tonelli bound***
   $$\mathcal I_m(f, h) := \int_{X_0} \cdots \int_{X_m} \lvert f(x_0) \rvert
   \Biggl(\prod_{j = 1}^{m} \lvert K_j(x_{j-1}, x_j) \rvert\Biggr) \lvert h(x_m) \rvert\,d\mu_m(x_m)\cdots d\mu_0(x_0) < \infty.$$
   *Define inductively $K^{[1]} := K_1$ and $K^{[j+1]}(x_0, x_{j+1}) := \int_{X_j} K^{[j]}(x_0, x_j) K_{j+1}(x_j, x_{j+1})\,d\mu_j(x_j)$
   (where absolutely convergent, $0$ otherwise). Then the $m$-step iterated transform
   $f_m := (T_{K_m} \circ \dots \circ T_{K_1})(f)$ coincides $\mu_m$-a.e. on $\{h \neq 0\}$ with
   $T_{K^{[m]}} f$, and satisfies the **seesaw adjoint identity***
   $$\bigl\langle (T_{K_m} \circ \dots \circ T_{K_1})(f),\,h \bigr\rangle_{L^2(X_m, \mu_m)}
   = \int_{X_0 \times X_m} K^{[m]}(x_0, x_m)\,f(x_0)\,\overline{h(x_m)}\,d(\mu_0 \otimes \mu_m)
   = \bigl\langle f,\,(T_{K_1}^\ast \circ \dots \circ T_{K_m}^\ast)(h) \bigr\rangle_{L^2(X_0, \mu_0)}.$$
3. *(Verification on unitary theta chains: compact definite case and rapid-decay cuspidal case)*
   - *(Definite chain)* *If $[U(X_0)], \dots, [U(X_m)]$ are quotients of totally definite unitary
     groups over $E/F$, each $[U(X_j)]$ is compact with finite Haar measure $\mu_j([U(X_j)]) < \infty$,
     and for Schwartz test functions $\Phi_j$ the theta kernels $K_j(x_{j-1}, x_j) = \theta_{\Phi_j}(x_{j-1}, x_j)$
     are continuous (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaKernelFundamentalProperties.lean:14` `[Lean, read]`), hence bounded:
     $\sup_{[U(X_{j-1})]\times[U(X_j)]} \lvert \theta_{\Phi_j} \rvert = M_j < \infty$. Thus for every
     $f \in L^1([U(X_0)])$ and $h \in L^1([U(X_m)])$,
     $\mathcal I_m(f, h) \le \lVert f \rVert_{L^1} \lVert h \rVert_{L^1} \bigl(\prod_{j=1}^m M_j\bigr)\bigl(\prod_{j=1}^{m-1} \mu_j([U(X_j)])\bigr) < \infty$
     holds unconditionally!*
   - *(Non-compact moderate-growth $\times$ rapid-decay step, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LiftConvContGrowth.lean:22–76` `[Lean, read]`)*
     *On a general adelic unitary quotient $\mathcal F_T \subset U(T)(\mathbb A_F)$ of finite Haar
     volume $\mu_T(\mathcal F_T) < \infty$, if a kernel $\theta_\Phi(g, h)$ is continuous and satisfies
     uniform moderate growth $\lvert \theta_\Phi(g, h) \rvert \le C\,\mathrm{ht}_S(g)^A\,\mathrm{ht}_T(h)^A$
     and $G : U(T)(\mathbb A_F) \to \mathbb C$ is left-$U(T)(F)$-invariant, continuous, and of rapid
     decay ($\forall N,\ \exists B_N,\ \lvert G(h) \rvert\,\mathrm{qht}_T(h)^N \le B_N$), then for
     every $g$, $\lvert \theta_\Phi(g, h) G(h) \rvert \le C \cdot 2^A B_A\,\mathrm{ht}_S(g)^A$
     uniformly in $h \in \mathcal F_T$, so $h \mapsto \theta_\Phi(g, h) G(h)$ is integrable on
     $(\mathcal F_T, \mu_T)$, and $g \mapsto \int_{\mathcal F_T} \theta_\Phi(g, h) G(h)\,d\mu_T(h)$
     is continuous and of moderate growth $\le C \cdot 2^A B_A \mu_T(\mathcal F_T)\,\mathrm{ht}_S(g)^A$!*

*Proof.*
(1) Fix $z \in X_2$. Because $K_1, K_2(\cdot, z), f$ are measurable and $(X_0, \mu_0), (X_1, \mu_1)$
are sigma-finite, the function $F_z(x, y) := K_1(x, y) K_2(y, z) f(x)$ is $(\mathcal M_{X_0} \otimes \mathcal M_{X_1})$-measurable,
and **Tonelli's theorem** on the nonnegative measurable function $\lvert F_z \rvert : X_0 \times X_1 \to [0, \infty]$ gives
$$\iint_{X_0 \times X_1} \lvert F_z(x, y) \rvert\,d(\mu_0 \otimes \mu_1)
= \int_{X_1} \Biggl(\int_{X_0} \lvert F_z(x, y) \rvert\,d\mu_0(x)\Biggr) d\mu_1(y) = I(z) < \infty,$$
and simultaneously
$$\int_{X_0} \Biggl(\int_{X_1} \lvert K_1(x, y) K_2(y, z) \rvert\,d\mu_1(y)\Biggr) \lvert f(x) \rvert\,d\mu_0(x) = I(z) < \infty.$$
Therefore $F_z \in L^1(X_0 \times X_1, \mu_0 \otimes \mu_1)$! For every $x \in X_0$ with $f(x) \neq 0$
where the inner $y$-integral is finite (a full-measure subset of $\{f \neq 0\}$ since its integral
against $\lvert f(x) \rvert > 0$ is $I(z) < \infty$), $y \mapsto K_1(x, y) K_2(y, z)$ belongs to
$L^1(X_1, \mu_1)$, $\lvert K_{12}(x, z) f(x) \rvert \le \bigl(\int_{X_1} \lvert K_1(x,y) K_2(y,z) \rvert\,d\mu_1(y)\bigr)\lvert f(x) \rvert$
belongs to $L^1(X_0, \mu_0)$ with $L^1$-norm $\le I(z)$ (proving (a)), and **Fubini's theorem** on
$F_z \in L^1(\mu_0 \otimes \mu_1)$ equates the two iterated integrals:
$$\int_{X_1} K_2(y, z) \Biggl(\int_{X_0} K_1(x, y) f(x)\,d\mu_0(x)\Biggr) d\mu_1(y)
= \int_{X_0} \Biggl(\int_{X_1} K_1(x, y) K_2(y, z)\,d\mu_1(y)\Biggr) f(x)\,d\mu_0(x)
= \int_{X_0} K_{12}(x, z) f(x)\,d\mu_0(x),$$
proving (b)!

(2) By sigma-finiteness of $(X_0, \mu_0), \dots, (X_m, \mu_m)$, the $(m+1)$-fold product measure
$\mu_0 \otimes \dots \otimes \mu_m$ is associative and sigma-finite, and Tonelli's theorem implies that
$$\Phi(x_0, \dots, x_m) := f(x_0)\Biggl(\prod_{j=1}^m K_j(x_{j-1}, x_j)\Biggr)\overline{h(x_m)} \in L^1(X_0 \times \dots \times X_m, \mu_0 \otimes \dots \otimes \mu_m)$$
with $L^1$-norm $\mathcal I_m(f, h) < \infty$. Applying Fubini's theorem inductively $m - 1$ times —
integrating first in $x_0, x_1, \dots, x_{m-1}$ in that order gives $\int_{X_m} f_m(x_m)\overline{h(x_m)}\,d\mu_m$;
integrating first over the internal variables $(x_1, \dots, x_{m-1})$ produces $K^{[m]}(x_0, x_m)$;
and integrating in reverse order $x_m, x_{m-1}, \dots, x_1$ produces $\overline{(T_{K_1}^\ast \circ \dots \circ T_{K_m}^\ast)(h)(x_0)}$
since $\int_{X_j} K_j(x_{j-1}, x_j)\overline{g_j(x_j)}\,d\mu_j = \overline{\int_{X_j} \overline{K_j(x_{j-1}, x_j)} g_j(x_j)\,d\mu_j} = \overline{(T_{K_j}^\ast g_j)(x_{j-1})}$!
Equating all three Fubini slicings proves (2).

(3) The compact definite case is immediate because continuous functions on compact Hausdorff spaces
$[U(X_{j-1})] \times [U(X_j)]$ are bounded and measurable (`BorelSpace`, `SecondCountableTopology`).
For the non-compact rapid-decay claim, follow `lift_conv_cont_growth` (`src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LiftConvContGrowth.lean:39–59`
[Lean, read]): because $\theta_\Phi(g, \gamma h) = \theta_\Phi(g, h)$ for all $\gamma \in U(T)(F)$
(`hleft`), for every $h \in U(T)(\mathbb A_F)$ we may pick $\gamma \in U(T)(F)$ with
$\mathrm{ht}_T(\gamma h) \le 2\,\mathrm{qht}_T(h)$ (by definition of the infimum quotient height
`qht`, `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:59`, `norm_le_quotHeight_pow` at `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LiftConvContGrowth.lean:40`), obtaining
$$\lvert \theta_\Phi(g, h) \rvert = \lvert \theta_\Phi(g, \gamma h) \rvert
\le C\,\mathrm{ht}_S(g)^A\,(2\,\mathrm{qht}_T(h))^A = C \cdot 2^A\,\mathrm{ht}_S(g)^A\,\mathrm{qht}_T(h)^A.$$
Multiplying by $\lvert G(h) \rvert$ and applying rapid decay $\mathrm{qht}_T(h)^A \lvert G(h) \rvert \le B_A$
cancels $\mathrm{qht}_T(h)^A$ completely, giving the **uniform $h$-independent envelope**
$\lvert \theta_\Phi(g, h) G(h) \rvert \le C \cdot 2^A B_A\,\mathrm{ht}_S(g)^A$ (`hbd`, `:39–48`)!
Because $\mu_T(\mathcal F_T) < \infty$ (`vol_ne_top`, `:29`), the constant function $C \cdot 2^A B_A\,\mathrm{ht}_S(g)^A$
is integrable on $(\mathcal F_T, \mu_T)$, giving both $L^1(\mathcal F_T, \mu_T)$-integrability (`hint`, `:36`),
continuity in $g$ by Lebesgue's dominated convergence theorem (`continuousAt_of_dominated`, `:56`),
and the moderate-growth bound $C \cdot 2^A B_A \mu_T(\mathcal F_T)\,\mathrm{ht}_S(g)^A$ (`:75`). $\square$

*(Remark on the 4-factor Fubini step in `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableThetaKernelProduct.lean:131–198`: when the archive
unfolds a pair of theta kernels along a Witt/Jacobi block decomposition $n = \operatorname{rank} W + t$
using upper-triangular unipotent matrices `bl hn 1 y 0 1` of determinant $1$, `lintegral_bl` (`:52–68`
[Lean, read]) proves unimodular Haar invariance `addEquivAddHaarChar φ = 1` from $\det = 1$, and
`integrable_core` (`:131–199` [Lean, read]) applies the four-factor Tonelli identity `Fub4` (`:192`)
to bound $\int_y \int_h \int_U \int_k F(k, h, U, y)$ by the factored product
$(\int_h \lVert N(\mathrm{ww}\,x_0\,h) \rVert_e\,dI.m) \cdot (\int_y \lVert \eta(y) \rVert_e\,d\mu) < \infty$!)*

### 7.4.3 Spectral parameter transfer and inductive inner-product preservation along an $m$-step chain

How does the archive ensure that after $m \approx \sqrt{x}$ theta lifts
$$U(X_0) \longrightarrow U(X_1) \longrightarrow \dots \longrightarrow U(X_m),$$
neither the archimedean Harish-Chandra discrete-series parameters nor the unramified Satake / Hecke
parameters collide or collapse to zero? We read four files in `DecoratedLatticeProofs/` and
`ThirdPlaceSeries/` (`R3` / `[Lean, read]`) that prove this transfer cleanly:

**Proposition 7.3 (Non-interlacing Harish-Chandra schedule, local Hecke transfer, and $m$-step chain induction).**
*Fix `D : D7` with chain length $m = D.R.m$ and rank step $t = D.R.t$* [Lean, read]:

1. *(Verified non-interlacing archimedean schedule: `HCIn.hc`, `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:109–161`)* *Given
   `I : HCIn` satisfying `I.OK R` (`1 ≤ Del`, `t + 3 ≤ 2 * hh`, `(k - 2) * (4 * Del) ≤ U1`, `Uk ≤ -1`,
   `-B ≤ Uk`, `:100`), the rational sequences
   $u_i = u_{\mathbb Z}(i) + \frac{1}{2}$ ($0 \le i < k$), $v_i = (k - 2 - i)(4\,\mathrm{Del})$
   ($0 \le i < k - 1$), $b_j = B + 2 j\,\mathrm{hh}$, and $e_j = B + 2 j\,\mathrm{hh} + \mathrm{hh}$
   ($0 \le j < m$) strictly interlace on the base ($v_i < u_i$ and $u_{i+1} < v_i$) while maintaining
   a **strict gap $\ge (t + 3)/2$** along all $m$ lift steps:*
   $$e_j - b_j = \mathrm{hh} \ge \frac{t + 3}{2}, \qquad b_{j+1} - e_j = \mathrm{hh} \ge \frac{t + 3}{2},
   \qquad -b_0 < u_{k-1}.$$
   *Consequently, at every step $0 \le j < m$, the base parameters lie strictly "far from" the
   archimedean Rallis singular locus $(t + 1)/2$ (`FarFrom`, proved in `rulePar_of_pairPar` and
   `rulePar_step`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FirstOccurrenceRuleThetaChainStepBothDirections.lean:21,58`)!*
2. *(Local Satake / Weil–Deligne parameter splicing: `pairLift_of_howeDuality_bernstein_alt` and
   `upPar_of_transfer`)* *At every finite place $w \notin S$ split in $E/F$ (where $U(r_j)(F_w) \cong \mathrm{GL}_{r_j}(E_w)$
   with $r_0 = r < t$, `:25`), local theta lifting from $\mathrm{GL}_{r_j}$ to $\mathrm{GL}_{r_j + t}$
   coupled with `RecLawsH` sends the Weil–Deligne parameter of a row representation $\sigma$ to the
   direct sum with the $t$-dimensional twisted Speh / determinant parameter $\mu_i[t]$
   (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PairLiftOfHoweDualityBernstein.lean:17–58`), and globally transfers Hecke eigenvalues across
   $r_{k+1} = r_k + t$ whenever the upward theta integral `Step.up` is nonzero (`upPar_of_transfer`,
   `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainUpwardLiftHeckeParamTransferred.lean:42,46–67`).*
3. *($m$-step inductive adjointness and parameter propagation: `thetaChain_upward_induction_fixed_metric`,
   `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainUpwardInductionFixedMetric.lean:41–77`)* *Assume stage metric existence `hMet : MetEx D`
   and node gap `hgap : NodeGap D` (`src/Development/AbelianVarietyTheory/Definitions/LatticeFrames/ParBoundW.lean:24`). Suppose $s_0$ is a stage-$0$ localization with
   Hermitian metric `(ipD₀, ip₀)`, $u \in s_0.\mathrm{CC}(c)$ is nonzero with initial spectral parameter
   `IsPar u B`, every step $0 \le k < m$ has non-vanishing $L$-value `LNe c (c.chT (k + 1)) (chainPar c B k)`
   (ensuring non-vanishing of the single-step lift `StepUp D`), and `Reach c s₀ k s Θ` ($k \le m$)
   records a $k$-step downward chain operator $\Theta : s.\mathrm{CC}(c) \to s_0.\mathrm{CC}(c)$. Then
   for any admissible metric `(ipD, ip)` on $s$, there exists $x_k \in s.\mathrm{CC}(c)$ such that:*
   $$\forall y \in s.\mathrm{CC}(c),\quad \mathrm{ip}(y, x_k) = \mathrm{ip}_0(\Theta y, u)
   \qquad\text{and}\qquad \mathrm{IsPar}\,x_k\,(\mathrm{chainPar}\,c\,B\,k).$$

*Proof.*
(1) Every inequality in `HCIn.hc` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:114–161`) is immediate integer arithmetic: since
$\mathrm{Del} \ge 1$, for $i = 0$ we have $v_{\mathbb Z}(0) = (k - 2)(4\,\mathrm{Del}) \le U_1 = u_{\mathbb Z}(0)$,
for $i = k - 1$ there is no $v_{k-1}$, and for $0 < i < k - 1$ we have
$u_{\mathbb Z}(i) = (k - 1 - i)(4\,\mathrm{Del}) - 1 - \delta_{i-1}\mathrm{Del} \ge (k - 2 - i)(4\,\mathrm{Del}) + 3\,\mathrm{Del} - 1 \ge v_{\mathbb Z}(i)$,
so $v_i < u_{\mathbb Z}(i) + \frac{1}{2} = u_i$. Similarly $u_{\mathbb Z}(i+1) + 1 \le (k - 2 - i)(4\,\mathrm{Del}) = v_{\mathbb Z}(i)$
gives $u_{i+1} < v_i$, and $2\,\mathrm{hh} \ge t + 3$ gives $e_j - b_j = \mathrm{hh} \ge \frac{t+3}{2}$
and $b_{j+1} - e_j = \mathrm{hh} \ge \frac{t+3}{2}$. In `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FirstOccurrenceRuleThetaChainStepBothDirections.lean:23–35`,
if any entry $y$ of the base parameter satisfied $y = \frac{t+1}{2}$, then $y + a_T$ would violate
`FarFrom aT ((t+3)/2)` ($\lvert (y + a_T) - a_T \rvert \ge \frac{t+3}{2} > \frac{t+1}{2}$), a contradiction
by `linarith`!

(2) In `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PairLiftOfHoweDualityBernstein.lean:19–58`, non-orthogonality `hpair` implies the $\sigma$-isotypic
space is nonzero (`hne`), `R.rank_add_five_le` gives $r < t$ (`hrt`), `theta_lift_general_linear`
identifies the untwisted $\mathrm{GL}_{r + t}$ theta lift $\pi'$ with the parabolic induction
$\mathrm{prod}_2(\sigma, \det_{\mu, t})$, and injectivity of `(T.e w)` equates the Weil–Deligne
parameters `liftPar = (X.rc ...).lpSum (speh ... R.t)`. In `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainUpwardLiftHeckeParamTransferred.lean:46–67`,
taking complex conjugates under the integral sign (`← integral_conj`, `:56`) expresses
$\overline{(p.\mathrm{up}\,\varphi\,y)(x)} = \int_{s.\mathrm{fd}} \theta_{p.\omega}(g, x, p.\mathrm{pt}\,\varphi)\,\overline{y(g)}\,ds.\nu$,
and for every finite place $w_0 \notin c.S$ where the Fock lattice vector is the unramified vacuum
(`fock_vectors_lattice_vacua_off_finite_set`, `:67`), `thetaIntegral_conjCuspForm_parameterTransfer`
transfers the spherical Hecke parameter!

(3) Follow the induction in `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainUpwardInductionFixedMetric.lean:46–63`!
- **Base case $k = 0$ (`Reach.zero`, $\Theta = \mathrm{id}$, $s = s_0$):** First prove metric
  uniqueness `ip_unique` (`:25–39`): because pure tensors span $s.\mathrm{M}$ (`PiTensorProduct.span_tprod_eq_top`),
  any nonzero $z \in s.\mathrm{CC}(c)$ evaluates non-trivially on some pure tensor $v_\otimes = \bigotimes_\tau v_\tau \neq 0$
  (`exists_tprod_ne_zero_of_cc`, `:14`). Both admissible metrics `(ipD, ip)` and `(ipD₀, ip₀)` agree
  on pure tensors (`ipD v_⊗ v_⊗ = ipD₀ v_⊗ v_⊗ ≠ 0` by positivity `posD`) and satisfy Schur
  proportionality `ip x y * ipD v_⊗ v_⊗ = ...`, so cancelling `ipD v_⊗ v_⊗ ≠ 0` gives
  `ip y u = ip₀ y u` for every $y$! Taking $x_0 := u$ satisfies `ip y x₀ = ip₀ (id y) u` and `IsPar u B`.
- **Inductive step $k \to k + 1$ (`Reach.step`, $\Theta_{k+1} = \Theta_k \circ p.\mathrm{dn}$):**
  Pick a stage-$k$ metric `(ipD, ip)` via `hMet`. By the induction hypothesis at step $k$, there
  exists $x_k \in s.\mathrm{CC}(c)$ with `ip z x_k = ip₀ (Θ_k z) u` for all $z$ and
  `IsPar x_k (chainPar c B k)`. Because $k < m$, hypothesis `hL k` supplies the non-vanishing
  $L$-factor `LNe c (c.chT (k + 1)) (chainPar c B k)`. Feeding `x_k` and `hL k` into the single-step
  upward theorem `hSU` (`StepUp D`, `:57`) produces $x_{k+1} \in s'.\mathrm{CC}(c)$ satisfying both
  $$\mathrm{ip}'(y, x_{k+1}) = \mathrm{ip}(p.\mathrm{dn}\,y, x_k) = \mathrm{ip}_0\bigl(\Theta_k(p.\mathrm{dn}\,y), u\bigr) = \mathrm{ip}_0(\Theta_{k+1} y, u)$$
  for all $y \in s'.\mathrm{CC}(c)$ and `IsPar x_{k+1} (chainPar c B (k + 1))` (`chainPar_succ`, `:62`)! $\square$

### 7.4.4 Top-level P17 $\to$ P7 $\to$ P4 assembly (`HypsAlt` $\to$ `TopG` $\to$ `EveryCharacter`)

Finally, we connect `P17` all the way back to Part I (`EveryCharacter`) by reading the four short
assembly files `SiegelEisensteinSecondTermHypotheses.lean`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean`, `DesWin.lean`, and
`TopPlug.lean` in full (`R3` / `[Lean, read]`).

**Theorem 7.4 (From definite-unitary theta hypotheses and `VWin` to `TopG` and `EveryCharacter`).**
*Assume the seven packages:*
- *`P : UnitaryGroupThirdPlaceHypotheses` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:22`),*
- *`F : ThetaLocalInputs`,*
- *`hA : ThetaIntegralsAgree` and `hM : LocalMatching` (`src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:585,581`),*
- *`hX : CovolumeBoundOfX` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LiftLambdaBound.lean:60`),*
- *`hL : RecTExists` (partial local Langlands, node `P15`, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:78`), and*
- *`hV : VWin` (the Tate–Shafarevich window bound, node `P12`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49`).*

*Then `Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)` holds,
`TopG` holds, `ZeroFreeAll` holds, and `UpperTheory.EveryCharacter` holds!*
*(Lean: `nonempty_hyps_definite_side_of_closed_bound` and
`every_character_of_theta_integrals_local_matching`,
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44,69`;
`shape_closed_link_n_of_green`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33`;
`topDesWin`, `src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean:11`;
`zero_free_all_of_green_v_win` and `every_character_of_green_v_win`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12,16`.)* [Lean, read]

*Proof.* Follow the four-stage wiring diagram in the Lean proof terms:

1. **Building `HypsAlt` (`nonempty_hyps_definite_side_of_closed_bound`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44–68`):**
   - Unramified Howe duality (`howeUnram_holds`) + convergent unitary Siegel–Weil (`P.siegelWeilUnitaryConvergent`)
     imply separation of functionals (`hS`, `:48`).
   - Combining `hS` with real Howe duality (`F.howeDualityReal`), cuspidal Green characters (`P.greenCuspidal`),
     the Hecke–Tate functional equation (`C.fe`), `ThetaIntegralsAgree` (`hA`), and `LocalMatching` (`hM`)
     assembles rational row test vectors (`hRat : S0.RowRat`, `:49`), fits the constant function
     (`hFit : S0.ConstantFunctionFits`, `:51`), and produces an evaluation-grid threshold `CF1` (`evaluation_grid_of_join`, `:52`).
   - Discrete-series covers, Harish-Chandra modules, cusp rapid decay, Casselman–Wallach, and ray
     class fields (`P.*`) produce a second threshold `CF0` (`rowFun_at_gridA_alt`, `:55`).
   - Taking `max CF0 CF1`, applying partial local Langlands `hL : RecTExists` and `hX : CovolumeBoundOfX`
     to link the covolume/height bundles (`hL3`, `:65`), and invoking `hypotheses_nonempty_of_unramified_exponents_alt`
     (`:68`) inhabits `Nonempty (HypsAlt S0.NL DefiniteSideCondition)` (where `S0.NL` comes from `P.nLink`
     via `boundAtTwoThree_linked_of_recT`, `:73`).
2. **Wiring `HypsAlt` + Green's classification into the nine chain links (`shape_closed_link_n_of_green`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33–55`):**
   Given `hGreen : GlobalTheory.GLq.Green` (obtained from `P.greenRegularCharacters` via
   `green_of_regular`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumRangeEqRoots.lean:225`) and the fields of `HypsAlt`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean`
   derives:
   - `hDIV`: the divisibility link `Closed (D3 3 𝒜) ... LinkDIVt` (`:47`, from `link_brest_alt`,
     `wire_sel_alt`, twisted admissibility `hA2`, and spectral decay `hC5`);
   - `hE`: smooth design existence `DesignExists` (`:50`, from `hEx`, `hTu`, class-number formula `hn4`,
     and `hLit`);
   - `closed_linkEta_of_duty` (`LinkEta`), `closed_linkIRR_of_join_count hGreen` (`LinkIRR`),
     `link_alt_alt_alt` (`SmallLevelRankEq`), `hgl.1` (lattice rank `NuFullF ∧ J.MuRank`),
     `closed_linkG_of_duty` (`LinkG`), `link_alt_alt_bis` (`LinkS`), and `hgl.2` (`LinkGLOBAL`),
     feeding all nine into `topDesWin` (`:52–55`)!
3. **Converting the nine links + `HypV` into `FamilyClassConnected` (`topDesWin`, `src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean:11–31`):**
   Intersecting the eventual $\varepsilon$-thresholds `min ε1 ε3` of `DesignExists` and the nine
   `Closed` links produces, for every $0 < \varepsilon < \min(\varepsilon_1, \varepsilon_3)$, a family
   `Fm : FamP eps` in `G.cls la`; combining `HypV` (supplied by `VWin`!) with `LinkN` and
   `SmallLevelRankEq` via `divinN_of_hypV` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:117`, node `P11`, Chapter 10) discharges
   the congruence-to-$Ш^1$ hypothesis of `aD` (`LinkDIVt`), and `aGL` (`LinkGLOBAL`) outputs
   `ChainTied Fm eD eL ...` across `Fm.Win`, establishing `TopG`!
4. **Closing to `EveryCharacter` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12–18`):**
   `zero_free_all_of_green_v_win` plugs `TopG` and `fun ψ => supplyChi ψ (hV ψ)` (Theorem 4.9, at
   window exponent `la := 3 / 2`) into `zeroFreeAll_of_topG` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:26`, Theorem 3.7
   + Corollary 5.6), yielding `ZeroFreeAll`, and `imprimitive` (`src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5`, Proposition 2.2)
   extends zero-freeness on $\Re s > 1/2$ to every Dirichlet character (`UpperTheory.EveryCharacter`)! $\square$

---

## 7.5 Remarks and formalization notes

### 7.5.1 Honest audit of formalization scope in P17: `structure` bundles, `UnusedSlot72`, and unread cones

Reading the actual Lean source of node `P17` brings two essential realities into sharp focus [Expository]:

1. **How hypotheses are packaged vs. discharged:** Inside `SiegelEisensteinSecondTermHypotheses.lean`,
   `LiftConvContGrowth.lean`, `IntegrableThetaKernelProduct.lean`, `ThetaChainUpwardLiftHeckeParamTransferred.lean`,
   and `ThetaChainUpwardInductionFixedMetric.lean` — all of which we read in full and verified free of
   `sorry` (`R3` / `[Lean, read]`) — major representation-theoretic theorems (`CuspRapidDecay`,
   `SiegelWeilUnitaryConvergent`, `CasselmanWallach`, `HoweUnram`, `ThetaIntegralsAgree`, `LocalMatching`,
   `StepUp`) appear **as `structure` fields or explicit theorem hypotheses**! Where are those `Prop`
   fields actually *proved* in the archive? One layer higher up the assembly chain, in
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215,810`
   (`P2` / `P18`, import cone **151,285 modules**) [Lean], which proves `every_character_of_literature_of_vWin`
   from `OpenLiteratureStatements` and passes the proved `Prop` terms into
   `every_character_of_theta_integrals_local_matching`!
   - Thus every `GlobalTheory.Published.*` field of `UnitaryGroupThirdPlaceHypotheses` *is* formally
     inhabited somewhere inside the 175,187-file archive with zero axioms beyond Lean's standard three
     `[Lean]`, `[Community]`;
   - **however**, nobody (including us) has read the 151,285-module proof cone behind those `Prop`s,
     and — as noted in `notes/proof-map.md` (node `P18`) and Chapter 13 — whether each custom `Prop`
     definition `GlobalTheory.Published.<Name>` faithfully states the published theorem of that name
     remains `[Open]` until audited declaration by declaration!
2. **A fossil inside `UnitaryGroupThirdPlaceHypotheses` (`UnusedSlot72`):** Look at line 74 of
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean`:
   ```lean
   siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation
   siegelEisensteinSimplePole : _root_.GlobalTheory.Published.UnusedSlot72
   schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
   ```
   Field #52, named `siegelEisensteinSimplePole`, has type `GlobalTheory.Published.UnusedSlot72`
   (`:74`) [Lean, read] — and indeed `SiegelEisensteinSecondTermHypotheses.lean` never projects
   `P.siegelEisensteinSimplePole`! Like `ErrorFormsWeakWindowsFalse.lean` in Chapter 5, this unused
   field is harmless to logical soundness (if a hypothesis of an implication is proved — even as `True` —
   and never used, the conclusion is unaffected), while illustrating vividly why human mathematical
   digestion must inspect definitions rather than trusting field names!

### 7.5.2 Structural map of the rest of Part II (Chapters 8–11)

Look back at lines 29–31 of `topDesWin` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean:11–31`, Step 3 of Theorem 7.4 above):
```lean
have hD := aD hT hDG aE (divinN_of_hypV Fm h0 (hV Fm (h2 Fm hc.1.1)) aN aZ)
exact ⟨Fm, h2 Fm hc.1.1, aGL hT hDG hCh ⟨aG, aS hT, aI, hD, ...⟩⟩
```
That two-line proof term is the **table of contents for Chapters 8–11** [Lean, read]:

- **Chapter 8 (`P8`, Divisibility at inert primes):** Opens `hDIV` / `LinkDIVt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:47`)
  and `WeilJacquetShalikaLaw.Conclusion1` (`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97` [Lean]),
  explaining why at primes of the host inert in $K = \mathbb Q(\sqrt{-d})$, supersingular CM evaluation
  and $p$-adic analysis of the $m$ theta kernels force the columns of the chain to vanish modulo high
  powers of $p$.
- **Chapter 9 (`P9`–`P10`, Heights, slopes, and near-orthogonality):** Opens `SlopeIneq`
  (`src/Formalism/HarderNarasimhan/Statement.lean:91` [Lean]), `aG : LinkG Fm`, `aS hT : LinkS Fm C0`
  (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:138,152` [Lean]), and `aGL : LinkGLOBAL`,
  showing how Chowla–Selberg periods, Siegel–Minkowski mass ratios (`hU`, `hG`), and Rallis/Bessel
  inner products make distinct chain words nearly orthogonal ($\text{defect} \le \exp(-x^{\varepsilon/8})$)
  and assemble `ChainTied`.
- **Chapter 10 (`P11`, Congruence modules to Tate–Shafarevich groups):** Opens `aN : LinkN Fm`
  (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:45` [Lean]), `CutCoreUnit.main`
  (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:44` [Lean]),
  and `divinN_of_hypV` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:117` [Lean]),
  bounding the excess congruence loss of each lift via Fitting ideals on generalized matrix algebras
  in terms of Selmer and $Ш^1\bigl(G_{E,S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e)\bigr)$ lengths.
- **Chapter 11 (`P12`, The window bound `VWin`):** Opens `hV : VWin` (`vwin_of_row`,
  `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4` [Lean],
  90% of the archive by import cone), splitting $Ш^1$ into $\ell = 2$, minus (Euler systems / Bernoulli
  numbers), and plus ($U(3)$ congruences and residually reducible modularity) parts.

### 7.5.3 Masullo's counterpart

Readers comparing the two November 2026 manuscripts will notice that **Chapter 2 of Masullo's draft
is titled "Adelic $\theta$-functions" (pp. 57–116)** [Paper; Masullo p. 57]. Despite the identical
word, **Masullo's $\theta$-functions are a completely different mathematical object from the
unitary-pair theta kernels of this chapter** (`notes/proof-map.md`, node `P17`) [Expository]:

- In **Section 2.2 ("Global adelic $\theta$-functions", pp. 74–97, specifically Lemma 2.2.2.1 on
  pp. 77–78)**, Masullo associates to a one-variable Schwartz–Bruhat function $f \in \mathcal S(\mathbb A_F)$
  on the adele ring of a number field $F$ its multiplicative $F^\times$-orbit sum on the idele group
  $\mathrm{GL}_1(\mathbb A_F)$ [Paper; Masullo pp. 74, 77–78]:
  $$\Psi_F(f)(g, x) := \sum_{\xi \in F^\times} f\bigl(g(\xi + x)\bigr), \qquad (g, x) \in \mathrm{GL}_1(\mathbb A_F) \times \mathbb A_F,$$
  calling the $F^\times$-invariant function $g \mapsto \Psi_F(f)(g, 0) = \sum_{\xi \in F^\times} f(g\xi)$
  on the idele class group $C_F = \mathrm{GL}_1(\mathbb A_F) / F^\times$ a "global adelic $\theta$-function"
  (whose global idelic Mellin transform in his Chapter 3, pp. 122–127, produces the Hecke $L$-functions
  of Tate's thesis `[Tate1967]`) [Paper; Masullo pp. 74–78, 122–127].
- Notice what is **absent** in Masullo's Chapter 2: there is no symplectic space $W$, no quadratic or
  Hermitian norm form $\langle \xi, \xi \rangle$ in the exponent (his sum is linear in $\xi \in F^\times$,
  corresponding in classical terms to the degenerate hyperbolic dual pair $(\mathrm{GL}_1, \mathrm{GL}_1)$
  inside $\mathrm{Sp}_2$, i.e. ordinary Tate–Poisson summation $\sum_{\xi \in F} f(g\xi) = \lvert g \rvert_F^{-1}\sum_{\xi \in F} \widehat{f}(g^{-1}\xi)$!),
  no higher-rank unitary groups $U(X_j)$, no Howe correspondence, and no chain of lifts!

---

## 7.6 Lean counterpart for this chapter

Every Lean declaration in the first table below was read in full, proof body included (`R3` / `[Lean, read]`).
Declarations in the second table are cross-chapter interfaces (`P8`–`P16`, `P18`) read at statement
level (`R2` / `[Lean]`) and opened in Chapters 8–13.

### 7.6.1 Weil-tensor models, kernel convergence, spectral transfer, and P17 $\to$ P4 assembly (nodes P17, P7, P4)

| Declaration | File:line | Mathematical content / role in Sections 7.3–7.4 | Tag |
|---|---|---|---|
| `AE`, `UA`, `ht`, `qht`, `IsStd`, `gauss`, `eps`, `Base`, `Spc`, `HasSig`, `IsCartan`, `Spc.IsHerm`, `Spc.IsSkew`, `Plane.IsAdapted`, `stepFac`, `StepBeta`, `StepAlpha`, `LocalMatching`, `ThetaIntegralsAgree` | `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:20,48,57,59,98,125,131,140,160,172,175,182,192,532,552,559,571,581,585` | Definition 7.3(1) & Example 7.2: adelic unitary groups, heights, local Gauss/$\varepsilon$-factors, Hermitian/skew-Hermitian lattice spaces, Witt hyperbolic-plane splitting, local matching, and rank-$+2$ $L$-factor step identities. | [Lean, read] |
| `GlobalTheory.ThKBasic.theta_kernel_basic_properties`, `GlobalTheory.T.theta_kernel_fundamental_properties` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaKernelFundamentalProperties.lean:14,42` | Definition 7.2(2) & Theorem 7.2(3): continuity, $U(V)(F) \times U(V')(F)$-invariance, and moderate growth of global pair theta kernels from `isUSplitting`. | [Lean, read] |
| `GlobalTheory.Unf.LiftRapid.lift_conv_cont_growth` | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LiftConvContGrowth.lean:22` | Theorem 7.2(3): uniform envelope $\lvert\theta_\Phi(g,h) G(h)\rvert \le C 2^A B_A \mathrm{ht}_S(g)^A$ from moderate growth $\times$ rapid decay, proving $L^1(\mathcal F_T)$-integrability, continuity, automorphy, and moderate growth of $\Theta_\Phi(G)$. | [Lean, read] |
| `GlobalTheory.CuspThetaConvX.integrableOn_theta_kernel_mul_cusp_form`, `GlobalTheory.T.twisted_theta_kernel_mul_cusp_form_integrableOn` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedThetaKernelMulCuspFormIntegrableOn.lean:12,34` | Theorem 7.2(3): fiberwise $L^1$ integrability of twisted theta kernel times cusp form along grid steps $i < m$. | [Lean, read] |
| `det_bl`, `lintegral_bl`, `inner_eq`, `integrable_core`, `GlobalTheory.T.integrable_theta_kernel_product` | `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableThetaKernelProduct.lean:27,52,83,131`; `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableThetaKernelProductStatement.lean:15` | Theorem 7.2 (remark): unimodular Haar invariance under block-unipotent shifts and 4-factor Tonelli (`Fub4`) integrability of composite kernel products. | [Lean, read] |
| `UpperTheory.One.M.pairLift_of_howeDuality_bernstein_alt` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PairLiftOfHoweDualityBernstein.lean:17` | Proposition 7.3(2): local split-place parameter transfer $\sigma \mapsto \sigma \boxplus \mu_i[t]$ (`speh`) for $r < t$ via `theta_lift_general_linear`. | [Lean, read] |
| `GlobalTheory.StepRule.rulePar_of_pairPar`, `rulePar_step` | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FirstOccurrenceRuleThetaChainStepBothDirections.lean:21,58` | Proposition 7.3(1): `FarFrom` gap $\ge (t+3)/2$ avoids the singular locus $(t+1)/2$ and gives bidirectional archimedean theta step rules. | [Lean, read] |
| `PiLocalization₂.val_autCusp`, `rankY_succ`, `GlobalTheory.ChainOnto.upPar_of_transfer` | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainUpwardLiftHeckeParamTransferred.lean:26,42,46` | Proposition 7.3(2): rank recursion $r_{k+1} = r_k + t$ and global off-$S$ spherical Hecke parameter transfer across upward theta integral `Step.up`. | [Lean, read] |
| `exists_tprod_ne_zero_of_cc`, `ip_unique`, `thetaChain_upward_induction_fixed_metric`, `chainUp_of` | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainUpwardInductionFixedMetric.lean:14,25,41,71` | Proposition 7.3(3): Schur uniqueness of metrics on pure tensors and $m$-step chain induction proving $\mathrm{ip}(y, x_k) = \mathrm{ip}_0(\Theta y, u)$ and `IsPar x_k (chainPar c B k)`. | [Lean, read] |
| `NonEndoscopicHypothesesAlt`, `GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses`, `geometricLemma` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:12,22,83` | Definition 7.3(2) & Section 7.5.1: 60-field `Prop` bundle of named literature inputs (including `UnusedSlot72` at `:74`). | [Lean, read] |
| `EventuallyAtAllPoints`, `LiftsCondition`, `CoversCondition`, `LiftLambdaBound`, `CovolumeBoundOfX` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LiftLambdaBound.lean:18,26,29,37,60` | Definition 7.3: lift/cover predicates along $i < m$ and covolume bound `CovolumeBoundOfX`. | [Lean, read] |
| `GlobalTheory.Fc.HypsAlt` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22` | Definition 7.3(3): 46-field `Type 1` bundle (`𝒜`, `σ`, `cT`, `c30`, `cIc`, plus 41 clauses) of definite/indefinite theta-lift families and row/period/mass properties. | [Lean, read] |
| `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound`, `every_character_of_theta_integrals_local_matching` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44,69` | Theorem 7.4 (Step 1): constructs `Nonempty (HypsAlt ...)` from Howe/Siegel–Weil, local matching, covolume bounds, and `RecTExists`, and deduces `EveryCharacter` given `VWin`. | [Lean, read] |
| `UpperTheory.Top.shape_closed_link_n_of_green`, `UpperTheory.Top.shapeWin` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33`; `src/Development/AutomorphicArithmetic/CharacterBoxes/ShapeWin.lean:27` | Theorem 7.4 (Step 2): wires `Green` and `HypsAlt` into `DesignExists` and the nine `Closed` chain links (`LinkDIVt`, `LinkEta`, `LinkIRR`, `LinkG`, `LinkS`, `LinkGLOBAL`, …). | [Lean, read] |
| `UpperTheory.Top.topDesWin` | `src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean:11` | Theorem 7.4 (Step 3) & Section 7.5.2: combines `DesignExists`, the nine `Closed` links, and `divinN_of_hypV` (`VWin`) to prove `FamilyClassConnected`. | [Lean, read] |
| `UpperTheory.Top.TopG`, `hypV_of_cls`, `eFamC_of_cls`, `zeroFreeAll_of_topG` | `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:12,16,19,26` | Definition 7.3(4) & Theorem 7.4 (Step 4): defines `TopG` and combines `TopG` + `supplyChi` + `level_gm_le_on_family_scales` + `formB` to prove `ZeroFreeAll`. | [Lean, read] |
| `UpperTheory.Top.zero_free_all_of_green_v_win`, `every_character_of_green_v_win` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12,16` | Theorem 7.4 (Step 4): plugs `Green`, `VWin`, and `Nonempty HypsAlt` into `zeroFreeAll_of_topG` and `imprimitive`. | [Lean, read] |

### 7.6.2 Cross-chapter interfaces referenced in the Part II roadmap (nodes P8–P12, P15–P16, P18)

| Declaration | File:line | Role in Chapters 8–13 | Tag |
|---|---|---|---|
| `Formalism.MainNotions.WeilJacquetShalikaLaw.Conclusion1` | `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97` | Chapter 8 (`P8`): inert-prime $p$-adic divisibility of theta-chain columns. | [Lean] |
| `Formalism.HN.SlopeIneq` | `src/Formalism/HarderNarasimhan/Statement.lean:91` | Chapter 9 (`P9`): Bost's slope inequality on Hermitian lattices. | [Lean] |
| `Formalism.MainNotions.LinkN`, `LinkG`, `LinkS` | `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:45,138,152` | Chapters 9–10 (`P10`–`P11`): congruence-to-$Ш^1$ link, gain link, and near-orthogonality of word periods. | [Lean] |
| `UpperTheory.Top.HypV`, `divinN_of_hypV` | `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10,117` | Chapter 10 (`P11`): converts `HypV` (`VWin`) and `LinkN` into the divisibility congruence budget. | [Lean] |
| `UpperTheory.One.vwin_of_row` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4` | Chapter 11 (`P12`): proves `VWin` from Galois representations `Row0b`. | [Lean] |
| `UpperTheory.Zero.LLC.RecTExists` | `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:78` | Chapter 12 (`P15`): partial local Langlands map passed into `SiegelEisensteinSecondTermHypotheses`. | [Lean] |
| `GlobalTheory.GLq.Green`, `green_of_regular` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumRangeEqRoots.lean:225` | Chapter 13 (`P16`): Green's cuspidal character classification for $\mathrm{GL}_d(\mathbb F_g)$ ($g$ prime). | [Lean] |
| `OpenLiteratureStatements`, `every_character_of_literature_of_vWin` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215,810` | Chapter 13 (`P18`): instantiates the named literature `Prop` slots in a 151,285-module cone (literature-matching fidelity `[Open]`). | [Lean] |

**Summary of the chapter.** Classical Poisson summation (Lemma 7.1) endows lattice sums of Schwartz
functions under the Weil representation of a reductive dual pair $(U(V), U(V')) \subset \mathrm{Sp}(W)$
with two commuting automorphic invariance groups `[Jacobi1829]`, `[Weil1964]`, `[Howe1979]` [Expository].
Under explicit sigma-finiteness and Tonelli $L^1$-domination hypotheses — satisfied automatically on
compact definite unitary quotients $[U(X_j)]$ and via moderate-growth $\times$ rapid-decay cancellation
on non-compact quotients (`lift_conv_cont_growth`, Theorem 7.2) [Lean, read] — iterating $m$ bilinear
theta lifts composes their kernels and equates the $m$-step upward inner product $\langle y, x_m \rangle$
to the downward seesaw pairing $\langle \Theta y, u \rangle$ while adjoining one non-interlacing
spectral block $\mu_j[t]$ per step (`HCIn.hc`, `thetaChain_upward_induction_fixed_metric`,
Proposition 7.3) [Lean, read]. In node `P17`, `nonempty_hyps_definite_side_of_closed_bound`,
`shape_closed_link_n_of_green`, `topDesWin`, and `every_character_of_green_v_win` (Theorem 7.4) [Lean, read]
assemble the definite-unitary chain families `HypsAlt` from 60 named literature `Prop` slots
(`UnitaryGroupThirdPlaceHypotheses`, audited honestly in Section 7.5.1) and wire them to `TopG` and
`EveryCharacter`, leaving four concrete arithmetic links — inert-prime divisibility (`P8`), slopes and
near-orthogonality (`P9`–`P10`), congruence modules (`P11`), and `VWin` (`P12`) — for Chapters 8–11.
