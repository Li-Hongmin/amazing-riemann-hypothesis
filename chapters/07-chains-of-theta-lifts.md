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

#### 7.4.3.1 Spherical transfer at a split place

A full-rank rectangular matrix records an $r$-plane inside a space of dimension $r+t$. The stabilizer of that plane acts on a quotient of dimension $t$. Extracting a coefficient of the Schwartz pairing at this matrix reveals the quotient's determinant character. The spherical Hecke algebra then measures that character as a string of $t$ entries.

For orientation, in the smallest positive-rank case $r=1$, $t=2$, the added determinant character has a one-dimensional representation space. Its first Hecke eigenvalue comes from $q+1$ lattice neighbors. After normalization, the eigenvalue encodes two Satake entries.

**Conventions.** Let $k$ be the nonarchimedean field at a split place, with integers $\mathcal O$, uniformizer $\varpi$, and residue cardinality $q$. Set $|\varpi|=q^{-1}$, $G_m=\mathrm{GL}_m(k)$, $K_m=\mathrm{GL}_m(\mathcal O)$, and $n=r+t$. Let $P$ be the upper block parabolic of type $(r,t)$, with diagonal blocks $a,d$. Its modulus is $\delta_P(p)=|\det a|^t|\det d|^{-r}$. The normalized induction $I=\operatorname{Ind}_P^{G_n}(\sigma\boxtimes(\mu\circ\det))$ consists of right-smooth functions with
$$
f(ph)=\delta_P(p)^{1/2}\mu(\det d)\sigma(a)f(h),
$$
with right translation by $G_n$. The Schwartz space consists of locally constant compactly supported functions on $M_{n,r}(k)$. Its split oscillator action is
$$
(\omega_\mu(g,h)\Phi)(x)=\mu(\det g)\mu(\det h)^{-1}|\det g|^{n/2}|\det h|^{-r/2}\Phi(h^{-1}xg).
$$
A theta pairing is a nonzero linear $B$ from this space to $\operatorname{Hom}_{\mathbb C}(V_\pi,V_\sigma)$ with
$$
B(\omega_\mu(g,h)\Phi)(\pi(h)w)=\sigma(g) B(\Phi)(w).
$$
The large-group action is on the argument of $B(\Phi)$. In the tensor convention this gives the smooth contragredient on the large side.

Our normalized Satake multiset consists of $\chi_j(\varpi)$ for the spherical constituent of normalized upper Borel induction of the unramified characters $\chi_j$. On this side $\mu[t]$ denotes the values at $\varpi$ of $\mu |\cdot|^{(t-1)/2-j}$ for $0\le j<t$, and $\boxplus$ is multiset union. The archive's rank-one Speh parameter is the direct sum of these twists of the rank-one parameter. In the unramified case its monodromy is zero. The archive's reciprocity interface takes inverses of its Satake coordinates when reading Frobenius eigenvalues. With its product and determinant laws the induced representation therefore gives the corresponding direct sum on the Weil–Deligne side, and its twist law applies the inverse character to the entire sum.

**Proposition 7.3f (Conditional spherical split-place transfer).** Suppose $1\le r<t$, $\sigma$ is smooth, irreducible, spherical and unitarisable, and $\mu$ is unitary and unramified. Assume $I$ is irreducible. If a smooth irreducible $\pi$ admits a theta pairing as above, then $\pi\simeq I$ and
$$
\operatorname{Sat}(\pi)=\operatorname{Sat}(\sigma)\boxplus\mu[t].
$$
In particular $\pi$ is spherical. Twisting it by $\eta^{-1}\circ\det$ for an unramified $\eta$ multiplies all entries by $\eta(\varpi)^{-1}$.

**Lemma (Rank descent).** Suppose $B$ kills every test vanishing at ranks at most $j$, for $0\le j<r$. Then it kills every test vanishing at ranks less than $j$.

*Proof.* Let $e_j$ be the matrix with an identity in its upper left $j$ by $j$ block and zeros elsewhere. Put $c=\varpi^s$ with $s\ge1$ and $U=e_j+cM_{n,r}(\mathcal O)$. For each $j$ by $r-j$ residue matrix $L$, choose an integral lift and put
$$
g_L=\begin{pmatrix}1_j&c L/\varpi\\0&1_{r-j}/\varpi\end{pmatrix}.
$$
On ranks at most $j$, $1_U(x)=\sum_L1_U(xg_L)$. In block coordinates $A,B_0,C,D$ for $x$, both sides require $A\equiv 1_j$ and $C\equiv0$ modulo $c$. Here $A$ is invertible and the rank condition forces $D=CA^{-1}B_0$. The condition that $B_0+cAL$ lie in $c\varpi M_{j,r-j}(\mathcal O)$ implies $B_0$ is divisible by $c$, and then $D$ is divisible by $c$. Conversely if $x\in U$, the class of $L$ is uniquely determined by $-A^{-1}B_0/c$ modulo $\varpi$. The bottom-right congruence follows from $D+cCL=CA^{-1}(B_0+cAL)$. For $j=0$ the identity is tested on the zero matrix and the sum has one term.

The oscillator scalar for $(g_L,1)$ has modulus $q^{n(r-j)/2}$ and is independent of $L$. Thus equivariance gives $B(1_U)w=s_j^{-1}\sum_L\sigma(g_L)B(1_U)w$ with $|s_j|=q^{n(r-j)/2}$. The invariant norm bounds the right side by $q^{(j-n/2)(r-j)}\|B(1_U)w\|$. This factor is below one since $2j<n$, so $B(1_U)=0$.

For localization, every rank-$j$ matrix in $e_j+\varpi M_{n,r}(\mathcal O)$ is carried from $e_j$ by integral invertible row and column operations, by the invertible block $A$ and the formula for $D$. These operations preserve all the standard ball lattices. A test supported in this neighborhood can be partitioned into finitely many sufficiently small standard cosets on which it is constant. For a coset meeting rank $j$, take its center at a rank-$j$ point and apply the ball calculation by equivariance. Cosets missing rank $j$ contribute a test vanishing on rank at most $j$ if the original test vanishes below rank $j$. Transport this neighborhood argument by rank normal form to each rank-$j$ point. For a general test vanishing below rank $j$, the intersection of its compact open support with the closed rank-at-most-$j$ locus is compact. Cover it by finitely many transported neighborhoods and refine them into disjoint compact open pieces by successive differences. The remaining test vanishes on rank at most $j$. This proves the lemma.

**Proof of Proposition 7.3f.** At $e=e_r$, take $s$ so large that the principal congruence subgroup of level $s$ in $K_n$ fixes $w$. For any $x\in e+\varpi^s M_{n,r}(\mathcal O)$, append the last $t$ standard columns to $x$ to obtain a matrix in this subgroup taking $e$ to $x$. It preserves the ball lattices and its determinant is a unit. Thus the values of $B(1_U)w$ on equal-radius smaller balls in this neighborhood coincide. Subdividing any test and the whole neighborhood at a common radius gives
$$
B(\Phi)w=\left(\int \Phi(x)\,dx\right)\operatorname{ev}(w)
$$
for tests supported sufficiently near $e$, with additive Haar measure normalized on the integer lattice. Testing on a common smaller ball shows uniqueness and hence linearity of $\operatorname{ev}$. If it were zero, transport by equivariance would give a zero germ at every full-rank point for each $w$. A compact-open partition then kills every test vanishing below full rank. The lemma, descending from $j=r-1$ to zero, would give $B=0$. Hence $\operatorname{ev}\ne0$.

For $p\in P$, $p^{-1}ea=e$. Take a test with nonzero integral and sufficiently small support for the germs of $w$ and $\pi(p)w$. In the integral of $\omega_\mu(a,p)\Phi$, the inverse Jacobian of $x\mapsto p^{-1}xa$ is $|\det p|^r|\det a|^{-n}$. With the oscillator scalar this gives $\mu(\det d)^{-1}\delta_P(p)^{-1/2}$. Equivariance now yields
$$
\operatorname{ev}(\pi(p)w)=\delta_P(p)^{1/2}\mu(\det d)\sigma(a)\operatorname{ev}(w).
$$
The upper unipotent radical acts trivially after applying $\operatorname{ev}$, so the coefficient factors through coinvariants, with the half-modulus removed on the normalized Jacquet module. Explicitly $w\mapsto[h\mapsto\operatorname{ev}(\pi(h)w)]$ takes values in $I$ by the displayed covariance and the open stabilizer of $w$. It intertwines by right translation and is nonzero by evaluation at the identity. Irreducibility gives the isomorphism.

By $G_n=PK_n$, evaluation at $1$ identifies $I^{K_n}$ with $V_\sigma^{K_r}$, since the image of $P\cap K_n$ in the Levi is $K_r\times K_t$. In the Schwartz model the integer-lattice indicator is fixed by $K_r\times K_n$. For every invariant test $B(\Phi)$ factors between the fixed lines by compact averaging. There is a nonzero such test: choose $w\in V_\pi^{K_n}$ with $\operatorname{ev}(w)\ne0$ by the evaluation isomorphism and average a small ball indicator at $e$ over the two compacts. Its value at $w$ is the average of $B(1_U)w$, which is already fixed by $K_r$ and equals $\operatorname{vol}(U)\operatorname{ev}(w)$. For a large-side Hecke operator $T$, integrating the pairing gives
$$
B(\omega_\mu(1,T)\Phi)w=B(\Phi)\pi(T^\vee)w,\qquad T^\vee(h)=T(h^{-1}).
$$
Inversion comes from placing $\pi$ on the argument of $B(\Phi)$.

On $G_t$, $\mu\circ\det$ embeds into normalized Borel induction of $\mu|\cdot|^{-(t+1-2j)/2}$, $1\le j\le t$. The function $h\mapsto\mu(\det h)$ has the required left covariance because the Borel half-modulus cancels the absolute-value twists. By the spherical classification, $\sigma$ is the spherical subquotient of normalized Borel induction for its multiset. Normalized induction in stages and exactness of induction give $I$ as a subquotient of the Borel induction for the concatenated lists. Compact fixed vectors are exact by averaging, so the fixed line has that principal series' Hecke character. This proves the parameter formula. Twisting multiplies every inducing character by $\eta^{-1}$.

**Computing the Hecke character.** Give $K_m$ volume one. For $1\le i\le m$ let $T_i$ be the indicator of $K_m\operatorname{diag}(\varpi 1_i,1_{m-i})K_m$. Its cosets $hK_m$ correspond to lattices between $\varpi\mathcal O^m$ and $\mathcal O^m$ with codimension $i$ modulo $\varpi$. An upper triangular representative has $\varpi$ on the diagonal at positions $J$ of size $i$ and $1$ elsewhere. In the residue subspace choose the echelon basis with last nonzero pivots in the complementary positions. The free entries are in rows $j\in J$ in columns $\ell\notin J$ with $\ell>j$. Lift those basis columns and add $\varpi$ times the remaining standard columns. This gives precisely $q^{\sum_{j\in J}(m-j)-i(i-1)/2}$ representatives for $J$. On each, the normalized Borel fixed vector with value $1$ at the identity takes the value $\prod_{j\in J} q^{-(m+1-2j)/2}z_j$, where $z_j=\chi_j(\varpi)$. Each coset has volume one. Multiplying the powers and summing gives
$$
\lambda(T_i)=q^{i(m-i)/2}e_i(z_1,\ldots,z_m),
$$
where $e_i$ is the elementary symmetric polynomial. The monic polynomial with those elementary symmetric coefficients recovers the multiset.

1. **Rank one and a rank-two block.** For $\sigma=\chi$ on $G_1$, the coset $\varpi K_1$ gives $a=\chi(\varpi)$. Put $b=\mu(\varpi)$. For $\mu\circ\det$ on $G_2$ the $q+1$ lines in the residue plane give $q+1$ cosets for $T_1$, each acting by $b$. The eigenvalues for $T_1,T_2$ are $(q+1)b,b^2$. The roots with sum $(q+1)b/q^{1/2}$ and product $b^2$ are $bq^{-1/2},bq^{1/2}$. With $G_0=\{1\}$, the boundary lift $0\to1$ has Schwartz space $\mathbb C$ with large-side action $\mu^{-1}$. Multiplication gives the pairing with the large partner $\mu$ and the eigenvalue $b$.
2. **Smallest positive ranks, $G_1\to G_3$.** For $T_1$ the three choices of $J$ give $q^2,q,1$ cosets with respective weights $q^{-1}a,bq^{-1/2},q bq^{1/2}$. Their sum is $qa+q^{1/2}(q+1)b$. For $T_2$, the pairs $\{1,2\},\{1,3\},\{2,3\}$ give $q^2,q,1$ cosets with weights $q^{-1}abq^{-1/2},abq^{1/2},qb^2$. The sum is $q^{1/2}(q+1)ab+qb^2$. The central $T_3$ gives $ab^2$. Divide the first two eigenvalues by $q$ to obtain the first two elementary symmetric functions. The polynomial is $(X-a)(X-bq^{-1/2})(X-bq^{1/2})$.

**Scope.** Proposition 7.3f starts with a nonzero local pairing and proves there is a spherical test with nonzero pairing on that pair. Global nonvanishing of an integral, occurrence in a specified automorphic isotypic space, and cuspidality require the global hypotheses of Proposition 7.3. In its archive consumer, PairRead supplies the local pairing, RowUnit supplies unitarisability, and rank_add_five_le supplies $r<t$. The Irr packages give smoothness and irreducibility, and mu_ok gives smoothness and unitarity of $\mu$. The large representation fed to the local theorem already carries the $\eta$ twist. The unramified restriction is used here to compute spherical Hecke eigenvalues.

**Classical comparison.** Mínguez gives the normalization in §1 and the matrix rank filtration in §2. Section 3 computes Jacquet modules of that filtration. Theorem 6.1 and Corollary 6.3 (pp. 733–734) give the Langlands-quotient description, with a contragredient in the tensor convention and the rank-difference string. The proof above follows the archive's split rank descent and full-rank germ. The spherical lattice counts make the parameter calculation explicit. [Mínguez, original article](https://www.numdam.org/item/ASENS_2008_4_41_5_717_0/).

**Verification.** See [Split-place supply for Proposition 7.3f](#split-place-supply-for-proposition-73f).

#### 7.4.3.2 Evaluation on a single Bruhat cell

The split theta argument needs to identify the representation contributed by one Bruhat cell. A section on the cell takes values in the original inducing space. Passing to the target Levi requires two operations: quotient the values by the action of the unipotent stabilizer, then average along the unipotent directions that move the point. The two cells of a principal series show why both operations occur.

**Example 1 (the two cells of $\mathrm{GL}_2$).** Let $B=TU$ be upper triangular, with $u(x)=1+xE_{12}$, and take normalized induction of $\chi_1\otimes\chi_2$. Use left covariance and right translations. Give $\mathcal O_F$ additive volume one. The identity cell is a point in the left quotient by $B$. Its section is determined by $v=f(1)$, and $U$ acts trivially. For $t=\operatorname{diag}(a,b)$, evaluation at $t$ gives $|a/b|^{1/2}\chi_1(a)\chi_2(b)v$. Jacquet normalization cancels $|a/b|^{1/2}$. Covariant extension of $v$ gives the inverse, and evaluation and extension undo each other.

For $s=(12)$ the points are $Bsu(x)$, with $x\in F$. A section is a compactly supported locally constant function $f(x)$. Right $U$ acts by translation. The cell map at $1$ is $I(f)=\int_F f(x)\,dx$ and its inverse sends $v$ to the class of $v1_{\mathcal O_F}$. Integration recovers $v$. For the other composite choose $K=\varpi^{-e}\mathcal O_F$ containing both supports. Averaging $f-I(f)1_{\mathcal O_F}$ over $K$ gives zero on $K$ by translation invariance and zero off $K$ by support. An average represents the same coinvariant class as the starting vector, since it is a finite weighted sum of translates with weights summing to one. Now $su(x)t=(sts^{-1})su(bx/a)$. Left covariance contributes $|b/a|^{1/2}\chi_1(b)\chi_2(a)$, substitution contributes $|a/b|$, and Jacquet normalization contributes $|a/b|^{-1/2}$. The resulting open-cell character is $\chi_1(b)\chi_2(a)$.

**Definitions.** Let $F$ be a nonarchimedean local field, $G=\mathrm{GL}_n(F)$, and $P=MU$, $Q=LN$ standard upper block parabolics. Write $\sigma$ for a smooth complex representation of $M$ on $W$, and set $\tau(p)=\delta_P(p)^{1/2}\sigma(p_M)$, where $\delta_P$ is the absolute determinant of conjugation on $U$. Fix a permutation matrix $w$. Put $H=Q\cap w^{-1}Pw$, $A=N\cap H$ and $D=L\cap H$. The block entry conditions give $H=AD$. The cell is presented as the left quotient of $Q$ by $H$, via $q\mapsto Pwq$. Let $C$ be the smooth functions on $Q$ with covariance $f(hq)=\tau(whw^{-1})f(q)$ and support compact modulo $H$. Let $p_A:W\to E$ be the quotient by the relations $\tau(waw^{-1})v-v$ for $a\in A$. Since $D$ normalizes $A$, it acts on $E$. Write $\lambda(d)$ for the measure multiplier of conjugation by $d$ on the left quotient of $N$ by $A$. Both unipotent groups are unimodular. Write $X$ for the left quotient of $N$ by $A$. Use the right invariant quotient measure on $X$, with the image of a compact open subgroup $K$ having volume $\operatorname{vol}(K)/\operatorname{vol}(A\cap K)$ for fixed compatible Haar normalizations.

**Proposition 7.3g (single-cell isomorphism).** Suppose the cell is presented by $C$. When applying this statement to a relative support quotient, assume that restriction identifies that quotient with $C$. The normalized $N$-coinvariants of $C$ are obtained by taking the normalized row Jacquet module of $\sigma$ for the refinements of the source blocks by target blocks, transporting its Levi action by $w$, and applying normalized column parabolic induction in $L$. This representation depends up to isomorphism on the intersection sizes. In the original cell coordinates the map is
$$
[f]\longmapsto \left(l\longmapsto \delta_Q(l)^{-1/2}
       \int_Xp_A f(nl)\,d\dot n\right).
$$

**Proof.** Write $Q=NL$. Uniqueness of the unipotent and Levi parts gives the fiber homeomorphism used below: locally over the base, the coordinates are $n l$, and two such coordinates over a fixed $l$ differ on the left by $A$. Indeed the decomposition $Q=N L$ is a homeomorphism of spaces, and the quotient map from $Q$ by left $H$-translations is open. Restricting to the inverse image of one base point gives the corresponding quotient topology, since saturation of an open subset of $Q$ commutes with restriction to an $H$-stable subset. First omit the outer half-modulus and call the resulting integral $I(f)$. The quotient on values makes the function independent of the representative of a left $A$-coset. The fiber over $Dl$ in the cell is homeomorphic to $X$. It is closed since the base quotient of $L$ by $D$ is Hausdorff. The support on that fiber is compact because the support in the cell is compact. The unprojected function on $N$ can have entire noncompact $A$-cosets in its support. The integral is a finite sum of values times volumes. For a compact open subgroup $K$ containing the support modulo $A$, it equals the normalized $K$-average of $p_A f(kl)$ times the volume of the image of $K$. It stabilizes under enlargement. Such subgroups exist: conjugate the integral upper unipotent matrices by diagonal powers of $\varpi$ with weights $0,1,2,\ldots$ on successive target blocks. The bounds on upper entries expand, giving increasing compact open subgroups exhausting $N$. Their images exhaust the quotient and are open, so a compact support fits at one level.

Right translation by $n_0$ changes the variable by right multiplication by $ln_0l^{-1}$, preserving the quotient measure. Thus $I$ factors through $C_N$. Right translation by $L$ commutes with the map and gives smooth sections. With $\overline{\tau}$ the induced action on $E$, substitution $n=d n'd^{-1}$ proves
$$
I(f)(dl)=\lambda(d)\overline{\tau}(wdw^{-1}) I(f)(l).
$$

To lift a section $\phi$ of this unnormalized target model, take a compact open right stabilizer $S\subset L$. There are finitely many sets $Dl_i S$, since $D$ is a parabolic in $L$ and this quotient is compact. Lift $\phi(l_i)$ to $v_i\in W$. Take $K_i$ compact open in $N$ small enough that $A\cap K_i$ acts trivially on $v_i$. Its normalizer in $L$ is open, by continuity of conjugation and compactness of $K_i$. Choose an open normal subgroup $S'\subset S$ so small that $L_i=l_iS'l_i^{-1}$ normalizes $K_i$ and $D\cap L_i$ fixes $v_i$ for the inducing action. These conditions are open and there are finitely many of them. Subdivide each $Dl_i S$ into double cosets for $S'$, choosing representatives $l=l_i s$. Normality makes $lS'l^{-1}=L_i$. On $H K_i L_i l$ define a section by covariance and right invariance under $l^{-1}(K_i L_i)l$, assigning the value $v_i/\operatorname{vol}(\operatorname{image}K_i)$ at $l$. The intersection of $H$ with $K_i L_i$ is $(A\cap K_i)(D\cap L_i)$ and fixes this value. Thus the factorization does not affect the section. Its support in this quotient is compact open, so extension by zero gives a smooth section. The projected fiber at $l$ has that constant value on the image of $K_i$ and vanishes elsewhere. The integral gives $\phi(l)$. By covariance and right $S'$-invariance the sum of the bumps gives $\phi$ everywhere.

For injectivity suppose $I(f)=0$. Choose $S\subset L$ compact open fixing $f$ and representatives $l_i$ for the double cosets of $D$ and $S$ in $L$. For each representative take a compact open subgroup $K_i$ containing the support modulo $A$ on its fiber. The $W$-valued $K_i$-average at $l_i$ lies in the kernel of $p_A$, so is a finite sum of relations $\tau(waw^{-1})v-v$. Enlarge $K_i$ to $K$ containing all the $a$ in these relations. Inside $K$ the function on the fiber is supported on $(A\cap K)K_i$. The new average is a scalar multiple of the $A\cap K$-average of the old one. Indeed product probability measure on $(A\cap K)\times K_i$ pushes forward to normalized Haar measure restricted to the product set, by invariance under left $A\cap K$ and right $K_i$. This average kills the relations. The same holds for every larger level. Right averaging the fiber over such a $K$ vanishes at every $n$: for $n\in AK$ use left covariance and Haar invariance in $K$, and for $n\notin AK$ use support.

Choose a common compact open $K_0\subset N$ normalized by $S$ whose conjugates by $l_i$ contain the enlarged levels. Start with one level containing the finitely many conjugated requirements, then generate a group by its $S$-conjugates. Their union is contained in a compact subset, which fits inside a single level of the exhaustion. The generated group is open and hence closed in that compact group. The right $K_0$-average remains right $S$-invariant since $S$ normalizes $K_0$. On the fiber over $Dl_i$ it is the average over $l_i K_0 l_i^{-1}$ in the $N$-coordinate. Hence it vanishes on every fiber over $Dl_iS$, by the fiber calculation, right invariance and left covariance. Thus $[f]=0$. The inverse on classes is the lift by the sum of bumps. Integrating gives the original section. In the other direction, subtract the bump lift of $I(f)$ from $f$. The difference has zero integral and is killed by a common compact average. This proves the second composite and independence from all choices of lifts, representatives and compact subgroups.

For normalization, transport the source partition through $w$ and compare its indices with the target indices on the same coordinates. The image of $A$ under conjugation and projection to $M$ is the row radical. The subgroup $D$ is the column parabolic. Conjugating and projecting to the refined row Levi agrees with projecting to the column Levi and then identifying the intersections by $w$. On that common Levi one has
$$
\delta_Q^{-1/2}\lambda\,(\delta_P^{1/2}\circ\operatorname{Ad}(w))
     =\delta_{\rm col}^{1/2}\delta_{\rm row}^{-1/2}.
$$
Pair the two opposite matrix directions for each pair of refined blocks. When the two indices increase in the same direction, the outer halves cancel and the target upper direction belongs to $A$. When they increase in opposite directions, the outer halves give the inverse of the target upper multiplier, which occurs in $\lambda$. When just the target index increases, its upper direction lies in $A$ and the negative outer half is the negative row half. When just the source index increases, the positive outer half is the column half. Equal indices contribute nothing. For a rectangular block of size $a$ by $b$ the multiplier is $|\det g_a|^b|\det g_b|^{-a}$, which gives the same calculation without any scalar-block assumption. All characters are trivial on the column radical, since its action on the relevant unipotent Lie algebras is unipotent. Multiplication by $\delta_Q(l)^{-1/2}$ implements the normalized action and its reciprocal reverses it.

Choose bases in the intersections, matched by $w$. The transport called `cell_iso` identifies the two relation spaces by the row group identification, hence takes the coefficient class of $v$ to the class of $v$. On sections it is pullback by the column Levi coordinate isomorphism followed by that coefficient map. Covariance follows from the preceding character identity. The inverse pulls back by the inverse group isomorphism and applies the inverse coefficient map. Substitution verifies both composites, and multiplicativity gives right equivariance.

For `cellFunctor_congr`, choose bijections between the refined bases of two placements of equal sizes. The resulting permutations $x\in M$ and $y\in L$ conjugate the respective parabolics and row radicals. The coefficient map is $J_x[v]=[\sigma(x)v]$, with inverse $J_{x^{-1}}$. It respects the row normalization since conjugation preserves determinants and block sizes. The map on sections is $F(l)\mapsto J_xF(y^{-1}l)$. To check covariance, move $d'$ past $y^{-1}$ by writing $y^{-1}d'=(y^{-1}d'y)y^{-1}$ and use the coefficient intertwining and the unchanged column modulus. Its inverse uses $J_{x^{-1}}$ and $yl$. Right translations commute with the change. The permutation representative enters the orbit chart and the matching of intersection bases. Changing the permutation within its double coset allows left and right block permutations, and the size-matrix transport identifies the resulting models. This is an existence statement for isomorphisms with specified choices. $\square$

**Example 2 (the first mixed two-block cell).** Take $P=Q$ of type $(2,1)$ in $\mathrm{GL}_3(F)$, $w=(23)$, and $\sigma=\chi\circ\det\boxtimes\eta$ for smooth characters. The intersection matrix has rows $(1,1)$ and $(1,0)$. Write $n(x,y)=1+xE_{13}+yE_{23}$. Under $w$ the two entries go to $E_{12}$ and $E_{32}$. Thus $A$ is the $x$-axis, the row radical is upper unipotent in the first $\mathrm{GL}_2$, and the fiber coordinate is $y$. The projection on the inducing line is the identity. In the first block of $L$, $E_{12}$ goes to $E_{13}$ and $E_{21}$ to $E_{31}$. Hence $D=B_2\times\mathrm{GL}_1$. For $d=\operatorname{diag}(a,b,c)$ the covariance is
$$
|ab/c^2|^{-1/2}|b/c|\,|ac/b^2|^{1/2}\chi(ac)\eta(b)
       =|c/b|^{1/2}\chi(a)\eta(b)\chi(c).
$$
The measure factor $|b/c|$ is the multiplier of $y$. The upper unipotent of $D$ shears $x$ and fixes $y$. The normalized row character is $|a/c|^{-1/2}\chi(a)\chi(c)$ and the column half-modulus is $|a/b|^{1/2}$. The result is the normalized $\mathrm{GL}_2$ induction of $\chi|\cdot|^{-1/2}$ and $\eta$, tensored with $\chi|\cdot|^{1/2}$ on the last factor.

For a concrete section, choose a deep principal congruence subgroup $S$ in $L$ and a normalized target section on $DS$ with value $v$ at $1$ and zero off $DS$. Lift by the covariant bump on $H n(\mathcal O_F,\mathcal O_F) S$ with value $v$ at $1$. The integral at $1$ is the integral of $v1_{\mathcal O_F}(y)$ and gives $v$. The known covariance gives the section on $DS$. For the reverse calculation, refine $S$ to a common stabilizer of a starting section and its lift. On each of the finitely many base pieces the fiber difference has integral zero. Its average over a ball containing its support in $y$ vanishes everywhere by the calculation of Example 1. The full two-coordinate average also vanishes because the function is constant in $x$. One common compact level after conjugating by the base representatives gives zero in the whole cell, so the original class is recovered. In the identity cell the matrix has rows $(2,0)$ and $(0,1)$, $A=N$ and $D=L$. The fiber is a point, the outer halves cancel and the result is $\sigma$, with inverse covariant extension.

**Unit evaluation in the support argument.** The declaration `Model.evalOne_bijective` concerns the bijection between $G$-maps $\pi\to i_P^G\rho$ and $M$-maps $r_P^G\pi\to\rho$. For the first map $T$, define $\psi([v])=T(v)(1)$. Since $T(\pi(u)v)(1)=T(v)(u)=T(v)(1)$ for $u\in U$, the definition descends. At $m\in M$, the induction half-modulus cancels the Jacquet inverse half-modulus. Conversely set $T_\psi(v)(g)=\psi([\pi(g)v])$. Writing $p=mu$ proves left covariance by the coinvariant relation and the normalized action of $m$. A subgroup fixing $v$ fixes the section on the right, and multiplication in $G$ proves equivariance. Evaluating at $1$ recovers $\psi$; the identity $T(v)(g)=T(\pi(g)v)(1)$ recovers $T$. For a determinant representation the unipotent relations are zero, so injectivity of the coefficient map implies injectivity of the resulting induced-model map. The inverse here uses the group action. The inverse of the fiber integral uses compact bumps and averaging.

**Notes on the proof and its use.** Bernstein and Zelevinsky give the orbit calculation in §§5.15–5.17, with the integral in §5.17 and the assembled filtration in Theorem 5.2. Their proof of the fiber isomorphism uses the regular representation and exactness. The proof above exhibits the inverse on classes using the finite averages and bumps of the archive's approach. [Paper] [Bernstein–Zelevinsky, pp. 460, 465–467](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0/)

The geometric package $h_G$ supplied to the split theta argument has a filtration field and a cell multiplicity field. The graded-quotient assembly composes its support-quotient equivalence with `cell_iso` and `cellFunctor_congr`. `Mix.cellone` uses the filtration sum and extracts an off-diagonal row contribution through the multiplicity field. The same geometry enters the support branch through Mix.front and CuspEmbed.main. In its noncuspidal branch, L_jacq uses unit evaluation to embed the irreducible representation into an induction, and L_tens uses the geometry to identify the Levi factor. A nonzero irreducible Jacquet quotient gives a nonzero induced-model map by evaluation at $1$, and irreducibility of the source makes it injective. The determinant-character calculation is another application of the same evaluation. Filtration assembly and Jacquet exactness are inputs here; the assembly, and the one step of it at which exactness enters, are read in [§7.4.3.4](#7434-from-one-cell-to-the-full-bruhat-filtration). See [§7.4.3.1](#7431-spherical-transfer-at-a-split-place) for spherical Hecke eigenvalues and [Chapter 13](13-greens-theorem-and-the-literature-layer.md) for Green characters. The direct evaluation and transport bodies have the scoped read tags in §7.6.1. The bump and kernel suppliers are read in [§7.4.3.3](#7433-compact-bumps-and-averaged-kernels-on-a-single-cell), the full-block support supplier in [§7.4.3.5](#7435-levels-in-the-unipotent-radical-and-supports-on-a-cell), and the cell semisimplification together with exactness of column induction in [§7.4.3.6](#7436-composition-factors-of-a-cell-module).

#### 7.4.3.3 Compact bumps and averaged kernels on a single cell

Proposition 7.3g described the single-cell map and sketched its inverse with bumps and finite averages. The archive does not package that inverse as one isomorphism. It supplies two separate statements to the graded assembly: a surjectivity supply, `cellJacquetMap_surjective`, and a kernel supply, `exists_sub_mem_ker_of_cellJacquet_eq_zero`. Both are consumed at the same two call sites, one in the unnormalized geometric lemma and one in the normalized Bernstein–Zelevinsky assembly, where they produce the graded pieces of the Jacquet filtration. This subsection reads the two supplies and the four declarations behind them. It explains three devices: a covariant bump on a tube $PxK$, an exhaustion of $N$ by compact open subgroups that every integral Levi element normalizes, and a positivity argument showing that a bump has nonzero image without computing any integral.

**Example 3 (what a bump looks like in $\mathrm{GL}_2$).** Keep the notation of Example 1 with $B=TU$, $s=(12)$, and the open cell $BsB$. Fix $J\ge 1$ and let $K_J$ be the principal congruence subgroup of level $J$. For a vector $v$ fixed by $\tau$ on $B\cap K_J$, define $b(g)=\tau(p)v$ when $g=psk$ with $p\in B$ and $k\in K_J$, and $b(g)=0$ otherwise. This is well defined: if $psk=p's k'$ then $p'^{-1}p=s(k'k^{-1})s^{-1}$ lies in $B\cap K_J$ and fixes $v$. Its cell function is $x\mapsto b(su(x))$. Now $su(x)\in BsK_J$ exactly when $u(x)\in \bar BK_J$ with $\bar B=s^{-1}Bs$ lower triangular. Writing $u(x)=\bar b k$ and $\bar b^{-1}=\begin{pmatrix}a&0\\c&d\end{pmatrix}$ gives $k=\begin{pmatrix}a&ax\\c&cx+d\end{pmatrix}$, so $k\in K_J$ forces $a\in 1+\varpi^J\mathcal O$ and $x\in\varpi^J\mathcal O$. Conversely $u(x)\in K_J$ for such $x$. Hence the cell function is $v\,1_{\varpi^J\mathcal O}(x)$, a compactly supported bump of height $v$, and
$$
\int_F b(su(x))\,dx=q^{-J}v .
$$
The level $J$ had to be positive: at level $0$ the tube $BsK_0$ is all of $G$, the bump is the spherical section, and its cell function, equal to $v$ for $|x|\le1$ and to $|x|^{-1}\chi_1^{-1}\chi_2(x)v$ for $|x|>1$, is not compactly supported. Example 5 below shows what goes wrong with the averages in that case.

**Definitions.** Keep the setting of Proposition 7.3g: $G=\mathrm{GL}_n(F)$, standard block parabolics $P=MU$ and $Q=LN$, a permutation matrix $w$, the cell $C_w=PwQ$, and $H=Q\cap w^{-1}Pw=AD$ with $A=N\cap H$ and $D=L\cap H$. A section of the inducing space means $f:G\to W$ with $f(pg)=\tau(p)f(g)$ for $p\in P$ and right invariance under some open subgroup. An open set $Y\subset G$ is a frame for $C_w$ if the closure of $C_w$ meets $Y$ exactly in $C_w$, $PY=Y$ and $YQ=Y$. In the consumer, $Y$ is the union of the first $j+1$ cells in the chosen ordering and $Y$ minus $C_w$ is the union of the first $j$ cells. Write $\mathcal I_Y$ for the sections vanishing off $Y$. Let $K_J\subset G$ be the principal congruence subgroup of level $J$. For $e\ge 0$ let $t_e$ be the diagonal matrix which is the scalar $\varpi^{-er}$ on the target block of rank $r$, where the rank of a target block is the number of coordinates in the target blocks before it (the archive's `blockRank`, `InductionParabolicGroups.lean:210`; for $Q$ of type $(2,1)$ the two ranks are $0$ and $2$, for the Borel subgroup of $\mathrm{GL}_3$ they are $0,1,2$). Put $N_e=N\cap t_e^{-1}\mathrm{GL}_n(\mathcal O)t_e$, so an entry of $N_e$ joining target blocks of ranks $r<r'$ lies in $\varpi^{-e(r'-r)}\mathcal O$. These are compact open subgroups of $N$, increasing in $e$, exhausting $N$, and each is normalized by $L\cap\mathrm{GL}_n(\mathcal O)$, because $t_e$ is central in $L$ and $L\cap \mathrm{GL}_n(\mathcal O)$ normalizes both $N$ and $\mathrm{GL}_n(\mathcal O)$; these properties are Lemma 7.3t of §7.4.3.5. For a section $f$ and $m\in L$ the cell function is $h_{f,m}(y)=f(wym)$ on $N$. It satisfies $h_{f,m}(ay)=\theta(a)h_{f,m}(y)$ for $a\in A$, where $\theta(a)=\tau(waw^{-1})$. Let $p_A:W\to E$ be the quotient by the relations $\theta(a)x-x$. Say $h_{f,m}$ has cell support at level $e$ if it vanishes off $AN_e$. For $f\in\mathcal I_Y$ and $m\in L$ such a level exists; this is the support supply `exists_cellSupp`, proved in [§7.4.3.5](#7435-levels-in-the-unipotent-radical-and-supports-on-a-cell) as Theorem 7.3v. For a compact open $K\subset N$ write $\operatorname{avg}_K\phi(y)$ for the average of $\phi(yk)$ over $k\in K$; for a smooth $\phi$ this is a finite average over cosets of a stabilizer. Write $c_K$ for the volume of the image of $K$ in the quotient of $N$ by $A$, normalized so that $c_{N_0}=1$. The level evaluation is
$$
\operatorname{ev}_K(f,m)=c_K\,p_A\!\left(\operatorname{avg}_K h_{f,m}(1)\right)\in E ,
$$
and $J_wf(m)$ is its common value for all cell-compact $K$ containing a support level. This is the map of Proposition 7.3g with the half-modulus omitted. The target $\mathcal J_w$ consists of the functions $\psi:L\to E$ with $\psi(dm)=\lambda(d)\overline{\theta}(d)\psi(m)$ for $d\in D$ and right invariance under an open subgroup of $L$. Right translation by $L$ commutes with $J_w$.

**Definition (covariant bump).** Let $x\in G$, let $K\subset G$ be a compact open subgroup, and let $v\in W$ be fixed by $\tau(p)$ for all $p\in P\cap xKx^{-1}$. The bump $b_{x,K,v}$ is the function equal to $\tau(p)v$ at $pxk$ and to zero off the tube $PxK$.

**Lemma 7.3h (bumps are sections).** The bump $b_{x,K,v}$ is well defined, left covariant, right $K$-invariant, supported in $PxK$, and takes the value $v$ at $x$.

*Proof.* If $pxk=p'xk'$ then $p'^{-1}p=x(k'k^{-1})x^{-1}\in P\cap xKx^{-1}$, so $\tau(p')v=\tau(p')\tau(p'^{-1}p)v=\tau(p)v$. For $p_0\in P$ the point $p_0pxk$ lies in the tube with value $\tau(p_0)\tau(p)v$, and a point off the tube stays off it under left $P$ and right $K$ translations. Right multiplication by $k'\in K$ sends $pxk$ to $pxkk'$ with the same value. $\square$

**Lemma 7.3i (small neighborhoods in a locally closed cell).** Let $Y$ be a frame for $C_w$. For every $J$ there is $J'\ge J$ such that for all $k\in K_{J'}$ one has $wk\in Y$, and if moreover $wk\in C_w$ then $wk=pwq$ with $p\in P\cap K_J$ and $q\in Q\cap K_J$.

*Proof.* Since the closure of $C_w$ meets the open set $Y$ in $C_w$, the cell is locally closed. The orbit map $(p,q)\mapsto pwq$ from $P\times Q$ onto the locally closed double coset is open onto its image. Hence there is a neighborhood $V$ of $w$ such that every point of $V\cap C_w$ is $pwq$ with $p$ and $q$ in prescribed neighborhoods of the identity, here $K_J$. Intersect $V$ with the open set $Y$, which contains $w$, and pull back along $k\mapsto wk$; the result is a neighborhood of $1$, which contains some $K_{J_1}$. Take $J'=\max(J,J_1)$. $\square$

In Example 3 this lemma is the factorization $k=\begin{pmatrix}1&0\\c/a&1\end{pmatrix}\begin{pmatrix}a&b\\0&d-cb/a\end{pmatrix}$ of a matrix $k\in K_J$ into a lower and an upper triangular factor, both in $K_J$, so $J'=J$ works for $J\ge1$. The same holds for the open cell of Example 2, where a matrix in $K_J$ factors as an element of $w^{-1}Pw$ times an element of $Q$, both in $K_J$, by clearing the entries $(2,1)$ and $(2,3)$ with a lower triangular $2\times2$ block and an upper right column. In general $J'$ can exceed $J$, and the proof above is the only place in the two supplies where local closedness of the cell is used.

**Lemma 7.3j (nonnegative averages do not cancel).** Let $\phi$ be a function on a group with values in $W$, let $K$ be a compact open subgroup over which $\phi$ has a finite average, and let $\pi:W\to E$ be linear. Suppose $\pi(\phi(xk))=r_k c_0$ with real $r_k\ge0$ for all $k\in K$. Then $\pi(\operatorname{avg}_K\phi(x))=rc_0$ with $r\ge0$, and $r>0$ whenever $\pi(\phi(x))=r_1c_0$ with $r_1>0$ and $c_0\ne0$.

*Proof.* The average is a finite sum over coset representatives $k_q$ with equal weights $1/\mathrm{index}$. Then $r$ is the mean of the $r_{k_q}$. If $c_0\ne0$ the coefficient of the representative of the trivial coset is determined and equals $r_1>0$, so the mean is positive. $\square$

**Lemma 7.3k (cell bumps).** Let $Y$ be a frame for $C_w$, let $J\ge0$, and let $v\in W$ be fixed by $\tau$ on $P\cap K_J$. There is $F\in\mathcal I_Y$ with the following three properties. If $J_wF(m)\ne0$ then $m\in D(L\cap K_J)$. For $k\in L\cap K_J$ one has $J_wF(mk)=J_wF(m)$. Finally $J_wF(1)=c\,p_A(v)$ for a nonzero scalar $c$.

*Proof.* Take $J'$ from Lemma 7.3i and let $f'=b_{w,K_{J'},v}$. The hypothesis of Lemma 7.3h holds, since $P\cap wK_{J'}w^{-1}\subset P\cap K_J$ because $w$ is integral and $J'\ge J$. By the first part of Lemma 7.3i the tube $PwK_{J'}$ lies in $Y$, so $f'\in\mathcal I_Y$. We first describe $f'$ on $wQ$. Suppose $y\in Q$ and $f'(wy)\ne0$. Then $wy=pwk$ with $k\in K_{J'}$, so $wk\in C_w$ and the second part of Lemma 7.3i gives $wk=p_1wq_1$ with $p_1\in P\cap K_J$ and $q_1\in Q\cap K_J$. Put $x=yq_1^{-1}$. Then $wxw^{-1}=pp_1\in P$, so $x\in H$, and
$$
f'(wy)=\tau(pp_1)v=\tau(wxw^{-1})v
$$
because $p_1$ fixes $v$. Thus the restriction of $f'$ to $wQ$ is supported on $wH(Q\cap K_J)$ and is given there by the $H$-covariance rule.

Let $F$ be the average of the right translates of $f'$ by $Q\cap K_J$. This is a finite average because $f'$ is right invariant under an open subgroup and $Q\cap K_J$ is compact; each translate is a section vanishing off $Y$, since $YQ=Y$. Thus $F\in\mathcal I_Y$, and $F$ is right invariant under $Q\cap K_J$, which gives the second property.

For the third property, consider any term $f'(wuk)$ with $u\in N$ and $k\in Q\cap K_J$. By the description above it is either zero or $\tau(wxw^{-1})v$ with $x\in H$ and $uk=xq_1$, $q_1\in Q\cap K_J$. Factor $x=ab$ with $b$ the Levi projection of $x$ and $a=xb^{-1}\in A$. Since the Levi projection of $u$ is trivial, $b$ is the product of the Levi projections of $k$ and $q_1^{-1}$, so $b\in D\cap K_J$ and $\tau(wbw^{-1})v=v$. Hence $p_A(\tau(wxw^{-1})v)=p_A(\theta(a)v)=p_A(v)$. Every term therefore projects to $p_A(v)$ or to $0$, that is, to a nonnegative multiple of $p_A(v)$, and the term with $u=1$ and $k=1$ is $v$ itself. Lemma 7.3j applied to the average over $k$ shows that $p_A(\operatorname{avg}_{Q\cap K_J}f'(wu\,\cdot))=r_u\,p_A(v)$ with $r_u\ge0$ and $r_1>0$ if $p_A(v)\ne0$. Applying Lemma 7.3j again to the average over $u\in N_e$ gives $p_A(\operatorname{avg}_{N_e}h_{F,1}(1))=r\,p_A(v)$ with $r>0$ when $p_A(v)\ne0$. Hence $J_wF(1)=c_{N_e}r\,p_A(v)$ with $c=c_{N_e}r\ne0$. If $p_A(v)=0$ any nonzero $c$ serves.

For the first property, suppose $J_wF(m)\ne0$. Then some term $F(wum)$ with $u\in N_e$ is nonzero, so some $f'(wumk)$ with $k\in Q\cap K_J$ is nonzero, and $umk=xq_1$ as above. Projecting to $L$ and using that $u$ projects to $1$ gives $m=b\cdot \mathrm{proj}_L(q_1)\,\mathrm{proj}_L(k)^{-1}$ with $b\in D$ and the second factor in $L\cap K_J$. $\square$

**Translated bumps.** For $s\in L\cap\mathrm{GL}_n(\mathcal O)$, right translation by $s^{-1}$ followed by division by $c$ turns $J_wF$ into an element $\chi_s$ of the image of $J_w$ which vanishes off $Ds(L\cap K_J)$ and equals $p_A(v)$ on $s(L\cap K_J)$. Here one uses that $J_w$ commutes with right translation and that $s$ normalizes $K_J$. Two elements of $\mathcal J_w$ that agree on $s(L\cap K_J)$ agree on $Ds(L\cap K_J)$ by the covariance rule.

**Theorem 7.3l (surjectivity of the cell map).** Let $\sigma$ be smooth and let $Y$ be a frame for $C_w$. Then $J_w:\mathcal I_Y\to\mathcal J_w$ is surjective.

*Proof.* Let $\varphi\in\mathcal J_w$ be right invariant under $L\cap K_{j_0}$. Since $D$ is a parabolic subgroup of $L$, the Iwasawa decomposition gives $L=D\,(L\cap \mathrm{GL}_n(\mathcal O))$, and $L\cap K_{j_0}$ has finite index in the compact group $L\cap\mathrm{GL}_n(\mathcal O)$. Choose a finite set $T\subset L\cap\mathrm{GL}_n(\mathcal O)$ with $L=D\,T\,(L\cap K_{j_0})$. For each $t\in T$ lift $\varphi(t)$ to $v_t\in W$. Smoothness of $\sigma$ gives a level $J\ge j_0$ such that every $v_t$ is fixed by $\sigma$ on $M\cap K_J$; on integral elements of $P$ the half-modulus is $1$ and $\tau$ acts through the Levi projection, so each $v_t$ is fixed by $\tau$ on $P\cap K_J$. Let $R$ be a set of representatives of $(L\cap K_{j_0})/(L\cap K_J)$. For each pair $(t,r)$ apply Lemma 7.3k and the translation by $s=tr$: this gives $\chi_{t,r}$ in the image of $J_w$, vanishing off $Dtr(L\cap K_J)$ and equal to $p_A(v_t)$ on $tr(L\cap K_J)$. Since $r$ and $k\in L\cap K_J$ lie in $L\cap K_{j_0}$, one has $\varphi(trk)=\varphi(t)=p_A(v_t)$, so $\chi_{t,r}$ agrees with $\varphi$ on $tr(L\cap K_J)$, hence on $Dtr(L\cap K_J)$. These finitely many sets cover $L$.

Now subtract bumps one pair at a time. Maintain a function $\psi$ in the span of $\varphi$ and the bumps constructed so far, together with a set of remaining pairs, such that $\psi$ is right invariant under $L\cap K_J$, $\psi$ vanishes off the union of $Dtr(L\cap K_J)$ over remaining pairs, and at each remaining base point $\psi(tr)$ is either $0$ or $\varphi(tr)$. Start with $\psi=\varphi$ and all pairs. Pick a remaining pair. If $\psi(tr)=0$ then $\psi$ vanishes on $Dtr(L\cap K_J)$ by the agreement rule, and the pair can be dropped. Otherwise replace $\psi$ by $\psi-\chi_{t,r}$: on $Dtr(L\cap K_J)$ the difference vanishes, and at another remaining base point $t'r'$ either $\chi_{t,r}$ vanishes and the value is unchanged, or $t'r'\in Dtr(L\cap K_J)$ and the value becomes $0$. In both cases the invariants persist and the pair can be dropped. When no pairs remain, $\psi=0$. Hence $\varphi$ is a finite sum of the $\chi_{t,r}$ and lies in the image. $\square$

The induction is needed because different pairs $(t,r)$ may produce the same set $Dtr(L\cap K_J)$; when the sets are pairwise disjoint, as in Example 4 below, $\varphi$ is simply the sum of the bumps.

**Lemma 7.3m (class-zero averages vanish at a higher level).** Let $\sigma$ be smooth, let $Y$ be a frame, let $f\in\mathcal I_Y$ and $m\in L$. If $J_wf(m)=0$ then there is a level $e$ at which $h_{f,m}$ has cell support and $\operatorname{avg}_{N_e}h_{f,m}(1)=0$ in $W$.

*Proof.* Let $e_0$ be a support level and $v_0=\operatorname{avg}_{N_{e_0}}h_{f,m}(1)$. The hypothesis says $p_A(v_0)=0$, so $v_0$ is a finite sum of relations $\theta(a_i)x_i-x_i$. The group $A$ is a closed subgroup of $N$ exhausted by the compact open subgroups $A\cap N_e$, so there is $e\ge e_0$ with all $a_i\in B:=A\cap N_e$. Because the support of $h_{f,m}$ lies in $AN_{e_0}$, the average over $N_e$ at $1$ is a positive multiple of $u:=\operatorname{avg}_B(\operatorname{avg}_{N_{e_0}}h_{f,m})(1)$: the product of normalized Haar measures on $B\times N_{e_0}$ pushes forward to normalized Haar measure on the set $BN_{e_0}$, which carries the support inside $N_e$, and the multiple is a ratio of indices. The vector $u$ is fixed by $\theta(B)$, since left multiplication by $b\in B$ acts by $\theta(b)$ on the $A$-covariant function and right multiplication by $b$ is absorbed by the average. Moreover $v_0-u$ lies in the span of $\theta(b)x-x$ for $b\in B$, because $\operatorname{avg}_{N_{e_0}}h_{f,m}(b)=\theta(b)v_0$. For a smooth representation of the compact open group $B$ there is exactly one $B$-fixed vector congruent to $v_0$ modulo that span, namely the $B$-average of $v_0$, and it is linear in $v_0$ and kills every $\theta(b)x-x$ with $b\in B$. Since all $a_i\in B$, the vector $v_0$ is itself in the span, so its $B$-average is $0$. Hence $u=0$ and $\operatorname{avg}_{N_e}h_{f,m}(1)=0$. $\square$

The point of the lemma is the passage from the quotient $E$ back to $W$. A vanishing class only says that $v_0$ is a finite combination of relations; the uniqueness of the fixed projection turns that into the vanishing of an actual average once the level absorbs the finitely many group elements in the relations.

**Theorem 7.3n (kernel of the cell map).** Let $\sigma$ be smooth and let $Y$ be an open set with $YQ=Y$ in which $C_w$ is closed. If $f\in\mathcal I_Y$ and $J_wf(m)=0$ for all $m\in L$, then there is a section $g$ vanishing off $Y\setminus C_w$ such that $f-g$ is a finite linear combination of differences $\pi(n)\varphi-\varphi$ with $n\in N$ and $\varphi$ a section. Conversely every section vanishing off $Y\setminus C_w$ has $J_w$ identically zero.

*Proof.* Let $U$ be an open subgroup fixing $f$ on the right and choose $j$ with $K_j\subset U$. As in Theorem 7.3l choose a finite $T\subset L\cap\mathrm{GL}_n(\mathcal O)$ with $L=D\,T\,(L\cap K_j)$. For each $t\in T$ Lemma 7.3m gives a level $e_t$ with cell support and vanishing average; let $E$ be the largest. Put $g=\operatorname{avg}_{N_E}f$, the average of right translates by $N_E$. It is a finite average, each translate is a section vanishing off $Y$ because $YQ=Y$, so $g$ is a section vanishing off $Y$.

First, $g$ vanishes on $wNt$ for $t\in T$. Since $t\in L\cap\mathrm{GL}_n(\mathcal O)$ normalizes $N_E$, the substitution $k\mapsto t^{-1}kt$ gives $g(wut)=\operatorname{avg}_{N_E}h_{f,t}(u)$ for $u\in N$. If $u=ak$ with $a\in A$ and $k\in N_E$, then by left covariance and right invariance this equals $\theta(a)\operatorname{avg}_{N_E}h_{f,t}(1)$, which vanishes: the average at level $e_t$ vanishes by Lemma 7.3m, and passing to the larger level $E$ multiplies a $B$-average of it by a positive constant as in the proof of that lemma. If $u\notin AN_E$ then every term $h_{f,t}(uk)$ vanishes by cell support at level $e_t\le E$.

Second, $g$ vanishes on $C_w$. Write a point as $pwq$ and $q=n_0m_0$ with $n_0\in N$, $m_0\in L$, then $m_0=btk$ with $b\in D$, $t\in T$ and $k\in L\cap K_j$. Then
$$
pwq=\bigl(p\,wbw^{-1}\bigr)\,\bigl(w\,n_1\,t\bigr)\,k,\qquad n_1=b^{-1}n_0b\in N .
$$
The element $k$ fixes $f$ on the right and normalizes $N_E$, so it fixes $g$ on the right. The first factor lies in $P$ and acts through $\tau$. Hence $g(pwq)=\tau(p\,wbw^{-1})g(wn_1t)=0$ by the first step. Therefore $g$ vanishes off $Y\setminus C_w$.

Third, writing the average as a sum over representatives $n_q$ of the cosets of the right stabilizer of $f$ in $N_E$,
$$
f-g=\frac{1}{[N_E:N_E\cap\mathrm{Stab}(f)]}\sum_q\bigl(f-\pi(n_q)f\bigr),
$$
which is the required combination. For the converse, if $f$ vanishes on $C_w$ then every cell function $h_{f,m}$ vanishes identically and so does every level evaluation. $\square$

Together with Theorem 7.3l this gives the consumer what it needs: the cell map on $\mathcal I_Y$ induces, modulo $N$-coinvariants, a surjection onto $\mathcal J_w$ whose kernel is the image of $\mathcal I_{Y\setminus C_w}$. The passage from this statement to the graded pieces of the filtration is read in [§7.4.3.4](#7434-from-one-cell-to-the-full-bruhat-filtration); the normalization by the half-modulus and the identification of $\mathcal J_w$ with the induced row Jacquet module are the transports of Proposition 7.3g.

**Example 4 (the open $(2,1)$ cell of $\mathrm{GL}_3$).** Keep the setting of Example 2, with $P=Q$ of type $(2,1)$, $w=(23)$, $\sigma=\chi\circ\det\boxtimes\eta$ unramified, $n(x,y)=1+xE_{13}+yE_{23}$, $A$ the $x$-axis, $D=B_2\times\mathrm{GL}_1$, and $L=\mathrm{GL}_2\times\mathrm{GL}_1$. The cell is open, so $Y=C_w$ is a frame and $Y\setminus C_w$ is empty. Here $\theta$ is trivial, so $E=W$ and $p_A$ is the identity; $A$-covariance says every cell function is constant in $x$. The last target block has rank $2$, so the levels are $N_e=n(\varpi^{-2e}\mathcal O,\varpi^{-2e}\mathcal O)$ and $c_{N_e}=q^{2e}$, the volume of the image $\varpi^{-2e}\mathcal O$ in the $y$-line.

*Bump.* Fix $J\ge1$ and a vector $v$. The bump $f_1=b_{w,K_J,v}$ has cell function $h_{f_1,1}(n(x,y))=v\,1_{\varpi^J\mathcal O}(y)$: the condition $wn(x,y)\in PwK_J$ means $n(x,y)\in (w^{-1}Pw)K_J$, and $w^{-1}Pw$ is the set of matrices with zero entries at $(2,1)$ and $(2,3)$; if $n(x,y)=mk$ then the second row of $k$ is $\mu(0,1,y)$ with $\mu\in1+\varpi^J\mathcal O$, forcing $y\in\varpi^J\mathcal O$, while for such $y$ the factorization $n(x,y)=n(x,0)\,n(0,y)$ with $n(x,0)\in A$ and $n(0,y)\in K_J$ exhibits the point in the tube. Averaging $f_1$ over $Q\cap K_J$ on the right does not change this cell function: for $k\in Q\cap K_J$, $wn(x,y)k\in PwK_J$ exactly when $wn(x,y)\in PwK_J$, and the value is again $v$. So $F=f_1$ on $wN$ and
$$
J_wF(1)=c_{N_e}\operatorname{avg}_{N_e}h_{F,1}(1)=\int_{\varpi^{-2e}\mathcal O}1_{\varpi^J\mathcal O}(y)\,dy\;v=q^{-J}v,
$$
independent of $e\ge0$. Every term in the average is $v$ or $0$, as Lemma 7.3j predicts, and $c=q^{-J}$.

*Surjectivity with disjoint bumps.* The base, the quotient of $L$ by $D$, is the quotient of $\mathrm{GL}_2(F)$ by $B_2$, that is, the projective line, via the bottom row of the $\mathrm{GL}_2$ factor. A set $T$ with $L=D\,T\,(L\cap K_1)$ is a set of representatives of $\mathbb P^1(\mathbb F_q)$, for instance the $q$ matrices $\begin{pmatrix}1&0\\ \lambda&1\end{pmatrix}$ with $\lambda$ running over lifts of $\mathbb F_q$ and the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, each paired with $1\in\mathrm{GL}_1$. The sets $Dt(L\cap K_1)$ are the preimages of the $q+1$ points of $\mathbb P^1(\mathbb F_q)$ under reduction of the bottom row, hence pairwise disjoint. A function $\varphi\in\mathcal J_w$ invariant under $L\cap K_1$ is determined by its $q+1$ values $\varphi(t)$, each bump $\chi_t$ equals $\varphi$ on $Dt(L\cap K_1)$ and vanishes elsewhere, and $\varphi=\sum_t\chi_t$ with no subtraction needed.

*Kernel.* Let $t_\varpi=\operatorname{diag}(1,1,\varpi)$, central in $L$. Then $n(x,y)t_\varpi=t_\varpi n(\varpi x,\varpi y)$ and $wt_\varpi w^{-1}=\operatorname{diag}(1,\varpi,1)\in P$ with $\tau(\operatorname{diag}(1,\varpi,1))=q^{-1/2}\chi(\varpi)$. So the right translate $\pi(t_\varpi)f_1$ has cell function $q^{-1/2}\chi(\varpi)v\,1_{\mathcal O}(y)$ when $J=1$. Put
$$
f=q^{1/2}\chi(\varpi)^{-1}\pi(t_\varpi)f_1-q\,f_1,\qquad h_{f,1}(n(x,y))=v\bigl(1_{\mathcal O}(y)-q\,1_{\varpi\mathcal O}(y)\bigr).
$$
The integral in $y$ is $1-q\cdot q^{-1}=0$, and the support of $f$ in the $L$ direction lies in $D(L\cap K_1)$ because both bumps have that property, so $J_wf$ vanishes identically. The kernel theorem predicts that $f$ is a combination of $N$-differences with $g=0$. Indeed, at level $E=0$ the average over $N_0=n(\mathcal O,\mathcal O)$ of $h_{f,1}$ at $n(x_0,y_0)$ is $\int_{y_0+\mathcal O}(1_{\mathcal O}-q1_{\varpi\mathcal O})\,dy\;v$, which is $0$ for $y_0\in\mathcal O$ and $0$ by support otherwise; on the other slices $wNt$ with $t\in T$ outside $D(L\cap K_1)$ the function $f$ vanishes identically. Hence $g=\operatorname{avg}_{N_0}f=0$ and, since $f$ is right invariant under $N\cap K_1$,
$$
f=q^{-2}\sum_{(x,y)\in(\mathcal O/\varpi)^2}\bigl(f-\pi(n(x,y))f\bigr),
$$
the sum running over the $q^2$ cosets of $N\cap K_1$ in $N_0$. The averaging in the $x$ direction is harmless because every cell function is constant in $x$; it is what makes one level $N_E$ serve all slices at once.

**Example 5 (why compact support is needed).** Both suppliers rest on the eventual constancy of the level evaluations $\operatorname{ev}_{N_e}$, which holds for $f\in\mathcal I_Y$ because a support level exists. The spherical sections of the two principal series are not in $\mathcal I_Y$ for the open cell, since they do not vanish on the closed cell, and their level evaluations never become constant.

For $\mathrm{GL}_2$ with $\chi_1,\chi_2$ unramified unitary and $f_0$ the spherical section with $f_0(1)=v$, the decomposition $su(x)=\begin{pmatrix}x^{-1}&1\\0&x\end{pmatrix}\begin{pmatrix}-1&0\\x^{-1}&1\end{pmatrix}$ for $|x|>1$ gives $f_0(su(x))=|x|^{-1}\chi_1(x)^{-1}\chi_2(x)v$, and $f_0(su(x))=v$ for $|x|\le1$. With $\alpha=\chi_1^{-1}\chi_2(\varpi^{-1})$ the shell $|x|=q^k$ contributes $(1-q^{-1})\alpha^k$, so
$$
\operatorname{ev}_{N_e}(f_0,1)=\Bigl(1+(1-q^{-1})\sum_{k=1}^{e}\alpha^k\Bigr)v .
$$
Consecutive values differ by $(1-q^{-1})\alpha^{e+1}v\ne0$, so there is no eventual value; for $\chi_1=\chi_2$ the evaluations grow linearly in $e$.

For the open $(2,1)$ cell of $\mathrm{GL}_3$ and the spherical section $f_0$ with $\sigma=\chi\circ\det\boxtimes\eta$ unramified unitary, the decomposition for $|y|>1$ is
$$
wn(x,y)=\begin{pmatrix}1&x/y&x\\0&y^{-1}&1\\0&0&y\end{pmatrix}
\begin{pmatrix}1&0&0\\0&-1&0\\0&y^{-1}&1\end{pmatrix},
$$
where the first factor is $p$ with Levi part $g=\begin{pmatrix}1&x/y\\0&y^{-1}\end{pmatrix}$ and $d=y$, and the second factor is integral with unit determinant. Thus $\delta_P(p)=|\det g|\,|d|^{-2}=|y|^{-3}$ and $f_0(wn(x,y))=|y|^{-3/2}\chi(y)^{-1}\eta(y)v$, independent of $x$ as $A$-covariance requires. With $\alpha=\chi^{-1}\eta(\varpi^{-1})$ and $z=\alpha q^{-1/2}$, the shell $|y|=q^k$ contributes $(1-q^{-1})z^k$, and the level $N_e=n(\varpi^{-2e}\mathcal O,\varpi^{-2e}\mathcal O)$ reaches the shell $k=2e$, so
$$
\operatorname{ev}_{N_e}(f_0,1)=\Bigl(1+(1-q^{-1})\sum_{k=1}^{2e}z^k\Bigr)v .
$$
These values converge absolutely, but consecutive values differ by $(1-q^{-1})z^{2e+1}(1+z)v$, which is nonzero because $0<|z|<1$, so again no level is final. For instance $q=4$, $\alpha=1$ and $e=1$ give the coefficient $25/16$. The two failures are different: divergence or oscillation in $\mathrm{GL}_2$, convergence without stabilization in $\mathrm{GL}_3$. The archive's cell map is defined through an eventual value, so it excludes both. The convergent $\mathrm{GL}_3$ integral is the classical intertwining integral, and it is recovered in the archive only after the spherical section is cut off along the closed cell, that is, through the filtration rather than through a single cell.

**Notes on the proofs and their use.** Bernstein and Zelevinsky prove the fiber isomorphism in §5.17 by reducing to the regular representation, where both sides are one-dimensional, and then using free resolutions and the exactness of both functors. The archive avoids exactness and resolutions: Theorem 7.3l builds preimages from finitely many bumps, and Theorem 7.3n exhibits the kernel by a single averaged difference. The positivity argument of Lemmas 7.3j and 7.3k, which shows that a bump has nonzero image because all its averaged terms project to nonnegative multiples of one class, has no counterpart in the paper. [Paper] [Bernstein–Zelevinsky, pp. 466–467](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0/)

The two theorems are consumed through the graded map at the two assembly sites named at the start of this subsection. The surjectivity input is passed unchanged, and the kernel input is the hypothesis of the lemma that the graded map vanishes exactly on the image of the previous filtration piece. The declarations behind Lemma 7.3h, Lemma 7.3i, Lemma 7.3j, Lemma 7.3k, Theorem 7.3l, Lemma 7.3m and Theorem 7.3n have the read tags recorded in §7.6.1 under the [bump and kernel supply](#bump-and-kernel-supply-for-theorems-73l-and-73n). The ambient support supply `exists_cellSupp` and the orbit-map openness statement are read in [§7.4.3.5](#7435-levels-in-the-unipotent-radical-and-supports-on-a-cell), down to Mathlib's open mapping theorem. The Iwasawa decomposition of the Levi with its finite index statement, the smooth fixed-vector projection, the counting lemmas relating averages at two levels, and the filtration assembly are named inputs here; their statements were read and their bodies were not.

#### 7.4.3.4 From one cell to the full Bruhat filtration

Theorems 7.3l and 7.3n concern one cell $C_w$ inside an open set $Y$ in which it is closed. The split theta argument uses the whole Jacquet module $r_Q(i_P\sigma)$, and it needs that module filtered so that each step is the module of one cell. Three things must be supplied. The first is a finite list of the cells and an order in which every initial union is open and the next cell is closed in the following union. The second is a filtration of the Jacquet module attached to these unions. The third is an identification of each step with the single-cell module, in both directions. Bernstein and Zelevinsky take for the second item the Jacquet modules of the spaces of sections supported in the unions; these are subspaces of $r_Q(i_P\sigma)$ because the Jacquet functor is exact. The archive takes the images of the support spaces in $r_Q(i_P\sigma)$ instead. Images are subspaces without any exactness, but then the cell map has to be shown to descend to them, and that descent is the one step of the filtration at which exactness enters. This subsection reads the producers of the three items, `GeometricLemmaCells.lean`, `GeometricLemmaFiltration.lean` and `GeometricLemmaGraded.lean`, and their assembly into the geometric lemma that the split theta argument consumes.

**Example 6 (the two layers for $\mathrm{GL}_2$).** Keep the notation of Examples 1 and 3: $P=Q=B$, $\sigma=\chi_1\otimes\chi_2$, $s=(12)$, $u(x)=1+xE_{12}$ and $t=\operatorname{diag}(a,b)$. A double coset is determined by whether the lower left entry vanishes: $BsB=\{g_{21}\ne0\}$ and $B=\{g_{21}=0\}$. The height defined below is $5$ on $BsB$ and $4$ on $B$, so the order is $C_0=BsB$, $C_1=B$. The unions are $Y_1=\{g_{21}\ne0\}$ and $Y_2=G$, both stable under left and right multiplication by $B$. The filtration is $0=V_0\subset V_1\subset V_2=r_B(i_B\sigma)$, where $V_1$ is the image of the sections supported in the open cell.

*Layer 1 (open cell).* Here $A=1$ and $D=T$. The two target blocks have ranks $0$ and $1$, so $N_e=u(\varpi^{-e}\mathcal O)$ and $c_{N_e}=q^e$. For $f\in\mathcal I_{Y_1}$ the cell function $\phi(x)=f(su(x))$ is compactly supported. Indeed the support of $f$ is open and closed, its image among the cosets $Bg$ is compact and lies in the image of $Y_1$, which is the affine line $x\mapsto Bsu(x)$, and compact subsets of that line are bounded. Hence
$$
\operatorname{ev}_{N_e}(f,1)=\int_{\varpi^{-e}\mathcal O}\phi(x)\,dx,
$$
which is constant once $\varpi^{-e}\mathcal O$ contains the support of $\phi$. For the bump $b_{s,K_J,v}$ of Example 3 this holds from $e=0$, with value $q^{-J}v$. By the computation of Example 1, $J_sf(t)=|a/b|\cdot|b/a|^{1/2}\chi_1(b)\chi_2(a)\,J_sf(1)$, where $|a/b|$ is the measure multiplier $\lambda(t)$ and $|b/a|^{1/2}\chi_1(b)\chi_2(a)=\tau(sts^{-1})$. The Jacquet normalization multiplies by $\delta_B(t)^{-1/2}=|a/b|^{-1/2}$, so layer 1 is the character $t\mapsto\chi_2(a)\chi_1(b)$.

*Layer 2 (closed cell).* Here $A=N$, the quotient of $N$ by $A$ is a point and $c_{N_e}=1$. Every section lies in $\mathcal I_{Y_2}$, its cell function $u\mapsto f(um)=f(m)$ is constant, cell support holds at level $0$, and $J_1f(m)=f(m)$. The twist is $\delta_B^{-1/2}(t)\,\delta_B^{1/2}(t)\chi_1(a)\chi_2(b)$, so layer 2 is $\chi_1\otimes\chi_2$.

*Both directions.* Since $D=L=T$, each target is one-dimensional, determined by the value at $1$. On layer 1 the graded map sends the class of $f\in\mathcal I_{Y_1}$ to $\int_Ff(su(x))\,dx$, and the inverse sends $c$ to the class of $c\,q^Jb_{s,K_J,1}$. On layer 2 the graded map sends the class of $f$ to $f(1)$, and the inverse sends $c$ to the class modulo $V_1$ of any section with value $c$ at $1$, for instance $c$ times the spherical section $f_0$ with $f_0(1)=1$. The second composite is the identity on classes: if $f(1)=0$ then $f$ vanishes on $B$ by covariance, so $f\in\mathcal I_{Y_1}$ and $[f]\in V_1$. Thus $V_1\simeq\chi_2\otimes\chi_1$ is a subrepresentation with quotient $\chi_1\otimes\chi_2$. The class of the spherical section maps to $1$ in the top layer, so it is not in $V_1$; Example 5 shows that the open-cell map cannot be evaluated on $f_0$ itself.

**Example 7 (three layers for $\mathrm{GL}_3$ with $P$ of type $(2,1)$ and $Q=B$).** Let $P$ have Levi $M=\mathrm{GL}_2\times\mathrm{GL}_1$, let $Q=B$ be the upper triangular Borel subgroup, with $L=T$ and $N$ the upper unipotent group, and let $\sigma=\chi\circ\det\boxtimes\eta$ for unramified characters $\chi,\eta$. (For $P=Q$ of type $(2,1)$, as in Examples 2 and 4, there are only two cells.) Since $p_{31}=p_{32}=0$ for $p\in P$, the coset $Pg$ is determined by the line through the last row of $g$; the cosets form the projective plane of row vectors, on which $B$ acts on the right. Write $u(x,y,z)=1+xE_{12}+yE_{23}+zE_{13}$, so that $u(x,y,z)\,u(x',y',z')=u(x+x',y+y',z+z'+xy')$.

*Order.* For this pair the rank array defined below records whether the last row vanishes on its first entry and on its first two entries. There are three cells:

- $w_0$, the permutation $1\mapsto3$, $2\mapsto1$, $3\mapsto2$, with last row $(1,0,0)$ and height $9$; $C_0=\{g_{31}\ne0\}$;
- $w_1=(23)$, with last row $(0,1,0)$ and height $8$; $C_1=\{g_{31}=0\ne g_{32}\}$;
- $w_2=1$, with last row $(0,0,1)$ and height $7$; $C_2=\{g_{31}=g_{32}=0\}=P$.

The unions are $Y_1=\{g_{31}\ne0\}$, $Y_2=\{(g_{31},g_{32})\ne(0,0)\}$ and $Y_3=G$. Each is stable under left multiplication by $P$, which rescales the last row, and under right multiplication by $B$, which multiplies it by an upper triangular matrix. The cell $C_1$ is the closed subset $\{g_{31}=0\}$ of $Y_2$. On the projective plane these are the three Schubert cells: the affine plane, an affine line, and a point.

*Levels.* The target blocks of $B$ have ranks $0,1,2$, so $t_e=\operatorname{diag}(1,\varpi^{-e},\varpi^{-2e})$ and
$$
N_e=\{u(x,y,z):\ x,y\in\varpi^{-e}\mathcal O,\ z\in\varpi^{-2e}\mathcal O\},
$$
a group because $xy'\in\varpi^{-2e}\mathcal O$. Its volume is $q^{4e}$.

*Layer 1 ($w_0$, open cell).* From
$$
w_0u(x,y,z)=\begin{pmatrix}0&1&y\\0&0&1\\1&x&z\end{pmatrix}
$$
one reads $w_0^{-1}Pw_0=\{g:\ g_{12}=g_{13}=0\}$, so $A=\{u(0,y,0)\}$ and $D=T$. Now $u(x,y,z)=u(0,y,0)\,u(x,0,z)$, and $w_0u(0,y,0)w_0^{-1}=1+yE_{12}$ has trivial image under $\tau$, so the cell function of $f\in\mathcal I_{Y_1}$ is $\phi_0(x,z)=f(w_0u(x,0,z))$. It is compactly supported, since the image of $Y_1$ among the cosets $Pg$ is the affine chart $[1:x:z]$. The quotient of $N$ by $A$ has coordinates $(x,z)$, the image of $N_e$ is $\varpi^{-e}\mathcal O\times\varpi^{-2e}\mathcal O$, and $c_{N_e}=q^{4e}/q^{e}=q^{3e}$. Hence
$$
\operatorname{ev}_{N_e}(f,1)=\int_{\varpi^{-e}\mathcal O}\int_{\varpi^{-2e}\mathcal O}\phi_0(x,z)\,dz\,dx,
$$
which is constant once the box contains the support of $\phi_0$; the $z$-direction reaches the shell $|z|=q^{2e}$ at level $e$. A point $w_0u$ lies in the tube $Pw_0K_J$ exactly when its last row $(1,x,z)$ is proportional to the first row of some $k\in K_J$, that is, when $x,z\in\varpi^J\mathcal O$; then $u=u(0,y,0)\,u(x,0,z)$ with $u(x,0,z)\in K_J$ gives the value $v$. So the bump $b_{w_0,K_J,v}$, which lies in $\mathcal I_{Y_1}$ because the first row of $k$ has a unit first entry, has $\phi_0=v\,1_{\varpi^J\mathcal O}(x)\,1_{\varpi^J\mathcal O}(z)$ and the stable value $q^{-2J}v$ from $e=0$. For $t=\operatorname{diag}(t_1,t_2,t_3)$, the identity $t^{-1}u(x,y,z)t=u(xt_2/t_1,\,yt_3/t_2,\,zt_3/t_1)$ gives $\lambda(t)=|t_1|^2|t_2|^{-1}|t_3|^{-1}$, and $w_0tw_0^{-1}=\operatorname{diag}(t_2,t_3,t_1)$ gives $\tau(w_0tw_0^{-1})=|t_2t_3|^{1/2}|t_1|^{-1}\chi(t_2t_3)\eta(t_1)$. With $\delta_B(t)^{-1/2}=|t_1|^{-1}|t_3|$ the layer is
$$
t\longmapsto \eta(t_1)\,\chi(t_2)|t_2|^{-1/2}\,\chi(t_3)|t_3|^{1/2},\qquad\text{that is,}\qquad \bigl(\eta,\ \chi|\cdot|^{-1/2},\ \chi|\cdot|^{1/2}\bigr).
$$

*Layer 2 ($w_1=(23)$).* Here
$$
w_1u(x,y,z)=\begin{pmatrix}1&x&z\\0&0&1\\0&1&y\end{pmatrix},
$$
$w_1^{-1}Pw_1=\{g:\ g_{21}=g_{23}=0\}$ and $A=\{u(x,0,z)\}$. From $u(x,y,z)=u(x,0,z-xy)\,u(0,y,0)$ and the triviality of $\tau$ on $w_1Aw_1^{-1}$, the cell function of $f\in\mathcal I_{Y_2}$ is $\phi_1(y)=f(w_1u(0,y,0))$. It is compactly supported: as $|y|\to\infty$ the point $[0:1:y]$ tends to $[0:0:1]$, which lies outside the image of $Y_2$. The quotient of $N$ by $A$ is the $y$-line, the image of $N_e$ is $\varpi^{-e}\mathcal O$, $c_{N_e}=q^e$, and
$$
\operatorname{ev}_{N_e}(f,1)=\int_{\varpi^{-e}\mathcal O}\phi_1(y)\,dy .
$$
The bump $b_{w_1,K_J,v}$ lies in $\mathcal I_{Y_2}$, because the last row of $w_1k$ is the second row of $k$, whose middle entry is a unit. The last row $(0,1,y)$ of $w_1u$ is proportional to the second row of some $k\in K_J$ exactly when $y\in\varpi^J\mathcal O$, so $\phi_1=v\,1_{\varpi^J\mathcal O}(y)$, with stable value $q^{-J}v$ from $e=0$. Here $\lambda(t)=|t_2/t_3|$ and $w_1tw_1^{-1}=\operatorname{diag}(t_1,t_3,t_2)$, so $\tau(w_1tw_1^{-1})=|t_1t_3|^{1/2}|t_2|^{-1}\chi(t_1t_3)\eta(t_2)$, and the layer is $\bigl(\chi|\cdot|^{-1/2},\ \eta,\ \chi|\cdot|^{1/2}\bigr)$.

*Layer 3 ($w_2=1$, closed cell).* Here $A=N$, $c_{N_e}=1$, $\lambda=1$ and $J_1f(t)=f(t)$. Since $\tau(t)=|t_1t_2|^{1/2}|t_3|^{-1}\chi(t_1t_2)\eta(t_3)$, the layer is $\bigl(\chi|\cdot|^{-1/2},\ \chi|\cdot|^{1/2},\ \eta\bigr)$.

The three layers are the three shuffles of $(\chi|\cdot|^{-1/2},\chi|\cdot|^{1/2})$ with $\eta$ that keep the order of the first two characters: $\eta$ comes first on the open cell and last on the closed cell. The modulus part of each twist, $\delta_B^{-1/2}\lambda\,(\delta_P^{1/2}\circ\operatorname{Ad}(w_j))$, equals the row half-modulus $\delta_{B_2}^{-1/2}$ on the two coordinates that $w_j$ sends into the $\mathrm{GL}_2$ block, as the identity in the proof of Proposition 7.3g requires when $Q=B$.

*The middle layer in both directions.* The graded map $\Psi_1$ sends the class of $f\in\mathcal I_{Y_2}$ to $\int_F\phi_1(y)\,dy$. Sections supported in $Y_1$ vanish on $C_1$, so $V_1$ lies in its kernel. The inverse sends $c$ to the class of $c\,q^Jb_{w_1,K_J,1}$ modulo $V_1$. To see that it inverts $\Psi_1$ on classes, let $f\in\mathcal I_{Y_2}$ with $\int\phi_1=0$, choose $E$ such that the support of $\phi_1$ lies in $\varpi^{-E}\mathcal O$, and put $g=\operatorname{avg}_{N_E}f$. The $y$-coordinate of $u(x,y,z)k$ is $y$ plus that of $k$, so $g(w_1u(x,y,z))$ is the average of $\phi_1$ over $y+\varpi^{-E}\mathcal O$. This average is $0$ for $y\in\varpi^{-E}\mathcal O$ because the integral vanishes, and $0$ for other $y$ by support. Hence $g$ vanishes on $w_1N$, and so on $C_1=Pw_1N$. Since $Y_2B=Y_2$, $g$ is a section supported in $Y_2$, hence in $\mathcal I_{Y_1}$, while $f-g$ is a finite combination of differences $f-\pi(k)f$ with $k\in N_E$. Therefore $[f]=[g]\in V_1$. This is Theorem 7.3n in the adjacent position, where the correction term $g$ may be nonzero on the open cell. If instead the class of $f$ vanishes in $r_B(i_P\sigma)$, then $f=\sum_i(\pi(n_i)\varphi_i-\varphi_i)$ with sections $\varphi_i$ that need not be supported in $Y_2$. Averaging over a compact open subgroup of $N$ containing all $n_i$ gives the zero function and does not change $\int\phi_1$, so $\Psi_1([f])=0$. This is the descent of Lemma 7.3p below.

*A repeated character.* If $\eta=\chi|\cdot|^{1/2}$, layers 2 and 3 are the same character $(\chi|\cdot|^{-1/2},\chi|\cdot|^{1/2},\chi|\cdot|^{1/2})$, which therefore occurs twice in $r_B(i_P\sigma)$. If $\eta=\chi|\cdot|^{-1/2}$, layers 1 and 2 coincide. Otherwise the three characters are distinct.

**Definitions.** Let $\beta$ and $\gamma$ be the block labelings of $P$ and $Q$: $\beta(i)$ is the index of the block of $P$ containing the coordinate $i$, so $P$ consists of the invertible $p$ with $p_{ij}=0$ whenever $\beta(j)<\beta(i)$, and similarly for $Q$. Write $\bar\beta$ and $\bar\gamma$ for the largest labels. For $g\in G$ and integers $a,b\ge0$ let $r_g(a,b)$ be the rank of the submatrix of $g$ formed by the rows $i$ with $\beta(i)\ge a$ and the columns $j$ with $\gamma(j)\le b$. Call $r_g$ the rank array of $g$, and its height
$$
h(g)=\sum_{a=0}^{\bar\beta+1}\ \sum_{b=0}^{\bar\gamma}r_g(a,b).
$$
A height enumeration is a list $C_0,\dots,C_{k-1}$ of the double cosets $PgQ$, each appearing once, along which $h$ is non-increasing, together with permutation matrices $w_j\in C_j$. Put $Y_j=C_0\cup\dots\cup C_{j-1}$. For a smooth representation $\sigma$ of $M$, let $I$ be the space of sections, $\pi$ the right translation, $r_Q(I)$ the space of $N$-coinvariants with $L$ acting by $r_Q(m)[f]=\delta_Q(m)^{-1/2}[\pi(m)f]$, and
$$
V_j=\{[f]:\ f\in\mathcal I_{Y_j}\}\subset r_Q(I),
$$
the image of the sections vanishing off $Y_j$. Write $\rho$ for right translation on the target modules $\mathcal J_{w}$ of §7.4.3.3.

**Theorem 7.3o (rank arrays order the cells).**

1. For $p\in P$ and $q\in Q$, $r_{pgq}=r_g$.
2. For a permutation matrix $w$, with $we_j=e_{w(j)}$, $r_w(a,b)$ is the number of $j$ with $\gamma(j)\le b$ and $\beta(w(j))\ge a$. Every double coset contains a permutation matrix, and two elements with the same rank array lie in the same double coset. In particular there are finitely many double cosets and height enumerations exist.
3. The closure of $PgQ$ is contained in the union of $PgQ$ with the set of $x$ such that $h(x)<h(g)$.
4. For a height enumeration, each $Y_j$ is open with $PY_jQ=Y_j$; $Y_0$ is empty and $Y_k=G$; the closure of $C_j$ meets $Y_{j+1}$ exactly in $C_j$; and $Y_{j+1}$ minus $C_j$ is $Y_j$. Thus $Y_{j+1}$ is a frame for $C_j$ in the sense of §7.4.3.3.

*Proof.* (1) Let $p\in P$ and let $i$ be a row with $\beta(i)\ge a$. Row $i$ of $pg$ is $\sum_kp_{ik}$ times row $k$ of $g$, and $p_{ik}\ne0$ only if $\beta(k)\ge\beta(i)\ge a$. So the rows of $pg$ with label at least $a$ are obtained from those of $g$ by multiplying by the square block of $p$ on these rows and columns. That block is invertible, because the same block of $p^{-1}$ is its inverse. The columns of $gq$ with label at most $b$ are treated in the same way, and multiplication by invertible matrices preserves rank.

(2) The submatrix of $w$ has a $1$ in column $j$ exactly when $\gamma(j)\le b$ and $\beta(w(j))\ge a$, and these entries lie in distinct rows and columns; this gives the count. That every $g$ lies in some $PwQ$ is the Bruhat decomposition. The archive reduces it to the Borel case by sorting the labels and keeps that case, `exists_mem_doubleCoset_permGL`, as a named input. Suppose $w$ and $w'$ have the same counts for all $a$ and $b$. Differencing first in $b$ and then in $a$ shows that, for every pair $(a,b)$, the number of $j$ with $\beta(w(j))=a$ and $\gamma(j)=b$ is the same for $w$ and $w'$. Choose a bijection $v$ of the coordinates matching these fibres, so that $\gamma(v(j))=\gamma(j)$ and $\beta(w'(v(j)))=\beta(w(j))$ for all $j$. Then $u=w'vw^{-1}$ preserves $\beta$ and $v^{-1}$ preserves $\gamma$. A permutation matrix preserving the labels is block diagonal, so $u\in P$, $v^{-1}\in Q$ and $w'=uwv^{-1}\in PwQ$. Finally, if $r_x=r_g$, choose permutation matrices $w\in PgQ$ and $w'\in PxQ$. By (1) they have the rank arrays of $g$ and $x$, hence equal counts, so $x\in PwQ=PgQ$.

(3) If a matrix $A_0$ has rank $k$, there are matrices $L_0$ and $R_0$ with $L_0A_0R_0$ the identity of size $k$. The condition $\det(L_0AR_0)\ne0$ is open in $A$ and forces $\operatorname{rank}A\ge k$. Hence each set $\{x:\ r_x(a,b)\ge k\}$ is open, and
$$
Z_g=\{x:\ r_x(a,b)\le r_g(a,b)\text{ for all }a,b\}
$$
is closed, being an intersection of complements of such sets. By (1), $Z_g$ contains $PgQ$, hence its closure. Let $x$ be in the closure with $h(x)\ge h(g)$. The differences $r_g(a,b)-r_x(a,b)$ are nonnegative and their sum over the box $0\le a\le\bar\beta+1$, $0\le b\le\bar\gamma$ is $h(g)-h(x)\le0$, so they vanish on the box. Outside the box both arrays are determined by their values on it, since $r(a,b)=0$ for $a>\bar\beta$ and $r(a,b)=r(a,\bar\gamma)$ for $b\ge\bar\gamma$. Hence $r_x=r_g$, and $x\in PgQ$ by (2).

(4) The complement of $Y_j$ is the union of the closures of the $C_l$ with $l\ge j$. Every point outside $Y_j$ lies in some $C_l$ with $l\ge j$. Conversely, let a point of $C_{l'}$ with $l'<j$ lie in the closure of $C_l$ with $l\ge j$. The point is not in $C_l$, since the double cosets are disjoint, so by (3) $h(C_{l'})<h(C_l)$, which contradicts $h(C_{l'})\ge h(C_l)$. A finite union of closed sets is closed, so $Y_j$ is open. If a point of $Y_{j+1}$ lying in $C_l$ with $l<j$ were in the closure of $C_j$, the same comparison would give $h(C_l)<h(C_j)$; hence the closure of $C_j$ meets $Y_{j+1}$ only in $C_j$. The other assertions follow from the disjointness of the double cosets and from the fact that each $Y_j$ is a union of them. $\square$

The height is a linear extension of the closure order, and ties do no harm: by (3), two cells of equal height are never in each other's closures. For $P=Q=B$ in $\mathrm{GL}_3$ the six cells have heights $10,11,11,13,13,14$, and the two tied pairs are the two simple reflections and the two elements of length two, neither of which lies in the closure of the other. The archive proves only the inclusion (3); it does not need the converse description of the closure order by rank arrays.

**Lemma 7.3p (descent of the cell map to the image filtration).** Let $Y$ be an open set with $YQ=Y$ in which $C_w$ is closed, and let $f\in\mathcal I_Y$.

1. For every compact subgroup $K\subset Q$, $\operatorname{avg}_Kf\in\mathcal I_Y$.
2. For every compact subgroup $K\subset N$, $J_w(\operatorname{avg}_Kf)=J_wf$.
3. If the class of $f$ in $r_Q(I)$ is zero, then $J_wf=0$.

*Proof.* (1) The section $f$ is fixed on the right by an open subgroup, so its average over $K$ is a finite average of right translates and is a section. If $g\notin Y$ and $k\in K$, then $gk\notin Y$, since $gk\in Y$ would give $g\in YQ=Y$. So every term of the average vanishes at $g$.

(2) Fix $m\in L$. Writing $mk=(mkm^{-1})m$ shows that the cell function of $\operatorname{avg}_Kf$ at $m$ is an average of right translates of $h_{f,m}$:
$$
h_{\operatorname{avg}_Kf,\,m}(y)=\operatorname{avg}_{k'\in mKm^{-1}}h_{f,m}(yk') .
$$
The group $mKm^{-1}$ is a compact subgroup of $N$, because $L$ normalizes $N$. Its entries are bounded, so it lies in some level $N_{e_2}$. Choose $E\ge e_2$ at which both $f$ and $\operatorname{avg}_Kf$ have cell support; both lie in $\mathcal I_Y$ by (1). Averaging over the subgroup $mKm^{-1}$ and then over $N_E$ is the same as averaging over $N_E$. Hence $\operatorname{ev}_{N_E}(\operatorname{avg}_Kf,m)=\operatorname{ev}_{N_E}(f,m)$, and both sides are the stabilized values.

(3) The class of $f$ vanishes exactly when $f=\sum_i(\pi(n_i)\varphi_i-\varphi_i)$ for finitely many $n_i\in N$ and sections $\varphi_i\in I$, which need not lie in $\mathcal I_Y$. Every finite subset of $N$ lies in a compact open subgroup $K$ of $N$. Averaging over $K$ is linear and kills $\pi(n)\varphi-\varphi$ for $n\in K$, because a right translate by an element of $K$ has the same $K$-average. Hence $\operatorname{avg}_Kf=0$ as a function, and by (1) and (2)
$$
J_wf=J_w(\operatorname{avg}_Kf)=J_w(0)=0.\qquad\square
$$

Part (3) is where the exactness of the Jacquet functor is used in the filtration. It enters only through the key lemma behind exactness: an element of the kernel of the coinvariant map is a combination of relations from one compact open subgroup, and is therefore killed by one compact average. The same lines give a little more. The difference $f-\operatorname{avg}_Kf$ is a finite combination of differences $f-\pi(k)f$ with $k\in K$, and these lie in $\mathcal I_Y$. So a section in $\mathcal I_Y$ whose class vanishes in $r_Q(I)$ already has vanishing class in the $N$-coinvariants of $\mathcal I_Y$, and $V_j$ is isomorphic to the Jacquet module of $\mathcal I_{Y_j}$. This is the form in which Bernstein and Zelevinsky use exactness. The archive does not state the isomorphism; it uses only (3).

**Theorem 7.3q (adjacent support quotients are single-cell modules).** Let $\sigma$ be smooth and fix a height enumeration. Then $0=V_0\subset V_1\subset\dots\subset V_k=r_Q(I)$ is a filtration by $L$-subrepresentations, and for each $j$, with $\mathcal J_j=\mathcal J_{w_j}$:

1. there is a well-defined linear map $\Psi_j:V_{j+1}\to\mathcal J_j$ with $\Psi_j([f])=J_{w_j}f$ for $f\in\mathcal I_{Y_{j+1}}$, and $\Psi_j(r_Q(m)x)=\delta_Q(m)^{-1/2}\rho(m)\Psi_j(x)$ for $m\in L$;
2. $\Psi_j$ is surjective and its kernel is exactly $V_j$;
3. the map $\Phi_j$ sending $\varphi\in\mathcal J_j$ to the class modulo $V_j$ of any $f\in\mathcal I_{Y_{j+1}}$ with $J_{w_j}f=\varphi$ is well defined, and $\Phi_j$ and the map induced by $\Psi_j$ are inverse isomorphisms between $V_{j+1}/V_j$ and $\mathcal J_j$ with $L$ acting by $\delta_Q^{-1/2}\rho$. The preimage $f$ can be taken to be the finite sum of translated cell bumps from the proof of Theorem 7.3l.

*Proof.* Put $Y=Y_{j+1}$, $C=C_j$ and $w=w_j$. By Theorem 7.3o(4), $Y$ is a frame for $C$ and $Y$ minus $C$ is $Y_j$. Each $\mathcal I_{Y_i}$ is stable under right translation by $Q$, because $Y_iQ=Y_i$, so $V_i$ is stable under every $r_Q(m)$. Moreover $V_0=0$ because $Y_0$ is empty, $V_k=r_Q(I)$ because $Y_k=G$ and the coinvariant map is onto, and $V_i\subset V_{i+1}$ because $Y_i\subset Y_{i+1}$.

(1) The cell map $J_w$ is linear on $\mathcal I_Y$, since two sections have a common support level and the level evaluation is linear. If $f,f'\in\mathcal I_Y$ have the same class, then $f-f'\in\mathcal I_Y$ has class zero, and $J_w(f-f')=0$ by Lemma 7.3p(3). So $\Psi_j$ is well defined, and it is linear. For $m\in L$, $r_Q(m)[f]=\delta_Q(m)^{-1/2}[\pi(m)f]$ with $\pi(m)f\in\mathcal I_Y$. The cell function of $\pi(m)f$ at $m'$ is that of $f$ at $m'm$, so $J_w(\pi(m)f)=\rho(m)J_wf$.

(2) Surjectivity is Theorem 7.3l, whose hypotheses are the four frame conditions and the smoothness of $\sigma$. If $x=[g]$ with $g\in\mathcal I_{Y_j}$, then $g$ vanishes on $C$, so $J_wg=0$ by the converse in Theorem 7.3n; thus $V_j\subset\ker\Psi_j$. Conversely, if $\Psi_j([f])=0$, then $J_wf$ vanishes on $L$, and Theorem 7.3n gives a section $g$ vanishing off $Y_j$ such that $f-g$ is a finite combination of $N$-differences. Hence $[f]=[g]\in V_j$.

(3) If $f,f'\in\mathcal I_Y$ both have image $\varphi$, then $\Psi_j([f]-[f'])=0$ and $[f]-[f']\in V_j$ by (2). So $\Phi_j$ is well defined, and it is linear. By construction $\Psi_j\Phi_j$ is the identity. For $x=[f]\in V_{j+1}$, $\Phi_j\Psi_j(x)$ is the class of some $f'$ with $J_wf'=J_wf$, and $[f']\equiv[f]$ modulo $V_j$ by the same argument. The equivariance in (1) shows that the induced isomorphism intertwines $r_Q$ with $\delta_Q^{-1/2}\rho$. $\square$

**Theorem 7.3r (the geometric lemma, conditional form).** Let $\sigma$ be a smooth representation of $M$. The normalized Jacquet module $r_Q(i_P\sigma)$ has a filtration by $L$-subrepresentations
$$
0=V_0\subset V_1\subset\dots\subset V_k=r_Q(i_P\sigma),
$$
indexed by the double cosets of $P$ and $Q$ in an order of non-increasing height. Each quotient $V_{j+1}/V_j$ is isomorphic to the normalized cell module of $w_j$: the normalized column induction in $L$ of the normalized row Jacquet module of $\sigma$, taken for the refinement of the blocks of $P$ by those of $Q$ and transported by $w_j$. In block coordinates the cells are indexed by size matrices $b$, the nonnegative integer matrices whose row sums are the block sizes of $P$ and whose column sums are those of $Q$; here $b_{il}$ is the number of nonzero entries of the permutation matrix $w_j$ in the rows of block $i$ of $P$ and the columns of block $l$ of $Q$, and the quotient depends only on $b$. Consequently, for every irreducible representation $\tau$ of $L$, the extended multiplicity $m(\tau,r_Q(i_P\sigma))\in\mathbb N_\infty$ of Lemma 7.3w ([§7.4.3.6](#7436-composition-factors-of-a-cell-module))—the supremum of lengths of chains of disjoint subquotient steps isomorphic to $\tau$—equals the sum, over size matrices, of the extended multiplicities $m(\tau,-)$ in the cell modules; when $r_Q(i_P\sigma)$ has finite length (in particular when $\sigma$ has finite length under the Jacquet and induction finiteness clauses of `BernsteinZelevinskyFiniteness`), every term is a finite natural number and agrees with the Jordan–Hölder multiplicity in any composition series. The statement is conditional on the named inputs listed after the proof.

*Proof.* *Step 1 (order).* Theorem 7.3o. In the archive, `exists_cellEnumeration` sorts the finitely many rank arrays by height and chooses a permutation matrix in each double coset.

*Step 2 (graded pieces).* Theorem 7.3q. This is `filtration_of_cellEnumeration`: the filtration is the image filtration, the graded map is `gradedJacquetMap`, surjectivity comes from `cellJacquetMap_surjective` (Theorem 7.3l), and the kernel comes from `exists_sub_mem_ker_of_cellJacquet_eq_zero` (Theorem 7.3n) through `gradedJacquetMap_eq_zero_iff`.

*Step 3 (normalization).* `normalized_piece` composes $\Psi_j$ with two bijective intertwiners. The first moves $\delta_Q^{-1/2}$ inside the induction from $D_j$ to $L$. The second identifies the twisted coinvariant data with the normalized row Jacquet module, which is the identity $\delta_Q^{-1/2}\lambda\,(\delta_P^{1/2}\circ\operatorname{Ad}(w))=\delta_{\rm col}^{1/2}\delta_{\rm row}^{-1/2}$ of Proposition 7.3g. Composing with bijections preserves surjectivity and the kernel.

*Step 4 (block coordinates).* `jacquetOfInducedFiltration` transports the filtration from matrix coordinates to the block model and reindexes the cells by size matrices. The reindexing is a bijection because the size matrix determines the double coset and every size matrix is realized by a permutation. Each graded piece is then identified with the cell module through `cell_iso` and `cellFunctor_congr`, the transports of Proposition 7.3g.

*Step 5 (multiplicities).* `jhMult_eq` adds extended multiplicities in $\mathbb N_\infty$ along the finite filtration (`jhMult_filtration`, Lemma 7.3w(3) in [§7.4.3.6](#7436-composition-factors-of-a-cell-module)) and replaces each graded piece by the isomorphic cell module; finiteness under finite length is Lemma 7.3w(5). $\square$

The conditions are the following named inputs, whose statements were read and whose bodies were not. Theorem 7.3o uses the Bruhat decomposition for the Borel subgroup, `exists_mem_doubleCoset_permGL`. Lemma 7.3p uses the averaging identities of `GeometricLemmaAverage.lean`; its level supplies `exists_unipotentCompactG_of_isCompact`, `exists_cellSupp` with `exists_unipotentCompactG_support`, and `exists_compactOpen_unipotentRadical` are read in [§7.4.3.5](#7435-levels-in-the-unipotent-radical-and-supports-on-a-cell), down to the Iwasawa decomposition and Mathlib's open mapping theorem. Theorem 7.3q uses Theorems 7.3l and 7.3n with the named inputs listed in §7.4.3.3. Theorem 7.3r uses the normalization intertwiners `indTwistHom` and `indCongrHom`, the coordinate transports called by `jacquetOfInducedFiltration`, `cell_iso` and `cellFunctor_congr` at the read levels of §7.4.3.2; `jhMult_of_le` is read through `jhMult_exact` in [§7.4.3.6](#7436-composition-factors-of-a-cell-module).

**Example 7 through the theorem.** For $P$ of type $(2,1)$ and $Q=B$ in $\mathrm{GL}_3$ the size matrices have rows of sums $2$ and $1$ and three columns of sum $1$. They are determined by the column in which the second row has its $1$: the first column for $w_0$, the second for $w_1$ and the third for $w_2$. The row Jacquet module of $\chi\circ\det$ for the refinement $(1,1)$ is $\chi|\cdot|^{-1/2}\boxtimes\chi|\cdot|^{1/2}$, and every column induction is trivial because the blocks of $B$ have size one. The theorem therefore returns the three characters computed by hand in Example 7. For $\tau=(\chi|\cdot|^{-1/2},\eta,\chi|\cdot|^{1/2})$ with the three characters distinct, the multiplicity sum has exactly one nonzero term, the middle cell. For $\eta=\chi|\cdot|^{1/2}$ the middle and closed cells both contribute and the multiplicity is $2$.

**Notes on the proofs and their use.** *Where exactness is used.* In the filtration, the averaging form of exactness appears twice: in Lemma 7.3p(3) for the $N$-coinvariants of the whole induced space, and in Lemma 7.3m for the $A$-coinvariants of the inducing space inside Theorem 7.3n. Both call `exists_mem_coinvariantsKer`. Exactness is not used for the order (Theorem 7.3o), for surjectivity (Theorem 7.3l), for the normalization, or for the coordinate transports. The general theorem `exact_jacquetMap` is not called by any producer read here. In the archive it is called by the finite-length files, which lie outside this reading, as does the subquotient transfer used for the determinant witness in `Mix.top`; the exactness of column induction inside `CellSemis.cellSemisimplification` is read in [§7.4.3.6](#7436-composition-factors-of-a-cell-module).

*Comparison with the classical proof.* Bernstein and Zelevinsky prove in Proposition 1.9(a) (p. 445) that the Jacquet functor is exact when the unipotent group is a limit of compact subgroups. In 5.1(3) they assume that there are finitely many orbits and, citing their earlier paper, number them so that the successive unions are open; Theorem 5.2 (p. 460) states the filtration. In 5.3 (p. 461) they define the subfunctor attached to an open union by applying the Jacquet functor to the sections supported there, and note that it is a subfunctor because the functor is exact. In 5.4 they define the orbit functor as a quotient of two such subfunctors, which reduces Theorem 5.2 to one orbit at a time; exactness is used again in 5.15 and 5.17. [Paper] [Bernstein–Zelevinsky, pp. 445, 460–461, 465–467](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0/) Zelevinsky's Theorem 1.2 and its reformulation 1.3 (pp. 170–171) state the version for $\mathrm{GL}_n$. He notes that the open-union condition suffices and that the closed cell may be put last, so that the closed-cell term is a quotient of the whole Jacquet module. Section 1.6 (pp. 171–172) indexes the cells by the matrices $B(w)$ used in Theorem 7.3r. [Paper] [Zelevinsky, pp. 170–172](https://www.numdam.org/item/ASENS_1980_4_13_2_165_0/) The archive replaces the citation for the order by the rank-array argument of Theorem 7.3o, replaces exactness in 5.3 by the descent of Lemma 7.3p, and replaces 5.15–5.17 by Theorems 7.3l and 7.3n.

*Use in the split theta argument.* `geometricLemma_of_filtration` pairs this filtration, `geometricLemmaFiltration_unconditional`, with the cell semisimplification `geometricLemma_cell_semisimplification_GL` ([§7.4.3.6](#7436-composition-factors-of-a-cell-module)). The resulting package $h_G$ is passed to `Mix.top` by the split-GL wrapper of §7.4.3.1. Inside it, `Mix.cellone` applies `jhMult_eq` to write the multiplicity of the original tensor in the Jacquet module of the product as a sum over size matrices, shows that every off-diagonal term vanishes by the cell semisimplification and the callback of `Mix.top`, and evaluates the diagonal term as $1$; this is the count used in §7.4.3.2. The same sum, followed by the cell semisimplification, is how `exists_cell_of_isSubquotient` finds a cell and row constituents for a given irreducible subquotient. The proofs are the archive authors' (Alpöge with Claude). The statements, the textbook proofs, Examples 6 and 7 and the comparison are this book's. The read tags are recorded in §7.6.1 under the [filtration supply](#filtration-supply-for-theorems-73o73r).

#### 7.4.3.5 Levels in the unipotent radical and supports on a cell

Every averaging argument in §§7.4.3.3–7.4.3.4 contains the step "choose a level large enough". The cell map $J_w$ is an eventual value of level evaluations. Lemma 7.3p puts a conjugated compact subgroup into a level, Lemma 7.3m puts finitely many relation elements of $A$ into a level, and Theorem 7.3n uses one level for finitely many base points. Four kinds of objects must fit into the levels $N_e$: single elements of $N$, compact subsets of $N$, the supports of cell functions, and families of these indexed by base points $m\in L$. This subsection reads the producers of all four, in `GeometricLemmaCompact.lean`, `GeometricLemmaCellGroups.lean`, `InductionParabolicLocal.lean`, `GLnLattice.lean` and `GeometricLemmaOrbit.lean`. The reading stops at two named inputs: the Iwasawa decomposition in its sorted form, and Mathlib's open mapping theorem, from which the archive derives the openness of the orbit map onto a locally closed double coset. A common level comes from three devices. Entry bounds of matrices add under products. The conjugation weights of the torus elements $t_e$ turn an entry bound into membership in a level. Compactness turns bounds that hold point by point into one bound. The support of a section enters through a compact subset of $Q$ that carries every nonzero value of the section on the cell. The archive states the support level pointwise in $m$. Its proof gives a level that is uniform on bounded sets of base points, and its consumers never need more than finitely many base points at a time.

**Example 8 (a two-ball section on the open cell of $\mathrm{GL}_2$).** Keep the notation of Examples 1, 3 and 6, with $\chi_1,\chi_2$ unramified: $P=Q=B$, $s=(12)$, $u(x)=1+xE_{12}$, $A=1$ and $D=H=T$. The two target blocks have ranks $0$ and $1$, so $t_e=\operatorname{diag}(1,\varpi^{-e})$, $t_eu(x)t_e^{-1}=u(\varpi^ex)$ and $N_e=u(\varpi^{-e}\mathcal O)$.

*The levels.* Since $u(x)u(x')=u(x+x')$ and $\varpi^{-e}\mathcal O$ is an additive group, $N_e$ is closed under products, and the inverse of $u(x)$ is $u(-x)$. For $k=\operatorname{diag}(\alpha,\delta)$ with $\alpha,\delta\in\mathcal O^\times$ one has $ku(x)k^{-1}=u(\alpha x/\delta)$ with $|\alpha/\delta|=1$, so the integral Levi group $T\cap K_0$ normalizes every $N_e$. The element $m_k=\operatorname{diag}(\varpi^{-k},1)$ with $k\ge1$ does not: $m_ku(x)m_k^{-1}=u(\varpi^{-k}x)$, so it carries $N_e$ onto $N_{e+k}$. The levels increase, $N_e\subset N_{e+1}$, and $u(x)$ lies in $N_e$ as soon as $|x|\le q^e$.

*The section.* Let $b=b_{s,K_1,v}$ be the bump of Example 3 at level $J=1$, with cell function $v1_{\varpi\mathcal O}(x)$, and put $f=\pi(u(\varpi^{-3}))b-2b$. Right translation by $B$ preserves $\mathcal I_{Y_1}$ because $Y_1B=Y_1$, so $f\in\mathcal I_{Y_1}$. Since $su(x)u(c)=su(x+c)$, the cell function of $f$ at $1$ is
$$
\phi(x)=v\bigl(1_{-\varpi^{-3}+\varpi\mathcal O}(x)-2\cdot 1_{\varpi\mathcal O}(x)\bigr).
$$
It takes the values $v$, $-2v$ and $0$. Its support consists of two balls of radius $q^{-1}$, one around $0$ and one around $-\varpi^{-3}$. The smallest level containing the support is $N_3$: the far ball is small, but its centre has absolute value $q^3$. Accordingly the level evaluation $\operatorname{ev}_{N_e}(f,1)=\int_{\varpi^{-e}\mathcal O}\phi(x)\,dx$ equals $-2q^{-1}v$ for $e=0,1,2$ and $-q^{-1}v$ for $e\ge3$.

*Moving the base point.* For $t=\operatorname{diag}(t_1,t_2)$ one has $su(x)t=(sts^{-1})\,su(xt_2/t_1)$, so $h_{f,t}(u(x))=\tau(sts^{-1})\phi(xt_2/t_1)$. Its support is $t_1/t_2$ times the support of $\phi$. On the compact group $T\cap K_0$ the support stays inside $\varpi^{-3}\mathcal O$, so the single level $N_3$ serves every base point of $T\cap K_0$. At $m_k$ the support lies in $\varpi^{-3-k}\mathcal O$ and in no smaller ball around $0$. The level evaluations change for the last time at $e=3+k$, and the stable value is $-q^{k/2-1}\chi_2(\varpi)^{-k}v$, as the covariance of Example 6 predicts. No single level serves all of $T$.

*The support fibre and the archive's level.* For $g=t'u(y)\in B$ one has $f(sg)=\tau(st's^{-1})\phi(y)$, so $f(sg)\ne0$ forces $g\in T\,u(\varpi^{-3}\mathcal O)$. Thus $\Lambda_f=u(\varpi^{-3}\mathcal O)$ is a compact subset of $B$ of the kind produced by Proposition 7.3u below. Every element of $\Lambda_f$ and its inverse have entries of absolute value at most $q^3$. The element $m_k$ has entries of absolute value at most $q^k$, and those of $m_k^{-1}$ are at most $1$. Theorem 7.3v below then gives the level $2\cdot3+2k=6+2k$ at $m_k$, and the level $6$ on all of $T\cap K_0$. The factorization behind this level can be seen directly. If $h_{f,m_k}(u(z))\ne0$, then $u(z)m_k=m_k\,u(\varpi^kz)$ with $m_k\in H$ and $u(\varpi^kz)\in\Lambda_f$. The Levi components of the two factors are $m_k$ and $1$, the $A$-component is $1$, and the remaining factor is $m_ku(\varpi^kz)m_k^{-1}=u(z)$. Its entry $z$ has absolute value at most $q^{3+k}$, well below the bound $q^{6+2k}$ used by the archive. The archive's level is not the smallest one, and nothing downstream needs it to be.

*A consumer.* Take $K=N_0=u(\mathcal O)$ in Lemma 7.3p(2), at the base point $m_k$. The conjugate $m_kKm_k^{-1}=u(\varpi^{-k}\mathcal O)$ is the level $N_k$. The average $g=\operatorname{avg}_Kf$ has cell function $\int_{x+\mathcal O}\phi=q^{-1}v\bigl(1_{-\varpi^{-3}+\mathcal O}(x)-2\cdot 1_{\mathcal O}(x)\bigr)$ at $1$. It has the same smallest level $3$ and the same integral $-q^{-1}v$. At $m_k$ the common level of the proof of Lemma 7.3p is $E=\max(3+k,\,3+k,\,k)=3+k$, and the stable values of $f$ and $g$ agree.

**Example 9 (the open $(2,1)$ cell of $\mathrm{GL}_3$: supports along $A$).** Keep the notation of Examples 2 and 4: $P=Q$ of type $(2,1)$, $w=(23)$, $\sigma=\chi\circ\det\boxtimes\eta$ unramified, $n(x,y)=1+xE_{13}+yE_{23}$, $A=\{n(x,0)\}$ and $D=B_2\times\mathrm{GL}_1$. The target blocks have ranks $0$ and $2$, so $t_e=\operatorname{diag}(1,1,\varpi^{-2e})$, $t_en(x,y)t_e^{-1}=n(\varpi^{2e}x,\varpi^{2e}y)$ and $N_e=n(\varpi^{-2e}\mathcal O,\varpi^{-2e}\mathcal O)$. The conjugation weight is $2$, the difference of the two ranks.

*The levels.* Since $n(x,y)n(x',y')=n(x+x',y+y')$ and $n(x,y)^{-1}=n(-x,-y)$, the group $N$ is abelian and each $N_e$ is a subgroup. For $k=\operatorname{diag}(g,c)\in L$ one has $k\,n(x,y)\,k^{-1}=n(x',y')$, where the column $(x',y')$ is $c^{-1}g$ times the column $(x,y)$. If $g\in\mathrm{GL}_2(\mathcal O)$ and $c\in\mathcal O^\times$, the box $(\varpi^{-2e}\mathcal O)^2$ is preserved, so $L\cap K_0$ normalizes $N_e$. Two non-integral elements of $D$ do not. The element $t_\varpi=\operatorname{diag}(1,1,\varpi)$ carries $N_e$ onto $n(\varpi^{-2e-1}\mathcal O,\varpi^{-2e-1}\mathcal O)$, which lies strictly between $N_e$ and $N_{e+1}$ and is not a level. The shear $s_\beta=\operatorname{diag}\Bigl(\begin{pmatrix}1&\beta\\0&1\end{pmatrix},1\Bigr)$ with $|\beta|>1$ carries $n(0,y)$ to $n(\beta y,y)$. An entry bound $|x|,|y|\le q^{e}$ places $n(x,y)$ in $N_e$ because $q^e\le q^{2e}$, so the weight only enlarges the level.

*The section.* Let $f_1=b_{w,K_1,v}$, whose cell function is $v1_{\varpi\mathcal O}(y)$ by Example 4, and put $f=\pi(n(0,\varpi^{-3}))f_1-2f_1$. Since $n(x,y)n(0,c)=n(x,y+c)$, the cell function at $1$ is $h_{f,1}(n(x,y))=\phi(y)$, with the $\phi$ of Example 8 now in the variable $y$. Its support in $N$ is the set of $n(x,y)$ with $y$ in the support of $\phi$, and this set is not compact: with each such $y$ it contains the whole line $A\,n(0,y)$. It is compact modulo $A$. This is why cell support at level $e$ means vanishing off $AN_e$ and not vanishing off $N_e$. Here $AN_e$ is the set of $n(x,y)$ with $y\in\varpi^{-2e}\mathcal O$. The smallest level is therefore $2$, the first $e$ with $2e\ge3$, and $\operatorname{ev}_{N_e}(f,1)=\int_{\varpi^{-2e}\mathcal O}\phi(y)\,dy$ is $-2q^{-1}v$ for $e=0,1$ and $-q^{-1}v$ for $e\ge2$. In the $y$-direction the levels move in steps of two.

*Scaling and shearing the base point.* For $m=\operatorname{diag}(1,1,c)\in D$ one has $n(x,y)m=m\,n(xc,yc)$, $wmw^{-1}=\operatorname{diag}(1,c,1)\in P$ and $\tau(\operatorname{diag}(1,c,1))=|c|^{1/2}\chi(c)$, so $h_{f,m}(n(x,y))=|c|^{1/2}\chi(c)\phi(yc)$. For $c=\varpi^k$ with $k\ge0$ the support requires $y\in\varpi^{-3-k}\mathcal O$, the smallest level is $\lceil(3+k)/2\rceil$, and the stable value is $-q^{k/2-1}\chi(\varpi)^kv$. For the shear, $n(x,y)s_\beta=s_\beta\,n(x-\beta y,y)$ and $ws_\beta w^{-1}=1+\beta E_{13}$ lies in the unipotent radical of $P$, so $h_{f,s_\beta}(n(x,y))=\phi(y)$ and the smallest level is $2$ for every $\beta$.

*The support fibre and the archive's factorization.* By the first step in the proof of Lemma 7.3k, which applies with $J'=J=1$ to this cell by the remark after Lemma 7.3i, $f_1(wg)\ne0$ with $g\in Q$ forces $g\in H(Q\cap K_1)$. Hence $f(wg)\ne0$ forces $g\in H\Lambda_f$ with
$$
\Lambda_f=(Q\cap K_1)\cup(Q\cap K_1)\,n(0,-\varpi^{-3}),
$$
a compact set whose elements and their inverses have entries of absolute value at most $q^3$. For $m=\operatorname{diag}(1,1,\varpi^k)$ and $u=n(x,y)$ with $h_{f,m}(u)\ne0$, one admissible factorization is $um=x_Hl$ with $x_H=m\,n(x\varpi^k,0)\in H$ and $l=n(0,y\varpi^k)\in\Lambda_f$. The Levi components are $m$ and $1$, the $A$-component is $a=n(x,0)$, and the remaining factor $n(0,y)$ lies in the smallest level $N_{\lceil(3+k)/2\rceil}$. For the shear with $|\beta|=q^k$ the same recipe gives $x_H=s_\beta\,n(x-\beta y,0)$ and $l=n(0,y)$. The $A$-component is then $a=n(x-\beta y,0)$, and the remaining factor is $s_\beta n(0,y)s_\beta^{-1}=n(\beta y,y)$. This factor carries the shear: for $y$ in the ball around $-\varpi^{-3}$ it lies in $N_e$ only when $2e\ge3+k$, although the cell support level is $2$ for every $\beta$, because the factorization $n(x,y)=n(x,0)\,n(0,y)$ is also available. The two-sided entry bound of $s_\beta$ is $k$, so the archive's level $2\cdot3+2k$ covers this factor. The decomposition $u=au'$ is not unique, and the level of Theorem 7.3v bounds one particular choice.

**Definitions.** Keep the setting of §7.4.3.3: $G=\mathrm{GL}_n(F)$, $K_0=\mathrm{GL}_n(\mathcal O)$, standard block parabolic subgroups $P=MU$ and $Q=LN$, a permutation matrix $w$, the cell $C_w=PwQ$, and $H=Q\cap w^{-1}Pw=AD$ with $A=N\cap H$ and $D=L\cap H$. Write $r(i)$ for the rank of the target block containing the coordinate $i$, the number of coordinates in the target blocks before it, and recall the torus elements $t_e$ and the levels $N_e=N\cap t_e^{-1}K_0t_e$, the cell functions $h_{f,m}(y)=f(wym)$ on $N$, and cell support at level $e$, which means vanishing off $AN_e$. For an integer $\epsilon\ge0$, a matrix $X$ with entries in $F$ has entry bound $\epsilon$ if $|X_{ij}|\le q^{\epsilon}$ for all $i,j$. The archive's `EntryBound` states this as $\varpi^{\epsilon}X_{ij}\in\mathcal O$. An element $g\in G$ is $\epsilon$-bounded if $g$ and $g^{-1}$ both have entry bound $\epsilon$. Write $\mathrm{pr}_L:Q\to L$ for the Levi projection, which keeps the diagonal blocks and replaces the blocks above them by zero; it is a homomorphism with kernel $N$. For a section $f$, a support fibre is a compact set $\Lambda_f\subset Q$ such that $f(wy)\ne0$ with $y\in Q$ implies $y\in H\Lambda_f$.

**Lemma 7.3s (entry bounds).**

1. If $X$ has entry bound $\epsilon$ and $X'$ has entry bound $\epsilon'$, then $XX'$ has entry bound $\epsilon+\epsilon'$.
2. Every $g\in G$ is $\epsilon$-bounded for some $\epsilon$. For every compact $S\subset G$ there is one $\epsilon$ such that every element of $S$ is $\epsilon$-bounded.
3. If $y\in Q$ has entry bound $\epsilon$, so does $\mathrm{pr}_L(y)$.

*Proof.* (1) Each entry of $XX'$ is a finite sum of products $X_{ik}X'_{kj}$, each of absolute value at most $q^{\epsilon+\epsilon'}$, and the absolute value is ultrametric. (2) Let $U_\epsilon$ be the set of $g\in G$ with entry bound $\epsilon$. It is open, because $\mathcal O$ is open in $F$ and the entries are continuous functions on $G$. The sets $U_\epsilon$ increase with $\epsilon$, and they cover $G$ because the finitely many entries of any $g$ have finite absolute values. A compact set covered by an increasing sequence of open sets lies in one of them. Apply this to $S\cup S^{-1}$, which is compact as the union of $S$ with its image under the continuous inversion. The first statement is the case $S=\{g\}$. (3) The entries of $\mathrm{pr}_L(y)$ are entries of $y$ or zero. $\square$

Part (2) is the first place where a statement that holds point by point is made uniform, and compactness is exactly what it uses. The closed set of the matrices $m_k=\operatorname{diag}(\varpi^{-k},1)$, $k\ge0$, in $\mathrm{GL}_2(F)$ is not compact, and $m_k$ is $k$-bounded and not $(k-1)$-bounded.

**Lemma 7.3t (the levels).** Let $e\ge0$.

1. For $u\in N$, $(t_eut_e^{-1})_{ij}=\varpi^{e(r(j)-r(i))}u_{ij}$. Hence $N_e$ consists of the $u\in N$ whose entries joining target blocks of ranks $r<r'$ lie in $\varpi^{-e(r'-r)}\mathcal O$.
2. $N_e$ is a compact open subgroup of $N$, $N_e\subset N_{e'}$ for $e\le e'$, and $N$ is the union of the $N_e$.
3. If $u\in N$ is $\epsilon$-bounded, then $u\in N_\epsilon$.
4. Every $k\in L\cap K_0$ normalizes $N_e$.
5. Every compact subset of $N$ lies in some $N_e$. In particular this holds for every finite subset of $N$, every compact subgroup $K\subset N$ and every conjugate $mKm^{-1}$ with $m\in L$. If $A'\subset N$ is a closed subgroup, the groups $A'\cap N_e$ are compact open subgroups of $A'$, and every finite subset of $A'$ lies in one of them.

*Proof.* (1) The matrix $t_e$ is diagonal with entries $\varpi^{-er(i)}$, which gives the formula. An element of $N$ is the identity on the diagonal blocks and zero below them, and so is its conjugate by $t_e$. Integrality of $t_eut_e^{-1}$ is therefore the stated condition on the entries above the diagonal blocks. The inverse of $t_eut_e^{-1}$ is then integral too, since a unipotent matrix with integral entries has determinant $1$ and an integral adjugate. (2) $N_e$ is the intersection of the subgroups $N$ and $t_e^{-1}K_0t_e$. It is open in $N$ because $K_0$ is open and conjugation is a homeomorphism, and compact because $N$ is closed and $t_e^{-1}K_0t_e$ is compact. For $e\le e'$ and $r<r'$ one has $\varpi^{-e(r'-r)}\mathcal O\subset\varpi^{-e'(r'-r)}\mathcal O$. The union is $N$ by (3) and Lemma 7.3s(2) applied to a single element. (3) If $r<r'$ are the ranks of two target blocks, then $r'-r\ge1$, because the rank of a block counts the coordinates of the blocks before it. So $q^{\epsilon}\le q^{\epsilon(r'-r)}$ and (1) applies. (4) The matrix $t_e$ is a scalar on each target block, so it commutes with $L$. Hence $t_e(kuk^{-1})t_e^{-1}=k(t_eut_e^{-1})k^{-1}\in K_0$, and $kuk^{-1}\in N$ because $L$ normalizes $N$. (5) By Lemma 7.3s(2) the elements of a compact $S\subset N$ are $\epsilon$-bounded for one $\epsilon$, and (3) gives $S\subset N_\epsilon$. Finite sets are compact. The conjugate $mKm^{-1}$ is compact as a continuous image of $K$, and it lies in $N$ because $L$ normalizes $N$. For a closed subgroup $A'$, the group $A'\cap N_e$ is closed in the compact group $N_e$ and open in $A'$, and a finite subset of $A'$ lies in some $N_e$. $\square$

The archive proves (3) from bounds on both $u$ and $u^{-1}$. The proof above needs only the bound on $u$, because the inverse condition in (1) is automatic. Part (4) is where "integral" matters. Examples 8 and 9 show non-integral Levi elements that move $N_e$ onto a larger level or onto a box that is not a level.

**Proposition 7.3u (compact support fibres).** Let $Y\subset G$ be open, with the closure of $C_w$ meeting $Y$ exactly in $C_w$, and let $f\in\mathcal I_Y$. Then $f$ has a support fibre: there is a compact set $\Lambda_f\subset Q$ such that $f(wq)\ne0$ for $q\in Q$ implies $q\in H\Lambda_f$.

The proof uses two named inputs. The first is the Iwasawa decomposition $G=PK_0$. The second is the openness of the orbit map $P\times Q\to C_w$, $(p,q)\mapsto pwq$, onto a locally closed double coset. The archive derives the second from Mathlib's open mapping theorem for transitive actions of $\sigma$-compact groups on Baire spaces; a locally closed double coset is locally compact, hence a Baire space.

*Proof.* *Step 1 (the support is clopen and lies in $Y$).* The section $f$ is right invariant under an open subgroup $U'$, so it is constant on each coset $gU'$. Both the set where $f\ne0$ and the set where $f=0$ are unions of such cosets, so the support is open and closed. It lies in $Y$ because $f$ vanishes off $Y$.

*Step 2 (a compact piece of the cell).* The set $K_c=K_0\cap\{f\ne0\}\cap\overline{C_w}$ is closed in $K_0$, hence compact, and $K_c\subset\overline{C_w}\cap Y=C_w$. The cell is locally closed, being the intersection of the open set $Y$ with the closed set $\overline{C_w}$.

*Step 3 (local factorization).* Fix a compact neighbourhood $\Omega$ of $1$ in $G$. Let $c\in C_w$. Openness of the orbit map, applied with base point $c$, gives a neighbourhood $V_c$ of $c$ such that every $z\in V_c\cap C_w$ can be written $z=pcq$ with $p\in P$ and $q\in Q\cap\Omega$. This is a pointwise statement: the neighbourhood depends on $c$.

*Step 4 (uniform factorization).* Cover $K_c$ by finitely many $V_{c_1},\dots,V_{c_r}$ and write $c_i=p_iwq_i$ with $p_i\in P$ and $q_i\in Q$. The set $\Lambda=\bigcup_iq_i(Q\cap\Omega)$ is a compact subset of $Q$. Every $z\in K_c$ has the form $p\,w\,l$ with $p\in P$ and $l\in\Lambda$: if $z\in V_{c_i}$, then $z=pc_iq=(pp_i)\,w\,(q_iq)$. Compactness of $K_c$ turns the local factorizations into one compact set.

*Step 5 (from $K_c$ to all of $wQ$).* Let $q\in Q$ with $f(wq)\ne0$. By the Iwasawa decomposition, $wq=pk$ with $p\in P$ and $k\in K_0$. Covariance gives $f(wq)=\tau(p)f(k)$, so $f(k)\ne0$, and $k=p^{-1}wq$ lies in $C_w$. Hence $k\in K_c$ and $k=p'wl$ with $p'\in P$ and $l\in\Lambda$. Put $x=ql^{-1}\in Q$. Then
$$
wxw^{-1}=wql^{-1}w^{-1}=pkl^{-1}w^{-1}=pp'\in P,
$$
so $x\in H$ and $q=xl$. Take $\Lambda_f=\Lambda$. $\square$

The hypothesis on $Y$ is used only in Step 2. It puts the compact set $K_c$ inside the cell, where the orbit map can be inverted locally. Without it, $K_c$ could contain points of $\overline{C_w}$ outside $C_w$; such points are not of the form $pwl$ at all, and Step 4 fails.

**Theorem 7.3v (cell-support levels: pointwise, uniform, common).** Let $Y$ be an open set with $\overline{C_w}\cap Y=C_w$, let $f\in\mathcal I_Y$, and let $\Lambda_f$ be a support fibre of $f$. Choose $\epsilon_f$ such that every element of $\Lambda_f$ is $\epsilon_f$-bounded, which is possible by Lemma 7.3s(2).

1. Let $m\in L$ be $\epsilon_m$-bounded. If $u\in N$ and $f(wum)\ne0$, then $u=au'$ with $a\in A$ and $u'\in N_{2\epsilon_f+2\epsilon_m}$. In particular $h_{f,m}$ has cell support at level $2\epsilon_f+2\epsilon_m$.
2. (Pointwise.) For every $m\in L$ there is a level at which $h_{f,m}$ has cell support.
3. (Uniform on bounded sets.) Let $M\subset L$ be a set of base points that are all $\epsilon_M$-bounded for one $\epsilon_M$. Then the single level $2\epsilon_f+2\epsilon_M$ serves every $m\in M$. This applies to every compact $M\subset L$, and on $M=L\cap K_0$ the level $2\epsilon_f$ serves.
4. (Common levels.) Given finitely many sections $f_1,\dots,f_r\in\mathcal I_Y$, finitely many base points $m_1,\dots,m_s\in L$ and finitely many compact subgroups $K'_1,\dots,K'_t\subset N$, there is one $E$ such that every $h_{f_i,m_j}$ has cell support at level $E$ and every $m_jK'_lm_j^{-1}$ lies in $N_E$. Every $E'\ge E$ has the same property.
5. (No uniformity on $L$.) In general no single level serves all $m\in L$.

*Proof.* (1) Since $um\in Q$ and $f(w\cdot um)\ne0$, the support fibre gives $um=xl$ with $x\in H$ and $l\in\Lambda_f$. The projection $\mathrm{pr}_L$ kills $u$ and fixes $m$, so $m=\mathrm{pr}_L(x)\,\mathrm{pr}_L(l)$, that is, $\mathrm{pr}_L(x)=m\,\mathrm{pr}_L(l)^{-1}$. Put
$$
a=x\,\mathrm{pr}_L(x)^{-1},\qquad u'=\mathrm{pr}_L(x)\,l\,m^{-1}.
$$
Then $au'=xlm^{-1}=u$. The element $a$ lies in $N$, since its Levi projection is $1$. It also lies in $w^{-1}Pw$. Indeed, $w^{-1}Pw$ is the block upper group for the labels of $P$ transported by $w$, so it is defined by the vanishing of certain entries. The element $x$ satisfies these vanishing conditions, and so does $\mathrm{pr}_L(x)$, whose entries are entries of $x$ or zero. Hence $a\in N\cap w^{-1}Pw=A$, and $u'=a^{-1}u\in N$. Substituting for $\mathrm{pr}_L(x)$,
$$
u'=m\,\mathrm{pr}_L(l)^{-1}\,l\,m^{-1},\qquad u'^{-1}=m\,l^{-1}\,\mathrm{pr}_L(l)\,m^{-1}.
$$
Here $m$ and $m^{-1}$ have entry bound $\epsilon_m$, and $l$ and $l^{-1}$ have entry bound $\epsilon_f$. By Lemma 7.3s(3), $\mathrm{pr}_L(l)$ and $\mathrm{pr}_L(l)^{-1}=\mathrm{pr}_L(l^{-1})$ have entry bound $\epsilon_f$. By Lemma 7.3s(1), $u'$ and $u'^{-1}$ have entry bound $\epsilon_m+\epsilon_f+\epsilon_f+\epsilon_m$, and Lemma 7.3t(3) gives $u'\in N_{2\epsilon_f+2\epsilon_m}$.

(2) Proposition 7.3u gives $\Lambda_f$. Lemma 7.3s(2) gives $\epsilon_f$, and, for $S=\{m\}$, a bound $\epsilon_m$. Now apply (1).

(3) In (1) the level depends on $m$ only through $\epsilon_m$. A compact $M$ is $\epsilon_M$-bounded for one $\epsilon_M$ by Lemma 7.3s(2), and an integral matrix with integral inverse is $0$-bounded.

(4) Take the maximum of the finitely many levels from (2) and of the levels that Lemma 7.3t(5) provides for the compact sets $m_jK'_lm_j^{-1}$. Cell support at level $e$ implies cell support at every level $e'\ge e$, because $AN_e\subset AN_{e'}$ by Lemma 7.3t(2).

(5) In Example 8 the smallest level at $m_k$ is $3+k$. $\square$

The archive's statement is (2): `exists_unipotentCompactG_support`, repackaged as `exists_cellSupp`. Its level is $\epsilon_m+\epsilon_f+\epsilon_f+\epsilon_m$, the sum in (1). Part (4) for two sections at one base point is `exists_cellSupp_pair`. Part (3) is not stated in the archive. It is read off from the proof of (1), and no consumer uses it.

**How the consumers choose their levels.** Each consumer in §§7.4.3.3–7.4.3.4 takes its level from the statements above in one of three ways: at a single base point, as a maximum over finitely many objects, or with the normalization of Lemma 7.3t(4).

- *The cell map.* The eventual value $J_wf(m)$ exists because a support level $e_0$ at $m$ exists by (2), and the level evaluations at $m$ agree from $e_0$ on (`exists_cellEv_eventually`, `cellEv_eq_of_le`). For this reason $J_wf(m)$ is defined one base point at a time, as an eventual value, rather than through one level for all $m$. Example 8 shows that such a level would not exist.
- *Linearity.* The additivity of $J_w$ uses one level for $f$ and $g$ at the same base point, from (4).
- *Covariance under $D$.* The proof of $J_wf(dm)=\lambda(d)\overline\theta(d)J_wf(m)$ uses support levels at $m$ and at $dm$. Conjugation by $d$ carries $N_{e}$ to a compact open subgroup that is in general not a level, as $t_\varpi$ and $s_\beta$ in Example 9 show; Lemma 7.3t(5) puts it back into a level, and the maximum is taken.
- *Lemma 7.3p(2).* The proof takes a common support level $e$ of $f$ and $\operatorname{avg}_Kf$ at $m$ and a level $e_2$ with $mKm^{-1}\subset N_{e_2}$, and works at $E=\max(e,e_2)$. The base point $m$ need not be integral: only compactness of $mKm^{-1}$ is used, not normalization.
- *Lemma 7.3p(3).* A vanishing coinvariant class is a finite combination of relations, and the finitely many elements of $N$ in these relations lie in one compact open subgroup of $N$, by Lemma 7.3t(5) for finite sets (`exists_compactOpen_unipotentRadical`).
- *Lemma 7.3m.* The finitely many relation elements of $A$ lie in a compact open subgroup of $A$, by the last part of Lemma 7.3t(5). That subgroup lies in a level by the first part, and the maximum with the support level at the base point is taken.
- *Theorem 7.3n.* This is the one place where a level must serve infinitely many base points, and part (3) is not used. The proof takes the maximum $E$ of the levels at the finitely many $t\in T$. It then uses that every $k\in L\cap K_0$ normalizes $N_E$, which propagates the vanishing on $wNt$ to $wNtk$, and left covariance handles the factor in $D$.
- *Lemma 7.3k and the converse in Theorem 7.3n.* The bump supplier calls (2) at the base point under consideration and at $1$. The converse, that a section vanishing on $C_w$ has $J_w=0$, calls (2) once.
- *Proposition 7.3g.* The textbook proof in §7.4.3.2 places the union of the $S$-conjugates of a compact subgroup inside one level. That union is compact, as the image of $S\times K$ under conjugation, so this is Lemma 7.3t(5).

**Spherical sections.** The spherical section $f_0$ with $f_0(1)=v\ne0$ is the bump $b_{w,K_0,v}$ of level $0$. Its tube $PwK_0$ is all of $G$ by the Iwasawa decomposition, and $f_0(pk)=\tau(p)v$ vanishes nowhere. Hence $f_0\in\mathcal I_Y$ only for $Y=G$. Proposition 7.3u and Theorem 7.3v apply to $f_0$ exactly when $C_w$ is closed in $G$, that is, for the last cell of a height enumeration. In both examples that cell is $P$, with $w=1$ and $A=N$, and level $0$ serves every base point. For every other cell the hypothesis $f\in\mathcal I_Y$ fails. The proof then breaks at Step 2 of Proposition 7.3u: the compact set $K_0\cap\overline{C_w}$ contains points of smaller cells, such as $1\in\overline{BsB}$, and Step 3 says nothing at such points. The conclusion fails as well. By Example 5 the cell functions $f_0(su(x))=|x|^{-1}\chi_1(x)^{-1}\chi_2(x)v$ for $|x|>1$ on $\mathrm{GL}_2$ and $f_0(wn(x,y))=|y|^{-3/2}\chi(y)^{-1}\eta(y)v$ for $|y|>1$ on the $(2,1)$ cell of $\mathrm{GL}_3$ are nonzero at every point, so they vanish off no $AN_e$. Decay is no substitute. The $\mathrm{GL}_3$ cell function is integrable in $y$, yet its level evaluations never stabilize, because the archive's cell map needs vanishing off a level and not smallness. Cutting $f_0$ to a tube $PwK_J$ with $J\ge1$ gives the bump $b_{w,K_J,v}$, which lies in $\mathcal I_Y$ and has support level $0$ in both examples. The cut changes the class in $r_Q(I)$, so statements about $f_0$ itself pass through the filtration of Theorem 7.3q, where the image of its class in the top quotient is nonzero (Example 6).

**Notes on the proofs and their use.** *Where the topology is.* Everything above except two inputs is elementary and read in full: entry bounds, levels, the compact piece $K_c$ with its finite subcover, and the factorization $u=au'$. The two named inputs are the Iwasawa decomposition and the openness of the orbit map, a Baire category argument. Both are classical and enter only through Proposition 7.3u.

*Pointwise and uniform.* Uniformity is obtained in three places. Lemma 7.3s(2) uses an increasing open cover of a compact set. Step 4 of Proposition 7.3u uses a finite subcover of $K_c$. Theorem 7.3v(4) and the proof of Theorem 7.3n take maxima over finite sets. The archive never takes a cell-support level that is uniform over infinitely many base points; in Theorem 7.3n the passage from finitely many base points to all of them goes through the normalization of Lemma 7.3t(4). Theorem 7.3v(3) shows that it could do so on bounded sets, and Example 8 shows that it could not do so on all of $L$. The levels produced are not the smallest ones (Examples 8 and 9), and since cell support persists to larger levels, this costs nothing.

*Comparison with the classical setting.* Bernstein and Zelevinsky call an $l$-group $U$ a limit of compact subgroups if every compact subset of $U$ lies in a compact subgroup (1.9, p. 445). This is Lemma 7.3t(5) for the unipotent radical. It is the condition under which their Proposition 1.9(a) makes the Jacquet functor exact, and it is part of hypothesis 5.1(2) of the geometric lemma (p. 459). Their statements about orbits come from §§1.5–1.6 of their 1976 survey. An $l$-group that is countable at infinity and acts with finitely many orbits has an open orbit, and the orbit map onto it from any of its points is open; the proof is a Baire category argument. For a transitive action, the induced map from the quotient by a stabilizer is a homeomorphism (1.6). They use this for the numbering of the orbits in 5.1(3) (p. 460) and for the homeomorphism of an orbit with a quotient space in 5.14 (p. 464). [Paper] [Bernstein–Zelevinsky 1977, pp. 445, 459–460, 464](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0/) [Paper] [Bernstein–Zelevinsky 1976, §§1.5–1.6, pp. 10–11 of the Russian original](https://www.mathnet.ru/eng/rm3720) The archive's `isOpenMap_doubleCoset` is the corresponding statement for the action of $P\times Q$ on one double coset. The archive's eventual-value cell map needs a support level for each cell function, and Proposition 7.3u and Theorem 7.3v supply it. Bernstein and Zelevinsky instead apply the exact Jacquet functor to the spaces of sections supported on open unions (5.3, p. 461).

*Use and attribution.* The level supplies feed the bump and kernel suppliers of §7.4.3.3 and the descent and graded map of §7.4.3.4, and through them the filtration field of the package $h_G$ that the split theta argument passes to `Mix.top`. The proofs are the archive authors' (Alpöge with Claude). The statements, the textbook proofs, Examples 8 and 9, the consumer analysis and the comparison are this book's, and part (3) of Theorem 7.3v is this book's reading of the archive proof. The read tags are recorded in §7.6.1 under the [level and support supply](#level-and-support-supply-for-theorem-73v). Mathlib's open mapping theorem `isOpenMap_smul_of_sigmaCompact` and the sorted Iwasawa decomposition `exists_blockUpper_mul_integralGL` remain named inputs.

#### 7.4.3.6 Composition factors of a cell module

Theorem 7.3r decomposes the normalized Jacquet module $r_Q(i_P\sigma)$ along a finite filtration indexed by size matrices $b$ and identifies each graded piece with the cell module $\operatorname{cellFunctor}_{f,g}(\sigma)=\operatorname{relInd}_g(\operatorname{relJac}_f(\sigma)\circ\mathrm{swap}_c)$. For the split theta consumers, `Mix.cellone` and `exists_cell_of_isSubquotient`, this identification is only half of the geometric lemma. When $M=\prod_{i=1}^r\mathrm{GL}_{m_i}(F)$ and $\sigma=\bigotimes_{i=1}^r\rho_i$ is an exterior tensor product of smooth representations $\rho_i$ of finite length—even when each $\rho_i$ is irreducible—the normalized row Jacquet module $A_i=r_{f_i}(\rho_i)$ for the $i$-th row refinement $(b_{i1},\dots,b_{is})$ has finite length under Bernstein–Zelevinsky finiteness, but it need not be semisimple; and if some $\rho_i$ is itself a non-split finite-length extension, non-semisimplicity is present before taking coinvariants. One cannot split $A_i$ into a direct sum of irreducibles and commute a direct sum through exterior tensor products and column parabolic induction. Instead, the archive passes to multiplicities in $\mathbb N_\infty=\mathbb N\cup\{\infty\}$ and peels one composition series at a time. Four ingredients carry the proof, read here from `JhMultSubAddQuot.lean`, `PiTensorSmoothRepsExactEachFactor.lean`, `PiTensorDoublyIndexedSwapBlocksEquiv.lean`, `JordanHolderMultNormalisedInductionExact.lean` (with `SmIndCoinvariants.lean`, `InductionContragredient.lean` and `IwahoriProjSurjective.lean`), `AdditiveFamilyFunctionDeterminedConstituents.lean` and `GeometricLemmaCellSemisimplificationGL.lean`: an $\mathbb N_\infty$-valued extended multiplicity that is additive on every short exact sequence without assuming finite length (which also supplies the exact multiplicity convention of Theorem 7.3r); factorwise exactness of exterior tensor products, block swapping on doubly indexed tensors, and exactness of normalized column induction; an inductive expansion of any coordinatewise exact-additive $\mathbb N_\infty$-valued functional on finite-length tuples; and the reindexing of row-Levi irreducibles as exterior tensors of block irreducibles.

**Example 10 (two single blocks in $\mathrm{GL}_2$: a non-split self-extension on the torus).** Let $P=B=TU$ be the upper triangular Borel subgroup of $G=\mathrm{GL}_2(F)$, with two $1\times 1$ blocks ($m_1=m_2=1$) and $M=T=F^\times\times F^\times$. Write $v_F:F^\times\to\mathbb Z$ for the normalized valuation with $v_F(\varpi)=1$ and $v_F(\mathcal O^\times)=0$. Given smooth characters $\chi_1,\chi_2:F^\times\to\mathbb C^\times$, define a two-dimensional representation $E_{\chi_1}$ of $\mathrm{GL}_1(F)=F^\times$ on $\mathbb C^2$ by
$$
E_{\chi_1}(a)=\chi_1(a)\begin{pmatrix}1&v_F(a)\\0&1\end{pmatrix},\qquad a\in F^\times .
$$
Because $v_F(ab)=v_F(a)+v_F(b)$, this is a group homomorphism, and because $\ker\chi_1\cap\mathcal O^\times$ is an open subgroup of $F^\times$ on which both $\chi_1(a)=1$ and $v_F(a)=0$, every vector of $\mathbb C^2$ has an open stabilizer, so $E_{\chi_1}$ is smooth. A vector $(c_1,c_2)^\top$ with $c_2\ne 0$ is sent by $\varpi$ to $\chi_1(\varpi)(c_1+c_2,c_2)^\top$, which is not proportional to $(c_1,c_2)^\top$; hence $\mathbb Ce_1$ is the unique proper nonzero $F^\times$-invariant subspace, giving a non-split short exact sequence
$$
0\longrightarrow\chi_1\longrightarrow E_{\chi_1}\longrightarrow\chi_1\longrightarrow 0
$$
of smooth representations of finite length $2$. Its constituent multiplicities are $m(\chi_1,E_{\chi_1})=2$ and $m(\psi,E_{\chi_1})=0$ for every smooth character $\psi\ne\chi_1$. Put $\sigma=E_{\chi_1}\boxtimes\chi_2$ on $T$, a non-semisimple smooth representation of length $2$. Recall that $\mathrm{GL}_0(F)$ is the trivial group, with unique smooth irreducible representation class $\mathbf{1}_0$ (`IrrRep.det (Fin 0) 1`, `ExistsCellOfIsSubquotient.lean:145`). We compute every constituent multiplicity of $r_Q(i_B^G\sigma)$ for $Q=G$ and for $Q=B$.

*(a) One target block, $Q=G$ (infinite-dimensional induced constituents).* Here $L=G$, $r_G$ is the identity functor, and there is a single size matrix $b=\binom{1}{1}$, whose cell module is $i_B^G(E_{\chi_1}\boxtimes\chi_2)$ itself. Both row refinements are trivial ($1=1$), so $A_1=E_{\chi_1}$ and $A_2=\chi_2$. The finite support set $T\subset\mathrm{IrrCl}(\mathrm{GL}_1(F))^2$ of Theorem 7.3z consists of the single pair $s=(\chi_1,\chi_2)$, with row-multiplicity product
$$
m(\chi_1,E_{\chi_1})\,m(\chi_2,\chi_2)=2\cdot 1=2 .
$$
The single column induction is the normalized parabolic product $\chi_1\times\chi_2=i_B^G(\chi_1\boxtimes\chi_2)$. Specialize first to the reducible point $\chi_1=\chi|\cdot|^{1/2}$, $\chi_2=\chi|\cdot|^{-1/2}$ for a smooth character $\chi$. By Proposition 1.11(b) of Zelevinsky (1980, p. 175), $\chi|\cdot|^{1/2}\times\chi|\cdot|^{-1/2}$ has length $2$: its unique proper subrepresentation is the twisted Steinberg representation $\chi\,\mathrm{St}_2$, with $r_B(\chi\,\mathrm{St}_2)=\chi|\cdot|^{1/2}\boxtimes\chi|\cdot|^{-1/2}$, and its quotient is the determinant character $\chi\circ\det$, with $r_B(\chi\circ\det)=\chi|\cdot|^{-1/2}\boxtimes\chi|\cdot|^{1/2}$ (`nonempty_jac_det_equiv`, `ExistsCellOfIsSubquotient.lean:321`). In the column factor $\chi_1\times\chi_2$, both $\chi\,\mathrm{St}_2$ and $\chi\circ\det$ therefore have multiplicity $1$, and every other irreducible $\tau$ of $\mathrm{GL}_2(F)$ has multiplicity $0$. Multiplying by the row product $2$ gives all constituent multiplicities of the infinite-dimensional representation $i_B^G(E_{\chi|\cdot|^{1/2}}\boxtimes\chi|\cdot|^{-1/2})$:
$$
m\bigl(\chi\,\mathrm{St}_2,\,i_B^G\sigma\bigr)=2\cdot 1=2,\qquad
m\bigl(\chi\circ\det,\,i_B^G\sigma\bigr)=2\cdot 1=2,
$$
and $m(\tau,i_B^G\sigma)=0$ for every other irreducible $\tau$ of $\mathrm{GL}_2(F)$, of total length $4$. When instead $\chi_1\chi_2^{-1}\ne|\cdot|^{\pm 1}$, the product $\chi_1\times\chi_2$ is irreducible, so $m(\chi_1\times\chi_2,i_B^G\sigma)=2\cdot 1=2$ and $m(\tau,i_B^G\sigma)=0$ for all $\tau\not\simeq\chi_1\times\chi_2$.

*(b) Two target blocks, $Q=B$ (open and closed cells).* Now $L=T$ and `SizeMatrix((1,1),(1,1))` consists of $b_{\mathrm{op}}=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ ($w=(12)$) and $b_{\mathrm{id}}=\begin{pmatrix}1&0\\0&1\end{pmatrix}$ ($w=1$). On $b_{\mathrm{op}}$, the row refinements $(0,1)$ and $(1,0)$ give $A_1\simeq\mathbf{1}_0\boxtimes E_{\chi_1}$ and $A_2\simeq\chi_2\boxtimes\mathbf{1}_0$; the support $T_{\mathrm{op}}$ has the single $2\times 2$ array $s_{\mathrm{op}}=\begin{pmatrix}\mathbf{1}_0&\chi_1\\ \chi_2&\mathbf{1}_0\end{pmatrix}$ with row-multiplicity product $2\cdot 1=2$, and the two size-$1$ column inductions produce $\chi_2\boxtimes\chi_1$, so the open cell contributes $2$ to $\chi_2\boxtimes\chi_1$ and $0$ to every other character of $T$ (indeed the open-cell module is $\chi_2\boxtimes E_{\chi_1}$). On $b_{\mathrm{id}}$, the support $T_{\mathrm{id}}$ has the single array $s_{\mathrm{id}}=\begin{pmatrix}\chi_1&\mathbf{1}_0\\ \mathbf{1}_0&\chi_2\end{pmatrix}$ with row product $2\cdot 1=2$ and column product $\chi_1\boxtimes\chi_2$, contributing $2$ to $\chi_1\boxtimes\chi_2$ and $0$ elsewhere (the closed-cell module is $E_{\chi_1}\boxtimes\chi_2$). Summing over the two cells by Theorem 7.3r: if $\chi_1\ne\chi_2$, then
$$
m\bigl(\chi_2\boxtimes\chi_1,\,r_B(i_B\sigma)\bigr)=2+0=2,\qquad
m\bigl(\chi_1\boxtimes\chi_2,\,r_B(i_B\sigma)\bigr)=0+2=2,
$$
and $m(\tau,r_B(i_B\sigma))=0$ for all other $\tau\in\mathrm{Irr}(T)$—which at $\chi_1=\chi|\cdot|^{1/2}$, $\chi_2=\chi|\cdot|^{-1/2}$ matches applying the exact functor $r_B$ to $2[\chi\,\mathrm{St}_2]+2[\chi\circ\det]$ from (a). If $\chi_1=\chi_2=\chi$, the two cells land on the same character and add: $m(\chi\boxtimes\chi,r_B(i_B(E_\chi\boxtimes\chi)))=2+2=4$, with $0$ for every $\tau\ne\chi\boxtimes\chi$.

**Example 11 (type $(2,1)$ in $\mathrm{GL}_3$: an infinite-dimensional non-semisimple input).** Let $P=Q$ be the standard upper parabolic of type $(2,1)$ in $\mathrm{GL}_3(F)$, so $M=L=\mathrm{GL}_2(F)\times\mathrm{GL}_1(F)$, as in Examples 2, 4 and 9. Fix a smooth character $\chi$ of $F^\times$, let
$$
\pi_+=\chi|\cdot|^{1/2}\times\chi|\cdot|^{-1/2}=i_{B_2}^{\mathrm{GL}_2}\bigl(\chi|\cdot|^{1/2}\boxtimes\chi|\cdot|^{-1/2}\bigr)
$$
be the reducible length-$2$ representation $0\to\chi\,\mathrm{St}_2\to\pi_+\to\chi\circ\det\to 0$ on $\mathrm{GL}_2(F)$, and set $\sigma=\pi_+\boxtimes\eta$ on $M$ with $\eta=\chi|\cdot|^e$ ($e\in\mathbb Q$). Unlike $\chi\circ\det\boxtimes\eta$ in Example 2, $\sigma$ is infinite-dimensional and non-semisimple of length $2$, so vector-space dimension is infinite on almost every piece; Theorems 7.3r and 7.3z track the exact constituent multiplicities on $L=\mathrm{GL}_2(F)\times\mathrm{GL}_1(F)$ across the two matrices of `SizeMatrix((2,1),(2,1))`.

*Closed cell $b_{\mathrm{id}}=\begin{pmatrix}2&0\\0&1\end{pmatrix}$ ($w=1$).* Neither block is refined: $A_1\simeq\pi_+\boxtimes\mathbf{1}_0$ on $\mathrm{GL}_2\times\mathrm{GL}_0$ has the two constituents $(\chi\,\mathrm{St}_2)\boxtimes\mathbf{1}_0$ (multiplicity $1$) and $(\chi\circ\det)\boxtimes\mathbf{1}_0$ (multiplicity $1$), and $A_2\simeq\mathbf{1}_0\boxtimes\eta$ has the single constituent $\mathbf{1}_0\boxtimes\eta$ (multiplicity $1$). Thus $T_{\mathrm{id}}$ consists of the two $2\times 2$ arrays
$$
s_{\mathrm{id}}^{(1)}=\begin{pmatrix}\chi\,\mathrm{St}_2&\mathbf{1}_0\\ \mathbf{1}_0&\eta\end{pmatrix},\qquad
s_{\mathrm{id}}^{(2)}=\begin{pmatrix}\chi\circ\det&\mathbf{1}_0\\ \mathbf{1}_0&\eta\end{pmatrix},
$$
each with row-multiplicity product $1\cdot 1=1$. Both column inductions are trivial ($2+0=2$ and $0+1=1$), so the closed cell contributes multiplicity $1$ to $(\chi\,\mathrm{St}_2)\boxtimes\eta$, multiplicity $1$ to $(\chi\circ\det)\boxtimes\eta$, and $0$ to every other irreducible of $L$.

*Open cell $b_{\mathrm{op}}=\begin{pmatrix}1&1\\1&0\end{pmatrix}$ ($w=(23)$).* Row $1$ refines $\mathrm{GL}_2$ into $(1,1)$, so $A_1=r_{B_2}(\pi_+)$. By Example 6 (§7.4.3.4), $r_{B_2}(\pi_+)$ has length $2$ with constituents $\chi|\cdot|^{1/2}\boxtimes\chi|\cdot|^{-1/2}$ and $\chi|\cdot|^{-1/2}\boxtimes\chi|\cdot|^{1/2}$, each of row multiplicity $1$. Row $2$ refines $\mathrm{GL}_1$ into $(1,0)$, so $A_2\simeq\eta\boxtimes\mathbf{1}_0$ with row multiplicity $1$. Hence $T_{\mathrm{op}}$ consists of two $2\times 2$ arrays,
$$
s_{\mathrm{op}}^{(1)}=\begin{pmatrix}\chi|\cdot|^{1/2}&\chi|\cdot|^{-1/2}\\ \eta&\mathbf{1}_0\end{pmatrix},\qquad
s_{\mathrm{op}}^{(2)}=\begin{pmatrix}\chi|\cdot|^{-1/2}&\chi|\cdot|^{1/2}\\ \eta&\mathbf{1}_0\end{pmatrix},
$$
each with row-multiplicity product $1\cdot 1=1$. Reading down the columns, $s_{\mathrm{op}}^{(1)}$ induces to $(\chi|\cdot|^{1/2}\times\eta)\boxtimes\chi|\cdot|^{-1/2}$ on $\mathrm{GL}_2\times\mathrm{GL}_1$, and $s_{\mathrm{op}}^{(2)}$ induces to $(\chi|\cdot|^{-1/2}\times\eta)\boxtimes\chi|\cdot|^{1/2}$. Whether these column products reduce, and whether they collide with $b_{\mathrm{id}}$, depends on $e$:

1. *Linked exponent $\eta=\chi|\cdot|^{3/2}$ ($e=3/2$).* In $s_{\mathrm{op}}^{(1)}$, $\chi|\cdot|^{1/2}\times\chi|\cdot|^{3/2}$ has exponent difference $-1$, so by Proposition 1.11(b) of Zelevinsky (1980) it has length $2$ with subrepresentation $(\chi|\cdot|)\circ\det$ (column multiplicity $1$) and quotient $\chi|\cdot|\,\mathrm{St}_2$ (column multiplicity $1$). In $s_{\mathrm{op}}^{(2)}$, $\chi|\cdot|^{-1/2}\times\chi|\cdot|^{3/2}$ has exponent difference $-2\ne\pm 1$, so it is an irreducible principal series (column multiplicity $1$). Adding the closed cell gives five distinct irreducible constituents of $r_Q(i_P(\pi_+\boxtimes\chi|\cdot|^{3/2}))$, each with multiplicity $1$ and all others $0$ (total length $5$): $\bigl((\chi|\cdot|)\circ\det\bigr)\boxtimes\chi|\cdot|^{-1/2}$, $\bigl(\chi|\cdot|\,\mathrm{St}_2\bigr)\boxtimes\chi|\cdot|^{-1/2}$ and $\bigl(\chi|\cdot|^{-1/2}\times\chi|\cdot|^{3/2}\bigr)\boxtimes\chi|\cdot|^{1/2}$ from $b_{\mathrm{op}}$, together with $(\chi\,\mathrm{St}_2)\boxtimes\chi|\cdot|^{3/2}$ and $(\chi\circ\det)\boxtimes\chi|\cdot|^{3/2}$ from $b_{\mathrm{id}}$.
2. *Resonant exponent $\eta=\chi|\cdot|^{1/2}$ ($e=1/2$, cross-cell collision).* Now $s_{\mathrm{op}}^{(1)}$ forms $(\chi|\cdot|^{1/2}\times\chi|\cdot|^{1/2})\boxtimes\chi|\cdot|^{-1/2}$; the exponent difference is $0\ne\pm 1$, so $\chi|\cdot|^{1/2}\times\chi|\cdot|^{1/2}$ is irreducible and contributes multiplicity $1$. Meanwhile $s_{\mathrm{op}}^{(2)}$ forms $(\chi|\cdot|^{-1/2}\times\chi|\cdot|^{1/2})\boxtimes\chi|\cdot|^{1/2}$, whose first factor has exponent difference $-1$ and splits in multiplicity into $\chi\circ\det$ (subrepresentation, multiplicity $1$) and $\chi\,\mathrm{St}_2$ (quotient, multiplicity $1$)—the same two $\mathrm{GL}_2\times\mathrm{GL}_1$ irreducibles contributed by $b_{\mathrm{id}}$ at $\eta=\chi|\cdot|^{1/2}$. Adding the two cells gives three constituent classes of total length $5$:
   $$
   \begin{aligned}
   m\bigl((\chi\,\mathrm{St}_2)\boxtimes\chi|\cdot|^{1/2},\,r_Q(i_P\sigma)\bigr)&=1+1=2,\\
   m\bigl((\chi\circ\det)\boxtimes\chi|\cdot|^{1/2},\,r_Q(i_P\sigma)\bigr)&=1+1=2,\\
   m\bigl((\chi|\cdot|^{1/2}\times\chi|\cdot|^{1/2})\boxtimes\chi|\cdot|^{-1/2},\,r_Q(i_P\sigma)\bigr)&=1+0=1,
   \end{aligned}
   $$
   and $m(\tau,r_Q(i_P\sigma))=0$ for every other irreducible $\tau$ of $L$. (For $|e|\notin\{1/2,3/2\}$, such as $e=5/2$, both open-cell column products are irreducible and $r_Q(i_P\sigma)$ has length $4$, with four distinct constituents of multiplicity $1$.)

*Transitivity check.* Applying the exact functor $r_{B_2\times\mathrm{GL}_1}$ to the constituent multiset of $r_Q(i_P\sigma)$ must recover $r_B(i_P\sigma)=r_B(i_B(\chi|\cdot|^{1/2}\boxtimes\chi|\cdot|^{-1/2}\boxtimes\chi|\cdot|^e))$, whose constituent multiset consists of the six permutations of $(1/2,-1/2,e)$. At $e=3/2$, the five constituents yield $(1/2,3/2,-1/2)$, $(3/2,1/2,-1/2)$, $(-1/2,3/2,1/2)+(3/2,-1/2,1/2)$, $(1/2,-1/2,3/2)$ and $(-1/2,1/2,3/2)$, each once ($1+1+2+1+1=6$). At $e=1/2$, $(\chi\,\mathrm{St}_2)\boxtimes\chi|\cdot|^{1/2}$ (multiplicity $2$) gives $2\cdot(1/2,-1/2,1/2)$, $(\chi\circ\det)\boxtimes\chi|\cdot|^{1/2}$ (multiplicity $2$) gives $2\cdot(-1/2,1/2,1/2)$, and $(\chi|\cdot|^{1/2}\times\chi|\cdot|^{1/2})\boxtimes\chi|\cdot|^{-1/2}$ (multiplicity $1$, with $r_{B_2}$ equal to $2\cdot(1/2,1/2)$) gives $2\cdot(1/2,1/2,-1/2)$.

**Definitions.** Let $\Gamma$ be a group and let $\tau,\rho$ be complex representations of $\Gamma$ on $W,V$. For an integer $r\ge 0$, say that $\tau$ *occurs $r$ times* in $\rho$ (`OccursTimes τ ρ r`, `IsUnitarisableOfCharIff.lean:124`) if there exist $\Gamma$-subrepresentations $T_0,S_0,\dots,T_{r-1},S_{r-1}$ of $\rho$ satisfying
$$
T_0\le S_0\le T_1\le S_1\le\dots\le T_{r-1}\le S_{r-1}\qquad\text{and}\qquad S_i/T_i\simeq\tau\quad(0\le i<r).
$$
The *extended multiplicity* of $\tau$ in $\rho$ (`jhMult τ ρ`, `:128`) is the supremum
$$
m(\tau,\rho)=\sup\bigl\{r\in\mathbb N_\infty:\ \tau\text{ occurs }r\text{ times in }\rho\bigr\}\in\mathbb N_\infty,
$$
where $\mathbb N_\infty=\mathbb N\cup\{\infty\}$ (`ENat = WithTop ℕ`) carries the standard order and semiring operations: $a+\infty=\infty+a=\infty$, $0\cdot\infty=\infty\cdot 0=0$, and $a\cdot\infty=\infty\cdot a=\infty$ for $1\le a\le\infty$. The empty chain always witnesses $r=0$ (`occurs_zero`), so $m(\tau,\rho)$ is defined for every pair $(\tau,\rho)$. Say that $\tau$ is a *subquotient* of $\rho$ (`IsSubquotient τ ρ`, `:60`) if some subrepresentation $S\le\rho$ admits a surjective $\Gamma$-intertwining map onto $\tau$, and say that $\rho$ has *finite length* (`HasFiniteLength ρ`, `:117`) if $V$ is of finite length as a $\mathbb C[\Gamma]$-module, that is, both Noetherian and Artinian on $\Gamma$-subrepresentations (`hasFiniteLength_iff_wellFounded`, `HasFiniteLengthOfIsIrreducible.lean:62`). When $\Gamma$ is a topological group, `SmRep Γ` (`SmRep.lean:10`) packages a smooth complex representation of $\Gamma$, `IrrRep Γ` (`NontrivialOfIrreducible.lean:163`) packages a smooth irreducible one, and `IrrCl Γ` (`:183`) is the set of equivariant isomorphism classes of `IrrRep Γ`, with a chosen representative $c.\mathrm{rep}$ in each class $c$.

Now let $F$ be a nonarchimedean local field with integer ring $\mathcal O$ (written `k` and `KO k` in the `SmGL` files). Fix finite linearly ordered block index sets $\alpha,\beta$, finite coordinate sets $m_i$ ($i\in\alpha$), $m'_j$ ($j\in\beta$) and $c_{ij}$, and block decompositions $f_i:\bigsqcup_{j\in\beta}c_{ij}\xrightarrow{\sim}m_i$ and $g_j:\bigsqcup_{i\in\alpha}c_{ij}\xrightarrow{\sim}m'_j$, and write $\operatorname{Levi}_F(m)=\prod_{i\in\alpha}\mathrm{GL}_{m_i}(F)$. On the refined product $\prod_{i\in\alpha}\prod_{j\in\beta}\mathrm{GL}_{c_{ij}}(F)$, $\operatorname{relJac}_f(\sigma)$ (`ExistsCellOfIsSubquotient.lean:57`) is the coinvariant space of $\sigma$ for the product of row unipotent radicals $\prod_i U_{f_i}$, twisted by $\prod_i\delta_{f_i}^{-1/2}$. The homomorphism $\mathrm{swap}_c:\prod_{j\in\beta}\prod_{i\in\alpha}\mathrm{GL}_{c_{ij}}(F)\xrightarrow{\sim}\prod_{i\in\alpha}\prod_{j\in\beta}\mathrm{GL}_{c_{ij}}(F)$ (`:49`) exchanges coordinates by $(\mathrm{swap}_c(g))_{ij}=g_{ji}$. For a representation $\pi$ of $\prod_{j\in\beta}\operatorname{Levi}_F(c_{\bullet j})$, the *normalized column induction* $\operatorname{relInd}_g(\pi)$ (`:61`) twists $\pi$ by $\delta_{\mathrm{rel},g}^{1/2}=\prod_j\delta_{g_j}^{1/2}$, inflates along the Levi projection $\mathrm{relProj}_g$ of the product parabolic $P_{\mathrm{col}}=\prod_{j\in\beta}P_{g_j}\subset\operatorname{Levi}_F(m')$, and takes the smooth vectors under right translation by $\operatorname{Levi}_F(m')$. The block cell module is $\operatorname{cellFunctor}_{f,g}(\sigma)=\operatorname{relInd}_g(\operatorname{relJac}_f(\sigma)\circ\mathrm{swap}_c)$ (`:83`), and for column $j\in\beta$ and block representations $\sigma_{ij}$ of $\mathrm{GL}_{c_{ij}}(F)$, $\operatorname{multiProd}_{g_j}(( \sigma_{ij})_{i\in\alpha})=\operatorname{parInd}_{g_j}\bigl(\bigotimes_{i\in\alpha}\sigma_{ij}\bigr)$ (`IsSubquotientDetRepParInd.lean:321`) is the normalized parabolic induction on $\mathrm{GL}_{m'_j}(F)$.

**Lemma 7.3w (extended multiplicity in $\mathbb N_\infty$ and degeneration to $\mathbb N$).** Let $\Gamma$ be a group and let $\tau$ be an irreducible complex representation of $\Gamma$.

1. For every $\rho$, $m(\tau,\rho)\ne 0$ if and only if $\tau$ is a subquotient of $\rho$, and $m(\tau,\rho)$ is invariant under equivariant isomorphisms in either variable. If $\rho=0$, then $m(\tau,\rho)=0$. If $\tau'$ is irreducible, then $m(\tau,\tau')=1$ when $\tau\simeq\tau'$ and $0$ otherwise.
2. *(Exact additivity.)* For every short exact sequence $0\to\rho_1\xrightarrow{\iota}\rho\xrightarrow{p}\rho_2\to 0$ of complex $\Gamma$-representations (with no finite-length hypothesis),
   $$
   m(\tau,\rho)=m(\tau,\rho_1)+m(\tau,\rho_2)\qquad\text{in }\mathbb N_\infty .
   $$
3. *(Filtrations.)* For every finite filtration $0=S_0\le S_1\le\dots\le S_N=\rho$ by subrepresentations, $m(\tau,\rho)=\sum_{t=0}^{N-1}m(\tau,S_{t+1}/S_t)$ in $\mathbb N_\infty$.
4. *(Infinite multiplicity.)* On the countable direct sum $\rho=\bigoplus_{n=1}^\infty\tau$ (which is smooth whenever $\tau$ is smooth, for example $\tau=\mathbf{1}$ on $\mathrm{GL}_1(F)$), $\rho$ has no finite composition series and $m(\tau,\rho)=\infty$.
5. *(Degeneration under finite length.)* If $\rho$ has finite length $\ell(\rho)<\infty$, then $m(\tau,\rho)\le\ell(\rho)<\infty$; in particular $m(\tau,\rho)\in\mathbb N$, and it equals the number of factors isomorphic to $\tau$ in every composition series of $\rho$.
6. *(Finite support.)* If $\Gamma$ is a topological group and $\rho$ has finite length, then $\{c\in\mathrm{IrrCl}(\Gamma):m(c.\mathrm{rep},\rho)\ne 0\}$ is finite.

*Proof.* (1) An irreducible representation has $\bot\ne\top$ on subrepresentations, so its underlying space $W$ is nonzero (`nontrivial_of_irreducible`, `NontrivialOfIrreducible.lean:35`). If $m(\tau,\rho)\ne 0$, some $r\ge 1$ occurs, and $S_0\twoheadrightarrow S_0/T_0\simeq\tau$ exhibits $\tau$ as a subquotient; conversely, if $f:S\twoheadrightarrow\tau$ is a surjective intertwiner from $S\le\rho$, the single pair $T_0=\ker f\le S_0=S$ witnesses $r=1$, so $m(\tau,\rho)\ge 1$ (`jhMult_ne_zero_iff`, `JhMultSubAddQuot.lean:269`). Transporting chains along isomorphisms gives invariance (`jhMult_congr_left`, `jhMult_congr_right`), and $W\ne 0$ rules out surjections from $0$ (`jhMult_of_subsingleton`, `NontrivialOfIrreducible.lean:122`). If $\tau'$ is irreducible, any subquotient map from $S\le\tau'$ onto $\tau\ne 0$ forces $S=\tau'$ and has trivial kernel, so $\tau\not\simeq\tau'$ gives $m(\tau,\tau')=0$; for $\tau'=\tau$, any step $T_i\le S_i$ with $S_i/T_i\simeq\tau$ has $T_i\ne S_i$ because $W\ne 0$ (`Step.not_le`, `JhMultSubAddQuot.lean:242`), forcing $T_0=0$ and $S_0=\tau$, so no chain can have $r\ge 2$ and $m(\tau,\tau)=1$ (`jhMult_self`, `jhMult_rep_rep`).

(2) A subquotient isomorphism $S/T\simeq\tau$ on $T\le S\le\rho$ is equivalent, by $\mathbb C$-linear extension from $S$ to $V$, to a $\mathbb C$-linear map $f:V\to W$ that maps $S$ onto $W$, satisfies $f(\rho(g)v)=\tau(g)f(v)$ for $v\in S$, and has $\{v\in S:f(v)=0\}=T$ (`step_iff`, `JhMultSubAddQuot.lean:49`). Given such a step, consider $R=f(\iota(\iota^{-1}(S)))\subset W$. Equivariance of $\iota$ and of $f|_S$ makes $R$ a $\Gamma$-subrepresentation of $\tau$. Since $\tau$ is irreducible, either $R=W$ or $R=0$ (`step_dichotomy`, `:93`). If $R=W$, then $f\circ\iota$ witnesses $\iota^{-1}(S)/\iota^{-1}(T)\simeq\tau$ in $\rho_1$. If $R=0$, then any $v\in S$ with $p(v)=0$ equals $\iota(u)$ for some $u\in\iota^{-1}(S)$ by exactness $\ker p\subset\operatorname{im}\iota$, whence $f(v)=f(\iota(u))\in R=0$; thus $f|_S$ vanishes on $\ker(p|_S)$, extends linearly from $p(S)$ to $V_2$ (`exists_factor`, `:13`), and witnesses $p(S)/p(T)\simeq\tau$ in $\rho_2$. Now let $T_0\le S_0\le\dots\le T_{r-1}\le S_{r-1}$ witness $r$ occurrences of $\tau$ in $\rho$. Partition $\{0,\dots,r-1\}$ into the subset $A$ of indices where $\iota^{-1}(S_i)/\iota^{-1}(T_i)\simeq\tau$ and its complement $A^c$, whose indices satisfy $p(S_i)/p(T_i)\simeq\tau$ by the dichotomy. Since both $\iota^{-1}$ and $p$ preserve inclusion, $A$ and $A^c$ witness $|A|$ occurrences in $\rho_1$ and $|A^c|$ occurrences in $\rho_2$ (`occurs_of_finset`, `:77`), giving $r=|A|+|A^c|\le m(\tau,\rho_1)+m(\tau,\rho_2)$ and hence $m(\tau,\rho)\le m(\tau,\rho_1)+m(\tau,\rho_2)$. Conversely, given $a$ occurrences $(S_i,T_i)$ in $\rho_1$ and $b$ occurrences $(S'_j,T'_j)$ in $\rho_2$, injectivity of $\iota$ carries $(S_i,T_i)$ to steps $(\iota(S_i),\iota(T_i))$ inside $\operatorname{im}\iota=\ker p$ (`step_map`, `:132`), surjectivity of $p$ pulls $(S'_j,T'_j)$ back to steps $(p^{-1}(S'_j),p^{-1}(T'_j))$ containing $\ker p$ (`step_comap`, `:152`), and $\iota(S_{a-1})\le\ker p\le p^{-1}(T'_0)$ allows the two chains to be concatenated into $a+b$ occurrences in $\rho$ (`occurs_add`, `:162`). Taking the supremum over $a$ and $b$ gives $m(\tau,\rho_1)+m(\tau,\rho_2)\le m(\tau,\rho)$ in $\mathbb N_\infty$ (`jhMult_exact`, `:203`).

(3) Applying (2) to $0\to T\to S\to S/T\to 0$ gives $m(\tau,S)=m(\tau,T)+m(\tau,S/T)$ (`jhMult_of_le`, `NontrivialOfIrreducible.lean:109`), and induction on $N$ from $S_0=0$ gives the filtration sum (`jhMult_filtration`, `:129`).

(4) In $\rho=\bigoplus_{n=1}^\infty\tau$, the partial sums $T_i=\bigoplus_{n=1}^i\tau$ and $S_i=\bigoplus_{n=1}^{i+1}\tau$ ($0\le i<r$) satisfy $S_i/T_i\simeq\tau$ for every $r\ge 1$, so $m(\tau,\rho)=\infty$, while the strictly ascending chain $S_0<S_1<\dots$ prevents finite length.

(5) In the archive's `jhMult_ne_top` (`JhMultSubAddQuot.lean:250`), any $r=n+1\ge 1$ occurrences satisfy $T_j<S_j$ for each $j$, so $S_0<S_1<\dots<S_n$ is a strictly increasing chain of length $n$ in the $\mathbb C[\Gamma]$-submodule lattice of $\rho$, giving $n\le\ell(\rho)$ (`LTSeries.length_le_krullDim`) and $m(\tau,\rho)\le\ell(\rho)+1<\infty$. More sharply, $\rho$ admits a composition series $0=S_0\lessdot S_1\lessdot\dots\lessdot S_\ell=\rho$ with $\ell=\ell(\rho)$ irreducible quotients $S_{t+1}/S_t$ (`isIrreducible_subQuot`, `NontrivialOfIrreducible.lean:78`); applying (3) and the last assertion of (1) gives $m(\tau,\rho)=\sum_{t=0}^{\ell-1}m(\tau,S_{t+1}/S_t)\le\ell(\rho)$, equal to the number of composition factors isomorphic to $\tau$.

(6) Since $\rho$ is Artinian on subrepresentations, we argue by well-founded induction on $S\le\rho$ (`finite_constituents`, `NontrivialOfIrreducible.lean:212`). For $S=0$ the set is empty by (1). For $S\ne 0$, Noetherianity (`exists_le_covBy_of_lt`) provides a maximal proper subrepresentation $T\lessdot S$, so $S/T$ is irreducible (`isIrreducible_subQuot`). By (1), $m(c.\mathrm{rep},S/T)\ne 0$ holds for at most one class $c\in\mathrm{IrrCl}(\Gamma)$, and by (3), $m(c.\mathrm{rep},S)=m(c.\mathrm{rep},T)+m(c.\mathrm{rep},S/T)$, so the support for $S$ is contained in the union of that for $T$ with at most one class. $\square$

**Lemma 7.3x (factorwise tensor exactness, block swapping, and exactness of column induction).**

1. *(Factorwise exterior tensor exactness.)* Let $\alpha$ be finite, let $B_a$ ($a\in\alpha$) be smooth representations of topological groups $\Gamma_a$, and at one index $i\in\alpha$ let $0\to C_1\xrightarrow{\iota}C\xrightarrow{p}C_2\to 0$ be an exact sequence in $\mathrm{SmRep}(\Gamma_i)$. Updating $B$ at $i$ by $C_1,C,C_2$ and taking exterior tensor products over $a\in\alpha$ yields an exact sequence of $\prod_{a\in\alpha}\Gamma_a$-representations
   $$
   0\longrightarrow\bigotimes_{a\in\alpha}B[i\mapsto C_1]_a\xrightarrow{\;\iota'\;}\bigotimes_{a\in\alpha}B[i\mapsto C]_a\xrightarrow{\;p'\;}\bigotimes_{a\in\alpha}B[i\mapsto C_2]_a\longrightarrow 0 .
   $$
2. *(Block swap.)* For finite index sets $\alpha,\beta$ and representations $\sigma_{ij}$ of $\mathrm{GL}_{c_{ij}}(F)$, there is an equivariant isomorphism of $\prod_{j\in\beta}\prod_{i\in\alpha}\mathrm{GL}_{c_{ij}}(F)$-representations
   $$
   \Bigl(\bigotimes_{i\in\alpha}\bigotimes_{j\in\beta}\sigma_{ij}\Bigr)\circ\mathrm{swap}_c\;\xrightarrow{\;\sim\;}\;\bigotimes_{j\in\beta}\bigotimes_{i\in\alpha}\sigma_{ij}
   $$
   sending $\bigotimes_i\bigl(\bigotimes_j x_{ij}\bigr)$ to $\bigotimes_j\bigl(\bigotimes_i x_{ij}\bigr)$.
3. *(Column-induction exactness.)* Let $0\to\pi_1\xrightarrow{\iota}\pi\xrightarrow{p}\pi_2\to 0$ be an exact sequence of representations of $\prod_{j\in\beta}\operatorname{Levi}_F(c_{\bullet j})$ with $\pi$ smooth. Assuming the Iwasawa decomposition and parabolic closedness from `levi_integral_facts` together with Mathlib's open-normal-subgroup supply for profinite groups, the induced sequence $0\to\operatorname{relInd}_g(\pi_1)\xrightarrow{\iota_*}\operatorname{relInd}_g(\pi)\xrightarrow{p_*}\operatorname{relInd}_g(\pi_2)\to 0$ is exact; hence for every irreducible representation $\tau$ of $\operatorname{Levi}_F(m')$,
   $$
   m\bigl(\tau,\,\operatorname{relInd}_g(\pi)\bigr)=m\bigl(\tau,\,\operatorname{relInd}_g(\pi_1)\bigr)+m\bigl(\tau,\,\operatorname{relInd}_g(\pi_2)\bigr)\qquad\text{in }\mathbb N_\infty .
   $$

*Proof.* (1) Choose $\mathbb C$-linear maps $t:V_{C_2}\to V_C$ with $p\circ t=\mathrm{id}$ and $s_0:V_C\to V_{C_1}$ with $s_0\circ\iota=\mathrm{id}$, and set $s=s_0\circ(\mathrm{id}-t\circ p)$ (`piTensor_exact_position`, `PiTensorSmoothRepsExactEachFactor.lean:43–114`). Neither $s$ nor $t$ need be $\Gamma_i$-equivariant. Still, $s\circ\iota=\mathrm{id}$ because $p\circ\iota=0$, and for every $y\in V_C$ one has $p(y-t(p(y)))=0$, so $y-t(p(y))=\iota(u)$ for some $u\in V_{C_1}$ by exactness, whence $\iota(s(y))=\iota(s_0(\iota(u)))=\iota(u)=y-t(p(y))$, or $\iota\circ s+t\circ p=\mathrm{id}_{V_C}$. Put $f_i=\iota$, $g_i=p$, $s_i=s$, $t_i=t$, and take all four maps to be the identity at $a\ne i$. Then $\iota'=\bigotimes_a f_a$ and $p'=\bigotimes_a g_a$ are $\prod_a\Gamma_a$-intertwining maps (`piTensorHom`, `:12`), while the $\mathbb C$-linear maps $S=\bigotimes_a s_a$ and $T=\bigotimes_a t_a$ satisfy $S\circ\iota'=\mathrm{id}$ (so $\iota'$ is injective), $p'\circ T=\mathrm{id}$ (so $p'$ is surjective), and $p'\circ\iota'=0$ (the $i$-th factor of $(g_a\circ f_a)$ vanishes on every pure tensor). Moreover, because $f_a\circ s_a=\mathrm{id}=t_a\circ g_a$ for $a\ne i$ and $(f_i\circ s_i)+(t_i\circ g_i)=\mathrm{id}$, multilinearity in the single $i$-th coordinate gives $\iota'\circ S+T\circ p'=\mathrm{id}$ on pure tensors and hence on the whole tensor product (`piTensorMap_add_eq_id`, `:24`). Thus $p'(v)=0$ implies $v=\iota'(S(v))+T(0)=\iota'(S(v))$, proving $\ker p'\subset\operatorname{im}\iota'$.

(2) Choosing $\mathbb C$-bases in each $Y_{ij}$ identifies the flattened tensor product $\bigotimes_{(i,j)\in\alpha\times\beta}Y_{ij}$ linearly with $\bigotimes_{i\in\alpha}\bigotimes_{j\in\beta}Y_{ij}$ via the universal lift of the nested multilinear map (`sigmaCurry`, `sigmaCurry_tprod`, `PiExteriorTensorFlattenedIndexEquivNested.lean:41–76`). Reindexing the flattened product along $(i,j)\leftrightarrow(j,i)$ (`sigmaPairSwap`) and currying in the opposite order produces a linear equivalence sending $\bigotimes_i(\bigotimes_j x_{ij})$ to $\bigotimes_j(\bigotimes_i x_{ij})$ (`exists_pairCurrySwap`, `PiTensorDoublyIndexedSwapBlocksEquiv.lean:40–47`). On such a pure tensor, both actions apply $\sigma_{ij}(g_{ji})$ to $x_{ij}$ at every $(i,j)$, and linearity extends equivariance to the whole tensor space (`piTensor_swapBlocks_equiv`, `:50–87`).

(3) Twisting by the smooth character $\delta_{\mathrm{rel},g}^{1/2}$ (`isSmoothChar_relDeltaHalf`, `JordanHolderMultNormalisedInductionExact.lean:63`) and composing with the continuous Levi projection $\mathrm{relProj}_g$ (`LeviIntegralFacts.lean:78–90`) turns $(\iota,p)$ into an exact sequence $0\to\sigma_1\xrightarrow{\hat\iota}\sigma_0\xrightarrow{\hat p}\sigma_2\to 0$ of representations of $P_{\mathrm{col}}\subset L=\operatorname{Levi}_F(m')$, with $\sigma_0$ smooth. Composition of sections with $\hat\iota$ is injective by pointwise evaluation (`smIndMap_injective`, `JordanHolderMultNormalisedInductionExact.lean:21`), and $p_*\circ\iota_*=0$ holds pointwise. If $F\in\operatorname{relInd}_g(\pi)$ satisfies $p_*(F)=0$, then $\hat p(F(x))=0$ for every $x\in L$; exactness selects $u(x)$ with $\hat\iota(u(x))=F(x)$, and injectivity of $\hat\iota$ transfers both left $P_{\mathrm{col}}$-covariance ($\hat\iota(u(hx))=F(hx)=\sigma_0(h)F(x)=\hat\iota(\sigma_1(h)u(x))$) and right invariance under the open stabilizer of $F$ directly to $u$, so $u\in\operatorname{relInd}_g(\pi_1)$ with $\iota_*(u)=F$ without needing a separate smoothness assumption on $\pi_1$ (`exists_smIndMap_eq`, `:26–36`).

It remains to show that $p_*$ is surjective (`relInd_surjective`, `:69–95`, which projects only the first conjunct `.1` of `smInd_coinvariants`, `SmIndCoinvariants.lean:65–80`). Set $K_L=\prod_{j\in\beta}\mathrm{GL}_{m'_j}(\mathcal O)\subset L$. By `levi_integral_facts` (`LeviIntegralFacts.lean:44,91–118`), $P_{\mathrm{col}}$ is closed in $L$, $K_L$ is compact, and $L=P_{\mathrm{col}}K_L$ coordinatewise. Each factor $\mathrm{GL}_{m'_j}(\mathcal O)$ is compact and totally disconnected, so Mathlib's `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` supplies open subgroups of $K_L$ normalized by $K_L$ inside any identity neighborhood of $L$ (`exists_open_normalised_subgroup_subset`, `ExistsOpenNormalisedSubgroupSubset.lean:12–45`; `exists_normalised_pi`, `JordanHolderMultNormalisedInductionExact.lean:38–51`). Let $f\in\operatorname{relInd}_g(\pi_2)$, and choose such an open subgroup $J\le K_L$ fixing $f$ on the right. The tube $P_{\mathrm{col}}J$ is open in $L$, so $H_K=\{z\in K_L:z\in P_{\mathrm{col}}J\}$ is an open subgroup of the compact group $K_L$, of finite index. Because $K_L$ normalizes $J$, for each $z\in K_L$ the vector $w_z=f(z^{-1})$ is fixed by $P_{\mathrm{col}}\cap J$: if $h\in P_{\mathrm{col}}\cap J$, then $zhz^{-1}\in J$ fixes $f$ on the right, so $\sigma_2(h)f(z^{-1})=f(hz^{-1})=f(z^{-1}(zhz^{-1}))=f(z^{-1})$. Summing the right $z$-translates of the covariant tube bumps supported on $P_{\mathrm{col}}J$ with values $w_z$ over representatives $z$ of $K_L/H_K$ reproduces $f$, because any $x=pz'$ ($p\in P_{\mathrm{col}}$, $z'\in K_L$) hits exactly the coset of $z'^{-1}$ (`mem_span_bump`, `InductionContragredient.lean:123–168`). Thus it suffices to lift one bump at a time (`mem_of_bump`, `SmIndCoinvariants.lean:23–35`). Since $P_{\mathrm{col}}$ is closed and $J\le K_L$ is closed in compact $K_L$, the intersection $P_{\mathrm{col}}\cap J$ is compact (`:67–69`). Given a $(P_{\mathrm{col}}\cap J)$-fixed vector $w$ of $\sigma_2$, pick any $x$ with $\hat p(x)=w$. Smoothness of $\sigma_0$ makes $h\mapsto\sigma_0(h)x$ locally constant, so its image $S=\{\sigma_0(h)x:h\in P_{\mathrm{col}}\cap J\}$ on the compact group $P_{\mathrm{col}}\cap J$ is finite and nonempty (`exists_fixed_map_eq`, `IwahoriProjSurjective.lean:16–50`). Left multiplication by any $h\in P_{\mathrm{col}}\cap J$ permutes $S$, so the equal-weight arithmetic mean $v=|S|^{-1}\sum_{u'\in S}u'$ is fixed by $P_{\mathrm{col}}\cap J$, and since $\hat p(\sigma_0(h)x)=\sigma_2(h)w=w$ on all of $S$, one has $\hat p(v)=w$. Then $p_*$ maps the $v$-bump on $P_{\mathrm{col}}J$ to the $w$-bump (`smIndMap_bump`, `SmIndCoinvariants.lean:14–21`). Lemma 7.3w(2) now gives the multiplicity identity. $\square$

**Proposition 7.3y (constituent expansion of an additive family functional).** Let $\alpha$ be a finite index set, let $\Gamma_i$ ($i\in\alpha$) be topological groups, and let $\Phi:\bigl(\prod_{i\in\alpha}\mathrm{SmRep}(\Gamma_i)\bigr)\to\mathbb N_\infty$ satisfy:

1. if $B_i=0$ for some $i\in\alpha$, then $\Phi(B)=0$;
2. for every $i\in\alpha$, every tuple $B$, and every short exact sequence $0\to C_1\to C\to C_2\to 0$ in $\mathrm{SmRep}(\Gamma_i)$, $\Phi(B[i\mapsto C])=\Phi(B[i\mapsto C_1])+\Phi(B[i\mapsto C_2])$ in $\mathbb N_\infty$.

Then for every tuple $A=(A_i)_{i\in\alpha}$ in which each $A_i$ has finite length, and every finite set $T\subset\prod_{i\in\alpha}\mathrm{IrrCl}(\Gamma_i)$ such that every $t\notin T$ satisfies $m(t_i.\mathrm{rep},A_i)=0$ for at least one $i\in\alpha$,
$$
\Phi(A)=\sum_{t\in T}\Biggl(\prod_{i\in\alpha}m\bigl(t_i.\mathrm{rep},\,A_i\bigr)\Biggr)\Phi\bigl((t_i.\mathrm{rep})_{i\in\alpha}\bigr)\qquad\text{in }\mathbb N_\infty .
$$

*Proof.* First consider a single topological group $\Gamma$ and $\varphi:\mathrm{SmRep}(\Gamma)\to\mathbb N_\infty$ vanishing on zero spaces and additive on short exact sequences (`AdditiveExpand`, `AdditiveFamilyFunctionDeterminedConstituents.lean:26–99`). Applying additivity to $0\to 0\to B\xrightarrow{\sim}B'\to 0$ gives $\varphi(B)=0+\varphi(B')=\varphi(B')$, so $\varphi$ is invariant under equivariant isomorphism (`congr_equiv`, `:43`). If $B$ has finite length and $T_0\subset\mathrm{IrrCl}(\Gamma)$ is a finite set outside which $m(c.\mathrm{rep},B)=0$, well-founded induction on subrepresentations $S\le B$ shows $\varphi(S)=\sum_{c\in T_0}m(c.\mathrm{rep},S)\varphi(c.\mathrm{rep})$ (`one_coord₂`, `:53–98`): for $S=0$ both sides vanish by (1) and Lemma 7.3w(1); for $S\ne 0$, Noetherianity supplies a maximal proper subrepresentation $R\lessdot S$, so $S/R$ is smooth (`IsSubquotient.isSmooth`) and irreducible (`isIrreducible_subQuot`), representing some class $c_0\in\mathrm{IrrCl}(\Gamma)$. By Lemma 7.3w(1) and (3), $m(c.\mathrm{rep},S)=m(c.\mathrm{rep},R)+\delta_{c,c_0}$; hence $c_0\in T_0$ (whenever $m(c.\mathrm{rep},S)=0$ outside $T_0$), $\varphi(S)=\varphi(R)+\varphi(c_0.\mathrm{rep})$ by additivity on $0\to R\to S\to S/R\to 0$ and isomorphism invariance, and the induction hypothesis on $R<S$ together with $(a+b)x=ax+bx$ in $\mathbb N_\infty$ closes the step; $S=\top\simeq B$ gives the one-variable expansion.

For the general tuple, we prove the formula by induction on a finite subset $s\subset\alpha$ under the hypothesis that for every $j\notin s$ one already has $A_j=c_j.\mathrm{rep}$ for some $c_j\in\mathrm{IrrCl}(\Gamma_j)$ (`additive_family_expand`, `:103–176`). If $s=\emptyset$, then $A=(c_j.\mathrm{rep})_{j\in\alpha}$; by Lemma 7.3w(1), $\prod_i m(t_i.\mathrm{rep},c_i.\mathrm{rep})=\prod_i\delta_{t_i,c_i}=\delta_{t,c}$, and the support assumption forces $c\in T$ (otherwise $1=m(c_i.\mathrm{rep},c_i.\mathrm{rep})=0$ for some $i$), leaving the single term $\Phi((c_i.\mathrm{rep}))=\Phi(A)$. For the inductive step $s=\{i\}\cup s'$ with $i\notin s'$, let $T_i\subset\mathrm{IrrCl}(\Gamma_i)$ be the finite support of $A_i$ from Lemma 7.3w(6). Applying the one-variable expansion to $C\mapsto\Phi(A[i\mapsto C])$ gives
$$
\Phi(A)=\sum_{c\in T_i}m(c.\mathrm{rep},A_i)\,\Phi\bigl(A[i\mapsto c.\mathrm{rep}]\bigr).
$$
For each $c\in T_i$, the updated tuple $A'=A[i\mapsto c.\mathrm{rep}]$ has $A'_j$ of the form $c_j.\mathrm{rep}$ for all $j\notin s'$, still has finite-length entries (`IrrRep.hasFiniteLength`), and still has support inside $T$: if $t\notin T$ had $m(t_j.\mathrm{rep},A_j)=0$ for some $j\ne i$, that coordinate is unchanged; if $j=i$, then $m(t_i.\mathrm{rep},A_i)=0\ne m(c.\mathrm{rep},A_i)$ forces $t_i\ne c$, so $m(t_i.\mathrm{rep},c.\mathrm{rep})=0$. The induction hypothesis on $s'$ therefore expands $\Phi(A[i\mapsto c.\mathrm{rep}])$ over $t\in T$ with $i$-th factor $\delta_{t_i,c}$. Substituting, distributing $m(c.\mathrm{rep},A_i)$ into the sum over $t\in T$, and interchanging $\sum_{c\in T_i}$ with $\sum_{t\in T}$ yields, for each $t\in T$, an inner sum over $c\in T_i$: when $t_i\in T_i$, only $c=t_i$ survives and associative multiplication in $\mathbb N_\infty$ reassembles $\prod_{j\in\alpha}m(t_j.\mathrm{rep},A_j)\Phi((t_j.\mathrm{rep}))$; when $t_i\notin T_i$, the inner sum is empty and $m(t_i.\mathrm{rep},A_i)=0$, so $0\cdot\Phi((t_j.\mathrm{rep}))=0$ in $\mathbb N_\infty$ agrees as well. Taking $s=\alpha$ proves the proposition. $\square$

**Theorem 7.3z (cell constituent multiplicity formula, conditional form).** Let $F$ be a nonarchimedean local field, let $\alpha,\beta$ be finite linearly ordered block index sets, let $f_i:\bigsqcup_{j\in\beta}c_{ij}\xrightarrow{\sim}m_i$ and $g_j:\bigsqcup_{i\in\alpha}c_{ij}\xrightarrow{\sim}m'_j$ be row and column refinements, and let $\rho_i$ ($i\in\alpha$) be smooth representations of $\mathrm{GL}_{m_i}(F)$ of finite length. Conditional on the named Bernstein–Zelevinsky finiteness, exterior-tensor classification, factorwise Jacquet/induction commutation, and local Iwasawa/profinite inputs listed after the proof:

1. *(Finite support.)* There exists a finite subset $T\subset\prod_{i\in\alpha}\prod_{j\in\beta}\mathrm{IrrCl}(\mathrm{GL}_{c_{ij}}(F))$ such that for every $s\notin T$ there is $i\in\alpha$ with $m\bigl(\bigotimes_{j\in\beta}s_{ij}.\mathrm{rep},\,r_{f_i}(\rho_i)\bigr)=0$.
2. *(Product-and-sum formula in $\mathbb N_\infty$.)* For every smooth irreducible representation $\tau$ of $L=\prod_{j\in\beta}\mathrm{GL}_{m'_j}(F)$,
   $$
   \begin{aligned}
   m\Bigl(\tau,\,\operatorname{cellFunctor}_{f,g}\Bigl(\bigotimes_{i\in\alpha}\rho_i\Bigr)\Bigr)
   &=\sum_{s\in T}\Biggl(\prod_{i\in\alpha}m\Bigl(\bigotimes_{j\in\beta}s_{ij}.\mathrm{rep},\,r_{f_i}(\rho_i)\Bigr)\Biggr)\\
   &\qquad\times m\Bigl(\tau,\,\bigotimes_{j\in\beta}\operatorname{multiProd}_{g_j}\bigl((s_{ij}.\mathrm{rep})_{i\in\alpha}\bigr)\Bigr)
   \end{aligned}
   $$
   in $\mathbb N_\infty$, where every row factor $m\bigl(\bigotimes_j s_{ij}.\mathrm{rep},\,r_{f_i}(\rho_i)\bigr)$ is a finite natural number in $\mathbb N$.
3. *(Degeneration to $\mathbb N$ and subquotient extraction.)* Under the induction-finiteness clause of `BernsteinZelevinskyFiniteness`, each column factor—and hence the cell multiplicity above and, combined with Theorem 7.3r, the full Jacquet multiplicity $m\bigl(\tau,r_Q(i_P(\bigotimes_i\rho_i))\bigr)$ summed over `SizeMatrix m m'`—is a finite natural number in $\mathbb N$ equal to the Jordan–Hölder multiplicity in any composition series. Moreover (`exists_cell_of_isSubquotient`), $\tau$ is a subquotient of $r_Q(i_P(\bigotimes_i\rho_i))$ if and only if for some size matrix $b$ and some family $s_{ij}\in\mathrm{IrrRep}(\mathrm{GL}_{b_{ij}}(F))$ on the blocks of $b$, each $\bigotimes_j s_{ij}$ is a subquotient of $r_{f_i}(\rho_i)$ and $\tau$ is a subquotient of $\bigotimes_j\operatorname{multiProd}_{g_j}((s_{ij})_{i\in\alpha})$.

*Proof.* *Step 1 (row finiteness and coordinatewise exactness).* Put $A_i=r_{f_i}(\rho_i)\in\mathrm{SmRep}(\operatorname{Levi}_F(c_{i\bullet}))$ (`isSmooth_jac`), which has finite length by the `JacquetFiniteLength` clause `(hBZ F).2.1` of `BernsteinZelevinskyFiniteness` (`GeometricLemmaCellSemisimplificationGL.lean:62–64`). Fix $\tau\in\mathrm{IrrRep}(L)$ and define $\Phi_\tau:\bigl(\prod_{i\in\alpha}\mathrm{SmRep}(\operatorname{Levi}_F(c_{i\bullet}))\bigr)\to\mathbb N_\infty$ by $\Phi_\tau(B)=m\bigl(\tau,\operatorname{relInd}_g((\bigotimes_i B_i)\circ\mathrm{swap}_c)\bigr)$ (`:65–66`). If $B_i=0$, every pure tensor in $\bigotimes_a B_a$ has zero $i$-th coordinate and vanishes (`subsingleton_piTensor`, `:46–55`), so $\operatorname{relInd}_g$ acts on a zero space and $\Phi_\tau(B)=0$ by Lemma 7.3w(1) (`jhMult_relInd_of_subsingleton`, `:36–45, 70–73`). Since $\mathrm{swap}_c$ is continuous (`:67–69`), $(\bigotimes_a B_a)\circ\mathrm{swap}_c$ is smooth (`isSmooth_piTensor`, `isSmooth_comp`), and combining Lemma 7.3x(1) with Lemma 7.3x(3) shows that $\Phi_\tau$ is additive on short exact sequences in each coordinate $B_i$ (`:74–81`).

*Step 2 (finite support and block-Levi reindexing).* By Lemma 7.3w(5) and (6), each $A_i$ has finite row multiplicities in $\mathbb N$ supported on a finite set $T'_i\subset\mathrm{IrrCl}(\operatorname{Levi}_F(c_{i\bullet}))$; set $T'=\prod_{i\in\alpha}T'_i$ (`Fintype.piFinset`, `:82–89`). For each $i\in\alpha$ and $s_i\in\prod_{j\in\beta}\mathrm{IrrCl}(\mathrm{GL}_{c_{ij}}(F))$, the exterior tensor product $P_i(s_i)=\bigotimes_{j\in\beta}s_{ij}.\mathrm{rep}$ is smooth and irreducible by `piExteriorTensor_smoothIrreducible_isIrreducible` (`:90–92`). Define $\Theta:\bigl(\prod_{i,j}\mathrm{IrrCl}(\mathrm{GL}_{c_{ij}}(F))\bigr)\to\prod_i\mathrm{IrrCl}(\operatorname{Levi}_F(c_{i\bullet}))$ by $\Theta(s)_i=[P_i(s_i)]$ (`:93`). Then $\Theta$ is injective by `tensor_product_determines_factor_classes` (`:94–99`) and surjective by `exists_equiv_piExteriorTensor_blockLevi` (`:100–106`). Pulling $T'$ back along $\Theta$ gives a finite set $T=\Theta^{-1}(T')$ satisfying (1) (`:107–110`).

*Step 3 (factorwise Jacquet, additive expansion, and column identification).* Composing the isomorphism $\operatorname{relJac}_f(\bigotimes_i\rho_i)\simeq\bigotimes_i A_i$ of `relative_jacquet_functor_piTensor_equiv` with $\mathrm{swap}_c$ and transporting through $\operatorname{relInd}_g$ (`relIndEquiv`, `:25–34, 111–112`) identifies $\operatorname{cellFunctor}_{f,g}(\bigotimes_i\rho_i)$ with $\operatorname{relInd}_g((\bigotimes_i A_i)\circ\mathrm{swap}_c)$, so the left-hand side of (2) equals $\Phi_\tau(A)$. Proposition 7.3y expands $\Phi_\tau(A)$ over $t\in T'$, and bijectivity of $\Theta$ reindexes the sum over $s\in T$ (`Finset.sum_preimage`, `:113–114`), replacing $t_i.\mathrm{rep}$ by $P_i(s_i)$ in each row multiplicity (`:116–117`). Inside $\Phi_\tau((P_i(s_i))_{i\in\alpha})$, Lemma 7.3x(2) identifies $(\bigotimes_i\bigotimes_j s_{ij}.\mathrm{rep})\circ\mathrm{swap}_c$ with $\bigotimes_j\bigotimes_i s_{ij}.\mathrm{rep}$, and `normalised_induction_product_parabolic_piTensor` identifies $\operatorname{relInd}_g(\bigotimes_j\bigotimes_i s_{ij}.\mathrm{rep})$ with $\bigotimes_{j\in\beta}\operatorname{multiProd}_{g_j}((s_{ij}.\mathrm{rep})_{i\in\alpha})$ (`:118–122`), proving (2).

*Step 4 (degeneration to $\mathbb N$ and subquotient extraction).* Every $s_{ij}.\mathrm{rep}$ has finite length $1$ (`IrrRep.hasFiniteLength`). Repeatedly filtering one tensor factor along a composition series via Lemma 7.3x(1) and using `piExteriorTensor_smoothIrreducible_isIrreducible` on the irreducible quotients shows that any finite exterior tensor product of smooth finite-length representations of $\mathrm{GL}$ blocks has finite length. Thus each $\bigotimes_{i\in\alpha}s_{ij}.\mathrm{rep}$ has finite length, `(hBZ F).2.2.1` (`InductionFiniteLength`) gives finite length of each column induction $\operatorname{multiProd}_{g_j}((s_{ij}.\mathrm{rep})_i)$, the same tensor-filtration step gives finite length of $\bigotimes_{j\in\beta}\operatorname{multiProd}_{g_j}((s_{ij}.\mathrm{rep})_i)$, and Lemma 7.3w(5) places every multiplicity in $\mathbb N$. Finally, combining Theorem 7.3r (`jhMult_eq`) with (2) and Lemma 7.3w(1) (`jhMult_ne_zero_iff`) extracts a cell $b$ and a tuple $s\in T$ with nonzero row and column factors whenever $m(\tau,r_Q(i_P(\bigotimes_i\rho_i)))\ne 0$, and conversely (`exists_cell_of_isSubquotient`, `ExistsCellOfIsSubquotient.lean:249–270`). $\square$

The named inputs of Lemma 7.3x(3) and Theorem 7.3z, whose statements were read and whose proof bodies were not read here, are the following: the published-layer bundle `BernsteinZelevinskyFiniteness` (`HasFiniteLengthOfIsIrreducible.lean:49–53`, of which `cellSemisimplification` uses `(hBZ k).2.1 : JacquetFiniteLength` directly and passes `hBZ` to two exterior-tensor suppliers, while upstream inhabitation `bernstein_zelevinsky_finiteness` is not read here); the three exterior-tensor classification statements `piExteriorTensor_smoothIrreducible_isIrreducible`, `exists_equiv_piExteriorTensor_blockLevi` and `tensor_product_determines_factor_classes` (`PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement.lean:9`, `ExistsEquivPiExteriorTensorBlockLeviStatement.lean:9`, `TensorProductDeterminesFactorClassesStatement.lean:9`, classically irreducibility, exhaustion and factor-uniqueness of exterior tensor products over product groups); the two factorwise-commutation statements `relative_jacquet_functor_piTensor_equiv` and `normalised_induction_product_parabolic_piTensor` (`RelativeJacquetFunctorPiTensorEquivStatement.lean:9`, `NormalisedInductionProductParabolicPiTensorStatement.lean:9`); the local Iwasawa and compact-open interfaces `UnitInd.exists_iwasawa`, `UnitInd.unip_mul_levi_mem_KO`, `exists_levi_mul_unip`, `UnitInd.isLocallyConstant_modulus`, `SplitFlip.isCompact_KO`, `SplitFlip.isOpen_KO`, `SplitFlip.isEmbedding_val_GL`, `SplitWeil.Model.secondCountable_and_t2_local_field` and `SplitWeil.exists_cball_subset` called by `LeviIntegralFacts.lean` and `ExistsOpenNormalisedSubgroupSubset.lean`; and Mathlib's `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` (`Mathlib/Topology/Algebra/ClopenNhdofOne.lean:48` at pin `0df444a3`). In the corollary combining Theorem 7.3z with Theorem 7.3r, the filtration inputs of §7.4.3.4 are inherited unchanged except that `jhMult_of_le` is now read in full in Lemma 7.3w(3).

**Notes on the proofs and their use.** *Why the archive works in $\mathbb N_\infty$ before passing to Grothendieck groups.* Notice that `CellSemis.cellSemisimplification` never calls `(hBZ k).2.2.1` (`InductionFiniteLength`). Because `jhMult` takes values in $\mathbb N_\infty$, satisfies $0\cdot\infty=0$, and distributes addition over multiplication without finiteness hypotheses, Proposition 7.3y expands $\Phi_\tau(A)$ using finiteness of the row Jacquet modules $A_i$ alone; absent row constituents contribute $0\cdot\Phi_\tau(\dots)=0$ whether or not the column-induced representation has already been shown to have finite length. By contrast, the archive's Grothendieck group `Groth G = IrrCl G →₀ ℤ` (`NontrivialOfIrreducible.lean:185, 239–264`) applies `.toNat` to `jhMult` via `jhMult_ne_top`, so its exactness lemma `cls_exact` requires `HasFiniteLength` on all three terms in advance. Similarly, in Lemma 7.3x(3), `relInd_surjective` projects only the surjectivity half `.1` of `smInd_coinvariants` (leaving the coinvariant-kernel half `.2` and its invariant-functional supplier `DualAverage.exists_invariant_form` unused on this path) and lifts $(P_{\mathrm{col}}\cap J)$-fixed vectors by averaging over the finite orbit $S\subset V_{\sigma_0}$ rather than integrating against a Haar measure on $P_{\mathrm{col}}\cap J$.

*Comparison with the classical proofs.* Bernstein and Zelevinsky define the finite composition multiset $\mathrm{JH}^0(\pi)$ in 1.2 (p. 443) and gluing in 1.11 (p. 445), classify irreducible admissible representations of $G_1\times G_2$ as exterior tensor products in 1.6 (p. 443), prove exactness of induction and Jacquet functors and their commutation with exterior tensor products in Proposition 1.9(a), (g) and Proposition 2.3(a) (pp. 445–446), and deduce admissibility of irreducibles and finite length of cuspidal inductions in Theorems 2.5 and 2.8 (pp. 447–448). [Paper] [Bernstein–Zelevinsky 1977, pp. 443, 445–448](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0/) Zelevinsky's §0 Example (p. 169) states additivity of $\mathrm{JH}^0$ under gluing; Proposition 1.4 (p. 171) shows that $i_{\alpha,\beta}$ and $r_{\beta,\alpha}$ preserve finite length; 1.5 (p. 171) gives the exterior-tensor bijection onto $\mathrm{Irr}\,G_\alpha$ and factorwise commutation of $r$ and $i$; 1.6 (pp. 171–172) deduces that for irreducible $\rho=\rho_1\otimes\dots\otimes\rho_r$ the cell module $F_w(\rho)$ is glued from the column-induced products $\sigma(k_1,\dots,k_r)$ indexed by composition series of each $r_{\beta_i,(n_i)}(\rho_i)$, noting that this computes composition factors for any finite-length $\rho\in\mathrm{Alg}\,G_\beta$; and Proposition 1.7 (pp. 172–173) condenses 1.2 and 1.6 into the graded bialgebra homomorphism $c(\pi_1\times\pi_2)=c(\pi_1)\times c(\pi_2)$ on $R=\bigoplus_{n\ge 0}R(G_n)$ (with length-$2$ cuspidal products classified in Proposition 1.11, p. 175). [Paper] [Zelevinsky 1980, pp. 169, 171–173, 175](https://www.numdam.org/item/ASENS_1980_4_13_2_165_0/) Rather than constructing a multi-index gluing filtration on $F_w(\rho)$ itself, the archive applies `additive_family_expand` directly to the $\mathbb N_\infty$-multiplicity functional $\Phi_\tau$.

*Use in the split theta argument and attribution.* `geometricLemma_of_filtration` (`GeometricLemmaOfFiltration.lean:8–12`) pairs `geometricLemmaFiltration_unconditional` (§7.4.3.4) with `geometricLemma_cell_semisimplification_GL` (`GeometricLemmaCellSemisimplificationGLStatement.lean:7`, forwarding `CellSemis.cellSemisimplification`), and `ThetaLiftGlOfZelevinskyClassification.lean:12` hands the combined `GeometricLemma` package $h_G$ to `Mix.top`. Inside `Mix.cellone` (`MCellone.lean:22–109`), `jacquet_multiplicity_single_cell` expands $m(x_0\boxtimes x_1,r_e(x_0\times x_1))$ over $2\times 2$ size matrices $b$ via `(hG k).1.jhMult_eq` (Theorem 7.3r); on the diagonal matrix $b_0=\operatorname{diag}(d_0,d_1)$, `cell_diag` (`IsSubquotientCompMulSingle.lean:18–107`) proves $\operatorname{cellFunctor}(x_0\boxtimes x_1)\simeq x_0\boxtimes x_1$, giving multiplicity $1$ (`jhMult_self`), while on any $b\ne b_0$ row and column sums force $b_{10}>0$, and `cellone_offdiag` calls `exists_of_cell` (`IsSubquotientCompMulSingle.lean:119–135`, a direct wrapper around `(hG k).2`, Theorem 7.3z) to produce block irreducibles $s_{ij}$ with $s_{10}$ of positive rank occurring in a Jacquet module of $x_1$ and $x_0$ occurring in $s_{00}\times s_{10}$, contradicting the `nolow` callback of `Mix.top`. The companion theorems `offdiag_eq_zero` and `jhMult_jac_multiProd` (`IsSubquotientCompMulSingle.lean:137–218`) apply the same `exists_of_cell` and `cell_diag` pair under disjoint cuspidal supports, and `InducedCellSemisimplification.lean:6–7` instantiates `cellSemisimplification` unconditionally with `bernstein_zelevinsky_finiteness` on the global spectrum branch. The formal proofs are the archive authors' (Alpöge with Claude), with the profinite open-normal-subgroup lemma from Mathlib (Nailin Guan, Yi Song, Xuchun Li, Bryan Wang). The statements, the textbook proofs, the $\mathbb N_\infty$ degeneration analysis, Examples 10 and 11 and the classical comparison are this book's. The read tags are recorded in §7.6.1 under the [cell-constituent supply](#cell-constituent-supply-for-theorem-73z).

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

The [split-place supply for Proposition 7.3f](#split-place-supply-for-proposition-73f) identifies the local representation input separately from the vacuum-span and tensor-matching interfaces.

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

#### Split-place supply for Proposition 7.3f

The archive is A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The paths below are relative to its `lean/` directory.

- **Definitions.** The oscillator formula, pairing and normalized product are in `src/Development/AbelianVarietyTheory/Definitions/Foundations/MatrixMeasurableSpace.lean:40–45`, `src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/IsParahoricVec.lean:14–19` and `src/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean:367–368`. The latter file gives the uniformizer convention at lines 129–143 and the spherical subquotient definition at 529–530. Speh and the product, determinant, twist and Frobenius rules are at `src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/ExistsReadingLaws.lean:83–103`.
- **Actual local path [Lean, read] (R3).** The call at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PairLiftOfHoweDualityBernstein.lean:35–39` uses `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaLiftGeneralLinear.lean:9–10`, then `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/GlThetaLiftIsClosed.lean:8` and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaLiftGlOfZelevinskyClassification.lean:9–13`. The latter applies `Mix.top` for irreducibility and `lift_of_irr` for identification. Their bodies are at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/ImportsAlt.lean:19–56` and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/MingZel.lean:17–44`. The interface takes a general unitary-product hypothesis. The proof term ignores that argument and proves the needed special case from the geometric lemma, Bernstein–Zelevinsky finiteness and Zelevinsky polynomiality.
- **Rank descent and germs [Lean, read] (R3 for the listed bodies).** The ball identity and contraction are assembled in `src/Development/WeilBound/RepresentationTheoryGL/PointAveraging/MinkowskiBalls/ValLeOneOfLc.lean:382–460`, with rank localization in `src/Development/WeilBound/RepresentationTheoryGL/PointAveraging/MinkowskiBalls/MemBallMSelf.lean:134–194`. Germ extraction, uniqueness and propagation occur at `src/Development/WeilBound/RepresentationTheoryGL/PointAveraging/MinkowskiBalls/MeasurableSetBallM.lean:347–405`, `src/Development/WeilBound/RepresentationTheoryGL/PointAveraging/MinkowskiBalls/GermUnique.lean:137–157` and `src/Development/WeilBound/RepresentationTheoryGL/PointAveraging/MinkowskiBalls/RepInvApply.lean:33–75`. The covariance and induced map are at `src/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/GermIntegrals/RealPowerProductEqOne.lean:56–133` and `src/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/GermIntegrals/LFrob.lean:26–78`.
- **Input boundary [Lean].** The textbook statement assumes the irreducibility conclusion of `Mix.top`. That body packages the determinant representation using smoothness and unitarity of the character, uses smooth irreducible unitarisable input on the first block, and applies `nolow` with $r<t$ to rule out the lowest determinant-block exponent in the relevant off-diagonal cell. Its further inputs `geometricLemmaFiltration_unconditional`, `BernsteinZelevinskyFiniteness`, `zelevinskyPolynomialRing_of_parts`, `ss`, `cellone`, `detjac`, `nolow`, Jacquet exactness and support transfer are outside this subsection's read upgrade. The ball basis, normal form, measure covariance and support-localization dependencies retain their prior levels. The spherical classification and exactness of parabolic induction are classical inputs to the textbook parameter calculation.
- **The two matching interfaces.** `HoweUnram` at `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/HoweUnram.lean:8–19` asks for fixed vectors on each side to lie in the opposite orbit span of a nonzero cyclic vacuum in a `LocPair`. Its producer is `howeUnram_holds` at `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/RhoMemOfMkEq.lean:250–256`, using `fixed_mem_span` and the hermitian-adjoint swap. Its deeper proof retains its prior reading level. `LocalMatching` in `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:581–583` concerns matched data for an `IsTriple`. The split representation identification above uses `ThetaPair`. The distinct split label consumer at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LocalComponentMatchesOfHoweDuality.lean:65–94` also calls the split-GL theorem, then applies the product, determinant and inverse-twist rules.
- **Spherical calculation [Expository].** The lattice double-coset proof evaluates the spherical Hecke character in textbook normalization. The archive consumer reads its local parameters through `RecLawsH`.

#### Single-cell supply for Proposition 7.3g

All paths start at the root of A2, SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. [Archive provenance](../sources/SOURCES.md#1-the-lean-archive-primary-source)

| Archive path and lines | Declaration or role | Reading |
|---|---|---|
| lean/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaLiftGlOfZelevinskyClassification.lean:9–13 | Actual construction of the geometry argument to Mix.top | [Lean, read] caller |
| lean/src/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/ImportsAlt.lean:19–56 | Same geometry passed to cellone and nolow | [Lean] context |
| lean/src/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/MCellone.lean:22–32, 59–90 | Both fields of the geometry package | [Lean] context |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GeometricLemmaOfFiltration.lean:8–12 | Pairs filtration and cell multiplicity | [Lean, read] wrapper |
| lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetOfInducedFiltration.lean:98–107 | Composition with the two transports | [Lean, read] assembly, R3 in §7.4.3.4 |
| lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviIntersectionConjugate.lean:20–97, 123–212 | Induction and coinvariant transport, cell_equiv and cell_iso | [Lean, read] R3 for the direct bodies, using the named subgroup, continuity and modulus interfaces |
| lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CellLeviTensorDecomposition.lean:44–119, 226–302 | Quotient conjugation and induced conjugation | [Lean, read] R3 for cellFunctor_congr, jacJ_relJac and relInd_congr |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean:73–85, 137–232, 370–385, 455–535 | Volume ratio, compact-modulo-A support, stabilized evaluation and covariance | [Lean] R2 for full supplier |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaNormal.lean:57–98, 128–145, 278–351 | Normalization character and normalized inducing action | [Lean] normalization reference |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemma.lean:31–79 | Twist on sections and coefficient change | [Lean] normalization reference |
| lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BernsteinZelevinskyGeometricLemma.lean:63–83 | Graded kernel and surjectivity, then normalization | [Lean, read] assembly, R3 in §7.4.3.4 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:81–164, 241–489, 586 | bumpFun, exists_bump_permGL, exists_cellJacquet_bump, cellJacquetMap_surjective | [Lean, read] R3 in §7.4.3.3; see the bump and kernel supply below |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean:49, 192 | exists_avgOver_cellFun_eq_zero, exists_sub_mem_ker_of_cellJacquet_eq_zero | [Lean, read] R3 in §7.4.3.3; see the bump and kernel supply below |
| lean/src/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/NotInSupportOfSubsingleton.lean:17–84 | Model.evalOne and Model.evalOne_bijective | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsEmbeddingParIndOfJacquetNontrivial.lean:13–62 | Unit evaluation turns a Jacquet quotient into an embedding | [Lean, read] R3, taking Jacquet finite length as input |
| lean/src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsEmbeddingParIndOfJacquetNontrivialStatement.lean:14–15 | Alias consumed by L_jacq | [Lean, read] wrapper |
| lean/src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsCuspidalSupportIrreducibleSmoothGL.lean:22–24 | L_jacq and L_tens | [Lean] context |
| lean/src/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/MFront.lean:67–71 | Mix.front calls CuspEmbed.main with hG | [Lean] context |
| lean/src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LanglandsClassificationCuspidalSupport.lean:102–119, 141–164 | Noncuspidal branch uses L_jacq and L_tens | [Lean] context |
| lean/src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsCellOfIsSubquotient.lean:344–357 | Determinant embedding illustrates unit evaluation | [Lean] application |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GeometricLemmaCellSemisimplificationGL.lean:59–122 | CellSemis.cellSemisimplification, column induction exactness and finite-length multiplicity | [Lean, read] R3 in §7.4.3.6; see the cell-constituent supply below |

The auxiliary transport premises include block_count_reindex_equivs, levi_refinement_block_order, levi_refinement_parabolic, levi_equiv_continuous, levi_double_coset_intersection and refined_block_order_compat. The read tags cover the cited bodies with these premises as interfaces. Proposition 7.3g proves the isomorphism on the cell and takes the ambient relative support identification as a hypothesis.

#### Bump and kernel supply for Theorems 7.3l and 7.3n

All paths start at the root of A2, SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. File hashes: GeometricLemmaCellSurjective.lean 4ab724f7619b12ee8560bddbd1ded8720b687894827518ac1a208ae73747eaac, GeometricLemmaCellKernel.lean d0b7d3c552fa3501e3ad0b5e8643f3995bfab3c6a2ba3d631b2cb19fcefa231d, GeometricLemmaJacquetCell.lean d81c00dd165210d9065719d3b4bbfa2aa11d3db89b2bff4609b1364cbaec7cef.

| Archive path and lines | Declaration or role | Textbook item | Reading |
|---|---|---|---|
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:81–83, 87–157 | bumpFun, bumpFun_apply, bumpFun_eq_zero, bumpFun_mem | Definition of the covariant bump and Lemma 7.3h | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:199–225 | exists_level_near_permGL | Lemma 7.3i, using the orbit-map openness statement as interface | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:20–53 | exists_nonneg_avgOver | Lemma 7.3j | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:241–289 | exists_bump_permGL | Description of the bump on $wQ$ in the proof of Lemma 7.3k | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:306–474 | exists_cellJacquet_bump | Lemma 7.3k | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:490–551 | cellJacquetMap_parabolicInd, indRep_mem_range_cellJacquetMap, exists_bump_mem_range | Translated bumps | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:560–576 | eq_on_cellDoubleCoset | Agreement rule on $Ds(L\cap K_J)$ | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:586–815 | cellJacquetMap_surjective | Theorem 7.3l, including the finite subtraction (the inner induction at lines 687–804) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean:38–43, 49–138 | coinvariantsKer_mono, exists_avgOver_cellFun_eq_zero | Lemma 7.3m | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean:146–190 | avgOver_mul_right_of_normalizes, avgFinite_comp_mul_left, avgOver_permGL_mul_mul | Substitution $k\mapsto t^{-1}kt$ in the proof of Theorem 7.3n | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean:192–349 | exists_sub_mem_ker_of_cellJacquet_eq_zero | Theorem 7.3n, with the explicit difference formula at lines 328–349 | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean:21–23, 73–75, 106–107, 137–140, 167–170, 223–241, 316–329, 529–532 | IsCellCompact, cellNorm, cellFun, CellSupp, cellEv, cellJacquet, cellJacquet_eq_cellEv, cellJacquet_eq_zero, cellJacquetMap | Definitions and the converse in Theorem 7.3n | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean:148–157 | exists_cellSupp | Existence of a support level | [Lean, read] R3 in §7.4.3.5 (Theorem 7.3v), with its ambient supply exists_unipotentCompactG_support at GeometricLemmaCompact.lean:224–309 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean:39, 60–61, 246–250, 261 | rightStab, avgOver, avgOver_eq_sum_translates, sub_avgOver_mem_span | Finite averages and the difference formula | [Lean, read] definitions and the two cited statements |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean:84–88, 172–177, 205–208 | avgOver_eq_smul_avgOver_inf, relIndex_smul_avgOver_eq, avgOver_eq_zero_of_le | Two-level comparison of averages in Lemma 7.3m and Theorem 7.3n | [Lean] statements read; bodies named |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean:57–58, 81–83 | unipotentCompactG, unipotentCompactG_eq | The levels $N_e$ | [Lean, read] definition |
| lean/src/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean:33–34 | rankTorus | The block-scalar torus elements $t_e$ | [Lean, read] definition |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean:60–64, 90–91, 164–165, 300–303 | cellUnipotent, cellLeviParabolic, cellRepA, exists_congruence_fixed, exists_finset_levi_eq_mul | $A$, $D$, $\theta$, smooth fixed levels, the finite set $T$ | [Lean] definitions read; the two existence statements named |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean:75–80 | exists_nhds_inter_doubleCoset_subset | Orbit-map openness used in Lemma 7.3i | [Lean, read] R3 in §7.4.3.5; isOpenMap_doubleCoset reduces it to Mathlib's isOpenMap_smul_of_sigmaCompact, which is named |
| lean/src/GroundTheory/AutomorphicForms/InductionJacquet.lean:27–31 | exists_mem_coinvariantsKer | Finitely many relations in Lemma 7.3m | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/SmoothRep.lean:331, 342, 353 | fixedProj, fixedProj_apply_of_mem_coinvariantsKer, fixedProj_eq_iff | Unique fixed projection in Lemma 7.3m | [Lean] statements named |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean:189–195 | supportedIn | $\mathcal I_Y$ | [Lean, read] definition |
| lean/src/GroundTheory/AutomorphicForms/InductionParabolic.lean:81–82, 99–104 | inflateTwist, mem_parabolicIndSpace | Sections and $\tau$ | [Lean, read] definition |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean:175, 240–246, 265 | gradedJacquetMap, gradedJacquetMap_eq_zero_iff, gradedJacquetMap_surjective | Graded consumer interface | [Lean, read] R3 in §7.4.3.4 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaUnnormalized.lean:82–84 | Consumption of both supplies | Assembly | [Lean, read] R3 in §7.4.3.4 |
| lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BernsteinZelevinskyGeometricLemma.lean:67–69 | Consumption of both supplies | Assembly | [Lean, read] R3 in §7.4.3.4 |

The frame hypotheses hYo, hCY, hYP and hYQ of the declarations are the four conditions on $Y$ in the definitions of §7.4.3.3. Theorem 7.3l uses all four; Theorem 7.3n uses hYo, hCY and hYQ. Smoothness of $\sigma$ enters Theorem 7.3l through exists_congruence_fixed and Lemma 7.3m through isSmooth_cellRepA. The reading is of the proof bodies against the named interfaces; it is not a kernel check, and no Lean was compiled for this subsection.

#### Filtration supply for Theorems 7.3o–7.3r

All paths start at the root of A2, SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. [Archive provenance](../sources/SOURCES.md#1-the-lean-archive-primary-source) File hashes: GeometricLemmaCells.lean ba853ff3a312edc142e82a0c78a4cb9b656067dcfd515b86a12e0b7e48117b1e, GeometricLemmaFiltration.lean 4bad875c57ee45fad3e72e893119c7f287102018ac2deaa58246fd019f835dc6, GeometricLemmaGraded.lean df9a16e4b81679afaf56539824b6a2a1fb75afd6128c535bbed3f8cd77aa99fb, BernsteinZelevinskyGeometricLemma.lean 12244c79a749899a52ae1525c5b279ff4a00b51d64955661ecdbba43e8ce6a55, JacquetOfInducedFiltration.lean 7800f6b0ef5dab1e2a0a70eb13446167073175ba0b883117dbb23f2c02a4beda.

| Archive path and lines | Declaration or role | Textbook item | Reading |
|---|---|---|---|
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean:18–75 | exists_mul_mul_eq_one_of_rank, isOpen_setOf_le_rank | Openness of rank conditions in Theorem 7.3o(3) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean:85–155 | cellRank, submatrix_mul_of_mem_blockUpper, mul_submatrix_of_mem_blockUpper, isUnit_det_submatrix_of_mem_blockUpper, cellRank_mul_mul, cellRank_of_mem_doubleCoset | Rank array and Theorem 7.3o(1) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean:163–302 | cellRank_permGL, permGL_mem_blockUpper, permGL_mem_doubleCoset_of_card | Theorem 7.3o(2): counts and fibre matching | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean:304–355 | conj_permGL_mem_blockUpper_iff, exists_permGL_mem_doubleCoset, mem_doubleCoset_of_cellRank_eq | Theorem 7.3o(2): reduction to the Borel case; rank arrays determine cells | [Lean, read] R3, with the Borel case named |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean:363–449 | cellHeight, cellRank_eq_zero_of_lt, cellRank_eq_of_le, cellRank_clip, cellRank_eq_of_le_of_cellHeight_le, isOpen_setOf_le_cellRank, closure_doubleCoset_subset, cellHeight_of_mem_doubleCoset | Height and Theorem 7.3o(3) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean:18–105 | cellUnion, cellUnion_zero, cellUnion_mono, cellUnion_succ, cellUnion_of_cover, isOpen_cellUnion, closure_inter_cellUnion_succ, disjoint_cellUnion | Theorem 7.3o(4) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean:113–179 | exists_cellEnumeration, closure_doubleCoset_subset_of_antitone | Height enumeration; Theorem 7.3o(4) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean:189–253 | supportedIn, supportedIn_le_comap, jacquetFiltration, jacquetFiltration_mono, jacquetFiltration_empty, jacquetFiltration_univ, jacquetFiltration_le_comap | $\mathcal I_Y$, the image filtration $V_j$ and its stability | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean:19–139 | avgOver_mem_supportedIn, cellJacquet_avgOver, cellJacquet_eq_zero_of_mk_eq_zero | Lemma 7.3p, the exactness step | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean:143–194 | jacquetSupported, jacquetSupported_surjective, ker_jacquetSupported_le, cellJacquetMap_eq_of_jacquetSupported_eq, gradedJacquetMap, gradedJacquetMap_apply | Theorem 7.3q(1) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean:206–269 | gradedJacquetMap_jacquetRep, gradedJacquetMap_eq_zero_of_mem, gradedJacquetMap_eq_zero_iff, gradedJacquetMap_surjective | Theorem 7.3q(1)–(2) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaUnnormalized.lean:21–86 | cellUnion_mul_mem, exists_filtration_jacquetModule_parabolicInd | Unnormalized assembly, parallel to the main path | [Lean, read] R3 |
| lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BernsteinZelevinskyGeometricLemma.lean:24–104 | filtration_of_cellEnumeration, normalized_piece, geometricLemma_uniform | Theorem 7.3r, Steps 1–3 | [Lean, read] R3 |
| lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BernsteinZelevinskyGeometricLemmaStatement.lean:12–13 | bernstein_zelevinsky_geometric_lemma | Forwarding to geometricLemma_uniform | [Lean, read] wrapper |
| lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetOfInducedFiltration.lean:30–107 | equivComp, jacquetOfInducedFiltration | Theorem 7.3r, Step 4 | [Lean, read] R3 for the assembly; the coordinate transports it calls are named |
| lean/src/CompanionTheory/AutomorphicTheory/TemperedLocalSpectra/LocalGeometry/Imports.lean:5–6 | CompanionTheory.Geo.geometricLemmaFiltration | Forwarding | [Lean, read] wrapper |
| lean/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeometricLemmaFiltrationUnconditional.lean:7–8 | geometricLemmaFiltration_unconditional | Forwarding | [Lean, read] wrapper |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GeometricLemmaOfFiltration.lean:8–12 | geometricLemma_of_filtration | Pairing with the cell semisimplification | [Lean, read] wrapper |
| lean/src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsCellOfIsSubquotient.lean:83–100, 149–178, 205–207 | cellFunctor, SizeMatrix, JacquetOfInducedFiltration, CellSemisimplification, GeometricLemma | Statement of Theorem 7.3r | [Lean, read] definitions |
| lean/src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsCellOfIsSubquotient.lean:236–277 | jhMult_eq, exists_cell_of_isSubquotient | Theorem 7.3r, Step 5, and its extraction | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NontrivialOfIrreducible.lean:109–150 | jhMult_of_le, jhMult_filtration | Additivity of extended multiplicities in $\mathbb N_\infty$ | [Lean, read] R3 (jhMult_of_le via jhMult_exact in §7.4.3.6) |
| lean/src/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/MCellone.lean:22–109 | cellone_offdiag, jacquet_multiplicity_single_cell, Mix.cellone | Use of jhMult_eq and cellSemisimplification in Mix.cellone | [Lean, read] R3 in §7.4.3.6 |
| lean/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaLiftGlOfZelevinskyClassification.lean:9–13 | thetaLift_gl_of_zelevinsky_classification | Passes the package to Mix.top | [Lean, read] caller |
| lean/src/GroundTheory/AutomorphicForms/InductionJacquet.lean:27–41 | exists_mem_coinvariantsKer | Lemma 7.3p(3) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/InductionJacquet.lean:46–73 | exact_coinvariantsMap | General exactness, not called by the filtration | [Lean, read]; not on this path |
| lean/src/GroundTheory/AutomorphicForms/InductionParabolic.lean:49–52, 143–148, 200–208 | invSqrtModular, jacquetRep, jacquetRep_mk, exact_jacquetMap | Normalized action of $L$; general exactness, not called | [Lean] definitions and statements read |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean:137–157, 243–249, 289–298, 316–329 | CellSupp, exists_cellSupp, exists_cellSupp_pair, cellJacquet_parabolicInd, cellJacquet_eq_zero | Support levels and equivariance in Lemma 7.3p and Theorem 7.3q | [Lean, read]; ambient supplier read in §7.4.3.5 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean:217–221 | exists_unipotentCompactG_of_isCompact | A compact subgroup of $N$ lies in a level | [Lean, read]; entryBound_of_isCompact read in §7.4.3.5 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean:224–309 | exists_unipotentCompactG_support | Ambient support supply | [Lean, read] R3 in §7.4.3.5 |
| lean/src/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean:33–34, 152–154 | rankTorus, exists_compactOpen_unipotentRadical | Levels $t_e$; compact open exhaustion of $N$ | [Lean, read] definition; exists_compactOpen_unipotentRadical R3 in §7.4.3.5 |
| lean/src/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean:210 | blockRank | Cumulative block ranks | [Lean, read] definition |
| lean/src/GroundTheory/AutomorphicForms/FiniteBruhat.lean:262–263 | exists_mem_doubleCoset_permGL | Bruhat decomposition for the Borel subgroup | [Lean] statement read; body named |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemma.lean:46–79 | indTwistHom, indCongrHom, indTwistHom_surjective, indCongrHom_injective, indCongrHom_surjective | Normalization in Step 3 | [Lean] statements read |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean:60–61, 184, 253, 286, 353 | avgOver, avgOver_comp_mul_right, avgOver_mem, avgOver_avgOver, avgFinite_of_isOpen | Averaging identities | [Lean] statements read |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean:17, 223 | avgOver_eq_zero_of_forall, avgOver_map_mulEquiv | Averaging identities | [Lean] statements read |

The coordinate transports called by `jacquetOfInducedFiltration` are exists_strict_block_order, levi_block_homeomorph, induction_reindex_equiv, jac_equiv_jacquetRep_comp_levi_equiv, parabolicInd_equiv_levi_transport, jacquet_module_equiv, filtration_transport_equiv, double_coset_block_matrix, permutation_block_counts, exists_perm_block_matrix and isSmooth_comp_continuous; levi_intersection_conjugate and cell_levi_tensor_decomposition are `cell_iso` and `cellFunctor_congr`, read for their direct bodies in §7.4.3.2. The reading checks proof bodies against the named interfaces. It is not a kernel check, and no Lean was compiled for this subsection.

#### Level and support supply for Theorem 7.3v

All paths start at the root of A2, SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. [Archive provenance](../sources/SOURCES.md#1-the-lean-archive-primary-source) File hashes: GeometricLemmaCompact.lean 037179b586350e838591aa64ef4c781f01ec9345c3d94eed4fec4f4491b7c754, GeometricLemmaCellGroups.lean bc9e6813f0b22053587c60c5f83e6d7508002b6788dafd710f71db21485b2a68, InductionParabolicLocal.lean 214bad1b169daebaa35dd8a051acb6f8fe6f1efada7fb44d867af7510282cb0d, GLnLattice.lean 7327514e6626b5a00981769249be1fd2307901c333eb21ee5b16b10e95061441, GeometricLemmaOrbit.lean ab6a0f5ca775ad6bf192bc5ffec53bcd29914300568a5a75cba358e9128d7d07, GeometricLemmaJacquetCell.lean d81c00dd165210d9065719d3b4bbfa2aa11d3db89b2bff4609b1364cbaec7cef, AdmissibleInduction.lean 5fae832b931fa818e48464fd00329ff4324f4ca4e4db50eeb596b745fda145f3.

| Archive path and lines | Declaration or role | Textbook item | Reading |
|---|---|---|---|
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean:22–49 | EntryBound, EntryBound.mul, entryBound_of_isCompact, EntryBound.leviProj | Lemma 7.3s | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GLnLattice.lean:338–376 | eventually_pow_mul_mem, exists_pow_mul_mem_of_isCompact | Lemma 7.3s(2): increasing open cover of a compact set | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean:33–34, 53–60, 71–165 | rankTorus, rankTorus_conj_apply, isClosed_unipotentRadical, rankTorus_conj_apply_mem, unipotentCompact, mem_unipotentCompact, isOpen_unipotentCompact, isCompact_unipotentCompact, mem_unipotentCompact_of_bound, exists_compactOpen_unipotentRadical | Lemma 7.3t(1)–(3) and (5) for finite sets | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean:57–145 | unipotentCompactG, unipotentCompactG_le, mem_unipotentCompactG, isCompact_unipotentCompactG, unipotentCompactG_eq, isOpen_conj_integralGL, mem_unipotentCompactG_of_bound, unipotentCompactG_mono | Lemma 7.3t(1)–(3) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean:217–260 | exists_unipotentCompactG_of_isCompact, conj_mem_unipotentCompactG, exists_compactOpen_subgroupOf, isClosed_cellUnipotent | Lemma 7.3t(4)–(5) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/InductionParabolic.lean:263–269 | rankTorus_commute | Lemma 7.3t(4) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean:21–65 | IsCellCompact, isCellCompact_unipotentCompactG, IsCellCompact.exists_le, IsCellCompact.map_conj | Lemma 7.3t(5) for conjugated compact open subgroups | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean:154–222 | isClopen_support_parabolicInd, exists_isCompact_support_doubleCoset | Proposition 7.3u, Steps 1, 2 and 5 | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean:75–131 | exists_nhds_inter_doubleCoset_subset, exists_isCompact_subset_doubleCoset | Proposition 7.3u, Steps 3 and 4 | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean:40–73 | isOpenMap_doubleCoset | Openness of the orbit map onto a locally closed double coset | [Lean, read] reduction to Mathlib's isOpenMap_smul_of_sigmaCompact, which is named |
| lean/src/GroundTheory/AutomorphicForms/AdmissibleInduction.lean:67–75 | exists_blockUpper_mul_integralGL' | Iwasawa decomposition in Step 5 | [Lean, read] reduction to the sorted case exists_blockUpper_mul_integralGL, which is named |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean:224–309 | exists_unipotentCompactG_support | Theorem 7.3v(1)–(2): the factorization and the level of four summed bounds | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean:137–157, 243–249 | CellSupp, CellSupp.mono, exists_cellSupp, exists_cellSupp_pair | Theorem 7.3v(2) and (4) | [Lean, read] R3 |
| lean/src/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean:99–118, 165–182, 210–220 | leviProj, leviProj_apply, leviProj_of_mem_levi, mem_unipotentRadical_iff_leviProj, conj_mem_unipotentRadical, blockRank, blockRank_lt, blockRank_eq | Levi projection and cumulative ranks | [Lean] definitions and statements read |
| lean/src/GroundTheory/AutomorphicForms/GLnLocal.lean:38–62, 144–168 | integralGL, mem_integralGL_iff, isOpen_integralGL, isCompact_integralGL | $K_0$ is a compact open subgroup | [Lean] definitions and statements read |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean:177–218, 251–285, 316–329, 455–510 | cellEv_eq_of_le, exists_cellEv_eventually, cellJacquet_add, cellJacquet_smul, cellJacquet_eq_zero, cellJacquet_mul_left | Consumers: the cell map, linearity, the converse in Theorem 7.3n, covariance under $D$ | [Lean, read] call sites of the level supplies |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean:34–76, 90–139 | cellJacquet_avgOver, cellJacquet_eq_zero_of_mk_eq_zero | Consumers: Lemma 7.3p(2)–(3) | [Lean, read] R3 from §7.4.3.4; call sites at lines 43, 48, 96 and 136 re-read |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean:49–138, 192–349 | exists_avgOver_cellFun_eq_zero, exists_sub_mem_ker_of_cellJacquet_eq_zero | Consumers: Lemma 7.3m and Theorem 7.3n | [Lean, read] R3 from §7.4.3.3; call sites at lines 61, 75, 78, 223 and 226 re-read |
| lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean:396, 447 | calls of exists_cellSupp | Consumer: Lemma 7.3k | [Lean, read] R3 from §7.4.3.3; call sites re-read |

The named inputs of this supply are Mathlib's open mapping theorem `isOpenMap_smul_of_sigmaCompact` (Mathlib.Topology.Algebra.Group.OpenMapping) and the sorted Iwasawa decomposition `exists_blockUpper_mul_integralGL`, together with the Mathlib compactness lemmas used by the finite and directed subcovers. Every file hash above agrees with the copy of the same path extracted from the archive. The reading checks proof bodies against the named interfaces. It is not a kernel check, and no Lean was compiled for this subsection.

#### Cell-constituent supply for Theorem 7.3z

All paths start at the root of A2, SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. [Archive provenance](../sources/SOURCES.md#1-the-lean-archive-primary-source) File hashes: GeometricLemmaCellSemisimplificationGL.lean 1d259a287da5057bcf83ab1dadbfe135eea5a20ed98677cac78b59b93825544d, AdditiveFamilyFunctionDeterminedConstituents.lean 75179f812d499a728616fd917d22617ab9548bf4f094e93b32469b81a4db9034, JordanHolderMultNormalisedInductionExact.lean cb71f6730472bc8af0b5d4c3a287364062a09711cc203082ef4e45ab1599e1b3, PiTensorSmoothRepsExactEachFactor.lean d6bb59fd6afddeea397bdea050b63d0700eedb3470892028b7a692df1316325b, PiTensorDoublyIndexedSwapBlocksEquiv.lean d335e8e7513f0a0bea455b1a8256f4547d8a8f4c6c3584f1e46dfb600ff972dd, JhMultSubAddQuot.lean 799d099bf917df17361b01ca3a71da9e79062418f6b1aaa19ba045b7d97f1093, SmIndCoinvariants.lean 24d4ecbb46c635a21c7a76f65530373b732f88d0b7932771a16712e0a1b42205, InductionContragredient.lean 11adff6acc2ab0ba31346321a86db86b298425006ba13aa52feb7cd5c6d35b73, IwahoriProjSurjective.lean d62c028e1813c19e5cc6fb8aec3a7c8a7fac063c11ab3f5d657afb1718eeaf40, ExistsOpenNormalisedSubgroupSubset.lean 87a94613917b1cefb500876b8dde9614d76ed42602486950c890802996f78fc5, LeviIntegralFacts.lean 5b02c6c81cd937f5187e42af1ab7472d6469d58c14b8a41e85dd74f7ef2625ae, PiExteriorTensorFlattenedIndexEquivNested.lean 2c1af0957bcf954794f0d78fe7fc9c4479a23d019ea2b95ff870399205e5eedb.

| Archive path and lines | Declaration or role | Textbook item | Reading |
|---|---|---|---|
| lean/src/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean:60–119, 120–150, 173–241, 267–302 | IsSubquotient, HasFiniteLength, subQuot, OccursTimes, jhMult, piTensor, IsSmoothChar, isSmooth_twist, IsSubquotient.isSmooth, isSmooth_piTensor, smIndMap | Definitions of extended multiplicity in $\mathbb N_\infty$, finite length, smooth exterior tensor and induced intertwiners | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmRep.lean:10–33 | SmRep, SmRep.ofIrr | Smooth representation bundle | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean:13–86, 93–226, 229–296 | exists_factor, subMap, subComap, Step, step_iff, occurs_of_finset, occurs_zero, step_dichotomy, step_map, step_comap, occurs_add, jhMult_exact, jhMult_sub_add_quot, Step.not_le, jhMult_ne_top, jhMult_ne_zero_iff | Lemma 7.3w(1), (2), (5): step dichotomy, concatenation, exact additivity in $\mathbb N_\infty$, finiteness bound | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NontrivialOfIrreducible.lean:17–156, 163–286 | jhMult_congr_left, jhMult_congr_right, nontrivial_of_irreducible, IsSubquotient.nonempty_equiv, jhMult_self, isIrreducible_subQuot, jhMult_of_le, topEquiv, jhMult_of_subsingleton, jhMult_filtration, IrrRep, IrrCl, finite_constituents, cls, cls_apply_cl, cls_exact, IrrRep.hasFiniteLength | Lemma 7.3w(1), (3), (5), (6) and Grothendieck-group comparison; upgrades jhMult_of_le from §7.4.3.4 | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfIsIrreducible.lean:19–93 | IrreducibleAdmissible, JacquetFiniteLength, InductionFiniteLength, InductionContragredient, BernsteinZelevinskyFiniteness, hasFiniteLength_iff_wellFounded, hasFiniteLength_of_isIrreducible | Finiteness bundle statement and well-foundedness equivalence | [Lean, read] definitions and transport lemmas |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PiTensorSmoothRepsExactEachFactor.lean:12–114 | piTensorHom, piTensorMap_add_eq_id, piTensor_exact_position | Lemma 7.3x(1): linear splitting on one factor and multilinear update identity | [Lean, read] R3; wrapper at PiTensorSmoothRepsExactEachFactorStatement.lean:9 |
| lean/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PiExteriorTensorFlattenedIndexEquivNested.lean:17–76 | tprod_tprod_update_sigma, curryML, sigBasis, nestBasis, sigmaCurry, sigmaCurry_eq_lift, sigmaCurry_tprod | Flattened-to-nested tensor equivalence in Lemma 7.3x(2) | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PiTensorDoublyIndexedSwapBlocksEquiv.lean:16–87 | sigmaPairSwap, exists_pairCurry, exists_pairSwap, exists_pairCurrySwap, piTensor_swapBlocks_equiv | Lemma 7.3x(2): doubly indexed block swap | [Lean, read] R3; wrapper at PiTensorDoublyIndexedSwapBlocksEquivStatement.lean:9 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JordanHolderMultNormalisedInductionExact.lean:21–108 | smIndMap_injective, exists_smIndMap_eq, exists_normalised_pi, isSmoothChar_relDeltaHalf, relInd_surjective, jhMult_relInd_exact | Lemma 7.3x(3): pointwise kernel exactness and surjectivity of column induction | [Lean, read] R3; wrapper at JordanHolderMultNormalisedInductionExactStatement.lean:9 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmIndCoinvariants.lean:14–40, 65–80 | smIndMap_bump, mem_of_bump, map_mem_fixed, smInd_coinvariants (first conjunct `.1`) | Lemma 7.3x(3): reduction of surjectivity to bumps on $P_{\mathrm{col}}J$ (second conjunct `.2` unused on this path) | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean:20–169 | cell, isOpen_cell, cell_cases, extFun, extInd, bump, bump_mul, bump_zero, mem_span_bump | Lemma 7.3x(3): finite decomposition into right $K_L$-translated bumps over $K_L/H_K$ | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean:16–50 | exists_fixed_map_eq | Lemma 7.3x(3): equal-weight average over the finite $(P_{\mathrm{col}}\cap J)$-orbit | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsOpenNormalisedSubgroupSubset.lean:12–45 | exists_open_normalised_subgroup_subset | Lemma 7.3x(3): open subgroups of $\mathrm{GL}_n(\mathcal O)$ normalized by $\mathrm{GL}_n(\mathcal O)$ | [Lean, read] reduction to Mathlib's ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one, which is named |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeviIntegralFacts.lean:17–118 | nabs_det_eq_one, levi_integral_facts | Lemma 7.3x(3): closedness of parabolics, continuity of Levi projection, forwarding of Iwasawa decomposition | [Lean, read] R3 for the assembly; UnitInd.exists_iwasawa and local compact-open interfaces named |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AdditiveFamilyFunctionDeterminedConstituents.lean:19–177 | jhMult_rep_rep, sub, quo, congr_equiv, one_coord₂, additive_family_expand | Proposition 7.3y: well-founded single-coordinate and active-set inductions | [Lean, read] R3; wrapper at AdditiveFamilyFunctionDeterminedConstituentsStatement.lean:9 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GeometricLemmaCellSemisimplificationGL.lean:25–122 | relIndEquiv, jhMult_relInd_of_subsingleton, subsingleton_piTensor, CellSemis.cellSemisimplification | Theorem 7.3z(1)–(2): full cell constituent multiplicity proof | [Lean, read] R3; wrapper at GeometricLemmaCellSemisimplificationGLStatement.lean:7 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement.lean:9 | piExteriorTensor_smoothIrreducible_isIrreducible | Exterior tensor of smooth irreducibles is irreducible | [Lean] statement read; body named |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEquivPiExteriorTensorBlockLeviStatement.lean:9 | exists_equiv_piExteriorTensor_blockLevi | Exhaustion of block-Levi irreducibles by exterior tensors | [Lean] statement read; body named |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TensorProductDeterminesFactorClassesStatement.lean:9 | tensor_product_determines_factor_classes | Exterior tensor product determines factor classes | [Lean] statement read; body named |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelativeJacquetFunctorPiTensorEquivStatement.lean:9 | relative_jacquet_functor_piTensor_equiv | Factorwise commutation of $\operatorname{relJac}_f$ with exterior tensor | [Lean] statement read; body named |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalisedInductionProductParabolicPiTensorStatement.lean:9 | normalised_induction_product_parabolic_piTensor | Factorwise commutation of $\operatorname{relInd}_g$ with exterior tensor | [Lean] statement read; body named |
| lean/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NonemptyEquivOfRangeEq.lean:27–49 | equivOfBijective, compEquiv, piTensorEquiv | Equivariant isomorphism helpers called in Step 3 | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean:257–275, 321–324, 367–392 | jac, isSmooth_jac, multiProd, prod₂, jac₂_detRep | Normalized Jacquet, column product and determinant Jacquet formulas (Examples 10–11) | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsCellOfIsSubquotient.lean:23–101, 144–179, 236–271, 321–357 | relParab, relUnip, relProj, relDeltaHalf, swapBlocks, relJac, relInd, cellFunctor, GrothGL.unit, CellSemisimplification, jhMult_eq, exists_cell_of_isSubquotient, nonempty_jac_det_equiv | Definitions, Theorem 7.3z(3) subquotient extraction and $\mathrm{GL}_0$/determinant checks | [Lean, read] R3 |
| lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GeometricLemmaOfFiltration.lean:8–12 | geometricLemma_of_filtration | Pairs filtration with cellSemisimplification | [Lean, read] wrapper |
| lean/src/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/MCellone.lean:22–109 | cellone_offdiag, jacquet_multiplicity_single_cell, Mix.cellone | Consumer: off-diagonal cell elimination and diagonal multiplicity $1$ | [Lean, read] R3, with parInd_jac_placing and prodIrrEquiv as interfaces |
| lean/src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsSubquotientCompMulSingle.lean:18–218 | cell_diag, isSubquotient_comp_mulSingle, exists_of_cell, offdiag_eq_zero, jhMult_jac_multiProd | Consumer: diagonal cell isomorphism and disjoint-support off-diagonal vanishing | [Lean, read] R3, with cuspidal-support uniqueness interfaces named |
| lean/src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/InducedCellSemisimplification.lean:6–7 | Glob.cellSemisimplification | Instantiation with bernstein_zelevinsky_finiteness | [Lean, read] wrapper |

Every file hash above agrees with the copy of the same path extracted from `lean.tar.gz`. The reading checks proof bodies against the named interfaces. It is not a kernel check, and no Lean was compiled for this subsection.

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
