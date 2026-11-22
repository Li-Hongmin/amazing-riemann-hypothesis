# Chapter 14. Masullo's trace-formula route

> **Status tags used in this chapter:** `[Paper; Masullo p. …]` for definitions, statements,
> equations, and author footnotes read directly in Alessandro Maria Masullo's 940-page draft
> *The Music of the Primes* (`sha256 e039d3f6…97bf5`); `[Paper; remark p. …]` for Alpöge's four-page
> note; `[Lean, read]` for cross-references to declarations in Alpöge's archive verified in earlier
> chapters; `[Community]` for public community audits, Zenodo notes, and formalization repositories
> (`mccorvie/riemann-masullo`, Prove2Me, Lean Zulip); `[Expository]` for classical harmonic-analytic
> background, hand-worked examples, and our own functional-analytic derivations; `[Open]` for
> unresolved analytic gaps, unreviewed repair proposals, and unwritten sections.

In Chapters 1 through 13 we followed a single machine-checked spine: Levent Alpöge and Claude's
175,187-file Lean 4 archive proving the Riemann Hypothesis and the Generalized Riemann Hypothesis for
all Dirichlet $L$-functions over $\mathbb Q$ by transporting Stepanov's auxiliary-vanishing method
to chains of $m \asymp \sqrt{x}$ definite unitary theta lifts. Roughly five hours after that archive
went online on 20 November 2026, a second, completely independent manuscript appeared on Ravi Vakil's
blog: **Alessandro Maria Masullo's 940-page human-written draft *The Music of the Primes*** [Paper;
Masullo p. 1] `[Community]`.

Masullo's draft aims higher in generality — targeting the **Generalized Riemann Hypothesis for all
unitary Hecke characters of all number fields $F$** [Paper; Masullo p. 6] — and uses **none** of the
machinery of Parts II and III of this book. There are no unitary dual pairs, no supersingular CM
formal groups, no Arakelov lattice slopes, no Hecke congruence modules, no Galois representations,
and no Tate–Shafarevich groups. Instead, Masullo works entirely over the **abelian idele class group
$C_F = \mathbb A_F^\times / F^\times$** (`GL_1`), combining Tate's 1950 thesis `[Tate1967]`, Weil's
explicit formula `[Weil1952]`, Grothendieck's theory of nuclear locally convex spaces
`[Grothendieck1955]`, and strip-weighted **Hardy–Sobolev Hilbert completions** $W_I^{s,2}(C_F)$
indexed by compact intervals $I = [-\alpha, \alpha] \subset \mathbb R$ [Paper; Masullo pp. 11–16,
395–520].

At the same time, Masullo's manuscript arrives in the opposite verification state from Alpöge's
archive:

1. By the author's own acknowledgements [Paper; Masullo p. 6], the PDF was released hurriedly before a
   planned year of polishing with Brian Conrad; Section 12.3 is an empty heading ("*Include section*",
   fn. 1) [Paper; Masullo p. 514], and **Chapter 13 ("Zeros of Hecke $L$-functions", pp. 521–522)**,
   where GRH is meant to be deduced from the Main Trace Formula (`Theorem 12.5.1.1`, p. 519), is a
   two-page placeholder whose main theorem `Theorem 13.3.1.2` carries the footnote *"Insert
   statement"* [Paper; Masullo p. 522].
2. Within hours of release, independent readers and formalizers identified a concrete functional-analytic
   obstruction in **Chapter 10 ("Trace Formula: Spectral Side")**: on **p. 451 after `(10.3.1.18)`**
   (and again in the strip case on **p. 463 at `(10.4.2.24)`**, resting on **Terminology 10.2.1.2(2),
   p. 444**), the proof assumes that normalizing a spectral Markushevich basis of zero-eigenmodes in
   $W_I^{s,2}\mathcal H_F$ automatically bounds its biorthogonal dual functionals uniformly across all
   zeros [Paper; Masullo pp. 444, 451, 463] `[Community]`. Because vertical pairs of critical-line
   zeros of $\zeta(s)$ come arbitrarily close together, individual biorthogonal functionals blow up at
   least inversely with zero spacing. While Yan Ru Pei (`doi:10.5281/zenodo.24409811`) proposed an
   unreviewed finite-rank window bypass on the **single critical line $I = \{0\}$** `[Community]`, the
   **positive-width strip $I = [-\alpha, \alpha]$ ($\alpha > 0$)** required to filter off-line zeros in
   Theorem 12.5.1.1 remains **unrepaired** `[Open]`.

Understanding **both** why Masullo's architectural idea is so natural and **why the entire logical
weight of GRH compresses into strip-independent geometric traces versus strip-nuclear spectral
expansions** is an unforgettable lesson in analytic number theory and functional analysis. We build
that understanding from the ground up.

---

## 14.1 Motivation: from Tate's thesis and Weil's explicit formula to topological strip filtering

### 14.1.1 Tate's idelic zeta integral and why zeros appear as cohomological quotients

Let $F$ be an algebraic number field of degree $d = [F : \mathbb Q] = r_1 + 2r_2$, with adele ring
$\mathbb A_F$, idele group $\mathrm{GL}_1(\mathbb A_F) = \mathbb A_F^\times$, idele norm
$\lvert \cdot \rvert_F : \mathbb A_F^\times \to \mathbb R_{>0}$, idele class group
$C_F := \mathbb A_F^\times / F^\times$, and norm-one compact subgroup
$C_F^1 := \ker(\lvert \cdot \rvert_F : C_F \to \mathbb R_{>0})$ `[Tate1967]`, `[RamakrishnanValenza1999]`
[Expository]. Choosing a splitting of $\lvert \cdot \rvert_F$ identifies
$$C_F \cong C_F^1 \times \mathbb R_{>0},$$
so unitary continuous characters $\chi : C_F^1 \to S^1$ extend canonically to $C_F$, and arbitrary
quasi-characters of $C_F$ have the form $\chi \cdot \lvert \cdot \rvert_F^z$ for $z \in \mathbb C$
(`[Hecke1920]`, `[Tate1967]`).

In Tate's 1950 thesis `[Tate1967]`, one starts with a Schwartz–Bruhat function $f \in \mathcal S(\mathbb A_F)$
and forms its idelic Mellin transform (zeta integral) along $g \in \mathbb A_F^\times$:
$$Z(f, \chi \lvert \cdot \rvert_F^s) := \int_{\mathbb A_F^\times} f(g)\,\chi(g)\,\lvert g \rvert_F^s\,d^\times g
\qquad (\Re s > 1).$$
On factorizable functions $f = \otimes_v f_v$, the integral factors into local Euler factors
$\prod_v Z_v(f_v, \chi_v \lvert \cdot \rvert_v^s) = \Lambda(s, \chi) \cdot E_f(s, \chi)$, where
$\Lambda(s, \chi)$ is the completed Hecke $L$-function (including $\Gamma$-factors at $v \mid \infty$)
and $E_f(s, \chi)$ is entire! How did Tate prove meromorphic continuation and the functional equation
$\Lambda(s, \chi) = \Lambda(1 - s, \overline{\chi})$? By folding the integral over $\mathbb A_F^\times / F^\times = C_F$
and applying **adelic Poisson summation** $\sum_{\xi \in F} f(g\xi) = \lvert g \rvert_F^{-1} \sum_{\xi \in F} \widehat{f}(g^{-1}\xi)$:
if $f$ lies in the **polar hyperplane intersection**
$$\mathcal S_0(\mathbb A_F) := \bigl\{f \in \mathcal S(\mathbb A_F) : f(0) = 0 \text{ and } \widehat{f}(0) = 0\bigr\}$$
(`Definition 2.2.4.4`, [Paper; Masullo p. 91]), both boundary terms $\xi = 0$ disappear! Then the
folded sum on $C_F$,
$$\Phi_F(f)(g) := \sum_{\xi \in F^\times} f(g\xi) \qquad (g \in C_F),$$
decays **faster than every power of $\lvert g \rvert_F$ both as $\lvert g \rvert_F \to \infty$ and as
$\lvert g \rvert_F \to 0^+$** (`Lemma 2.2.2.1`, `Theorem 2.2.3.2`, and `Theorem 2.2.3.4`, [Paper; Masullo pp. 77,
82–83]), so its shifted Mellin transform along the critical line $\Re z = \frac{1}{2}$ (`s` centered
at $0$),
$$\mathcal M\bigl(\lvert \cdot \rvert_F^{1/2} \Phi_F(f)\bigr)(\chi, s)
= \int_{C_F} \lvert g \rvert_F^{1/2}\,\Phi_F(f)(g)\,\chi(g)\,\lvert g \rvert_F^s\,d\mu(g)
= Z\bigl(f, \chi \lvert \cdot \rvert_F^{s + 1/2}\bigr),$$
is an **entire function of $s \in \mathbb C$** that **vanishes at $s_0$ whenever
$\Lambda(s_0 + \tfrac{1}{2}, \chi) = 0$** (to at least the multiplicity $N(s_0 + \tfrac{1}{2}, \chi)$
of the zero of $\Lambda$)!

Now look at the quotient idea that launches spectral approaches to RH (`[Deninger1993]`, `[Connes1999]`,
`[Meyer2005]`, and Masullo `§1.2.1`, [Paper; Masullo pp. 13–15]) [Expository]:

- Inside the space $\mathcal S_E(C_F)$ of smooth functions on $C_F$ of rapid ("exponential/Gaussian")
  decay at both ends $\lvert g \rvert_F \to 0^+$ and $\lvert g \rvert_F \to \infty$, Mellin transforms
  are arbitrary entire functions of rapid vertical decay in strips (denoted $AS(\mathbb C)$ on each
  $\chi$-sector).
- The subspace of functions coming from $\lvert \cdot \rvert_F^{1/2}\Phi_F(\mathcal S_0(\mathbb A_F))$
  consists — on the Mellin side — **precisely of those entire functions divisible by the completed (or
  $S$-stripped) $L$-function $L(s + \tfrac{1}{2}, \chi)$**!
- Therefore, in the **quotient space**
  $$\mathcal H_F \;:=\; \mathcal S_E(C_F) \,\Big/\, \overline{\lvert \cdot \rvert_F^{1/2}\,\Phi_F\bigl(\mathcal S_0(\mathbb A_F)\bigr)},$$
  every non-zero of $L(s + \tfrac{1}{2}, \chi)$ is **killed**, while every zero
  $\rho = \tfrac{1}{2} + s_0$ of multiplicity $N(\rho)$ survives as an $N(\rho)$-dimensional
  Jordan block of the $C_F$-translation action, spanned by the generalized eigenmodes
  $\chi(g)\,\lvert g \rvert_F^{s_0}\,(\log \lvert g \rvert_F)^m$ for $0 \le m < N(\rho)$!

### 14.1.2 Why Weil/Connes need positivity, whereas Masullo tries to filter by strips

Pause and ask the classic skeptic's question (`[Weil1952]`, `[Selberg1956]`, `[Bombieri2000]`)
[Expository]: *if $\mathcal H_F$ already realizes the zeros of $L(s, \chi)$ as the spectrum of $C_F$
acting on a quotient vector space, why didn't Tate's thesis prove the Riemann Hypothesis in 1950?*

Because $\mathcal S_E(C_F)$ is a **Fréchet space**, not a Hilbert space! On $\mathcal S_E(C_F)$,
computing the trace of a convolution operator $A(\varphi) = \int_{C_F} \varphi(g)\,\rho(g)\,d\mu(g)$
($\varphi \in C_c^\infty(C_F)$) merely reproduces **Weil's classical explicit formula** (`[Weil1952]`;
`Theorem B.4.4.7`, [Paper; Masullo p. 623]):
$$\sum_{\rho} \widehat{\varphi}\bigl(\rho - \tfrac{1}{2}\bigr)
\;=\; \text{(archimedean + prime-power geometric terms of }\varphi\text{)},$$
in which **every** nontrivial zero $\rho \in \{\,0 < \Re \rho < 1\,\}$ — whether on $\Re \rho = \frac{1}{2}$
or off it! — contributes cleanly to the left-hand side! Look at the two classic ways mathematicians
have tried to force $\Re \rho = \frac{1}{2}$ out of that identity [Expository]:

1. **The Weil–Connes positivity route (`[Weil1952]`, `[Connes1999]`, `[Meyer2005]`):** Complete the
   space in a **single $L^2$ Hilbert norm on the critical line** ($\Re s = 0$, i.e. $\Re \rho = \frac{1}{2}$),
   or pass to an absorptive/virtual representation `[Meyer2005]`. In Connes's noncommutative-geometric
   trace formula `[Connes1999]`, restricting to the $L^2$ Hilbert space *automatically* discards off-line
   zeros from the Hilbert spectrum (yielding an unconditional trace formula for the **critical-line
   zeros alone**!), **provided** one switches from a quotient to a subspace/cutoff limit — at the
   price that proving *all* zeros were captured becomes equivalent to establishing **Weil positivity**
   $W(\varphi \ast \varphi^\ast) \ge 0$!
2. **Masullo's strip-completion route (`§1.1.3`, `§1.4.6`, `§1.4.8`, [Paper; Masullo pp. 11–12, 30–31]):**
   Masullo explicitly **renounces Weil's positivity criterion** (`§1.4.6`, p. 30: *"Weil's Positivity
   Criterion is not used"*) [Paper; Masullo p. 30]. Instead, for **every** compact interval
   $I = [-\alpha, \alpha] \subset \mathbb R$ ($\alpha \ge 0$) and Sobolev order $s \ge 2[F : \mathbb Q]$,
   he completes $\mathcal S_E(C_F)$ and its quotient $\mathcal H_F$ inside the **strip-weighted
   Hardy–Sobolev Hilbert space** $W_I^{s,2}(C_F)$ (`§1.1.3`, pp. 11–12), whose weight
   $\max\bigl\{\lvert g \rvert_F^{-2\alpha},\, \lvert g \rvert_F^{2\alpha}\bigr\}\,(1 + \lvert \log\lvert g \rvert_F \rvert^2)^{s/2}$
   admits an eigenmode $\chi(g)\lvert g \rvert_F^{z}$ into the continuous dual **if and only if
   $\Re z \in I = [-\alpha, \alpha]$**, i.e., **if and only if the zero $\rho = \tfrac{1}{2} + z$ lies
   in the closed strip $\tfrac{1}{2} - \alpha \le \Re \rho \le \tfrac{1}{2} + \alpha$**!

Now watch the punchline of Masullo's strategy (`§1.4.8`, p. 31, and `Theorem 12.5.1.1`, p. 519)
[Paper; Masullo pp. 31, 519]:

- On the **spectral side** (Chapter 10), computing the trace of $A(\varphi)$ ($\varphi \in D(C_F)$
  vanishing pointwise on the norm-$1$ subgroup $C_F^1$, written $\varphi(C_F^1) = 0$, i.e. radially
  $\varphi(1) = 0$) on the quotient Hilbert/Banach space $W_I^{s,2}\mathcal H_F$ sums **only over zeros in the strip $\Re \rho \in \bigl[\tfrac{1}{2} - \alpha,\, \tfrac{1}{2} + \alpha\bigr]$**!
- On the **geometric side** (Chapters 11–12), Masullo resolves the quotient $\mathcal H_F$ by
  periodic "orbital Schauder bases" indexed by prime ideals $\mathfrak p$ (`Ch. 11`) plus an $S$-local
  residual integral (`§12.4`), and claims (`Theorem 12.5.1.1`, p. 519) that for every $\alpha \in (0, \tfrac{1}{2})$
  (or any compact $I = [-\alpha, \alpha]$), **the geometric trace evaluates to the exact same
  $\alpha$-independent Weil explicit-formula distribution**!
- If that equality held for **every** $\alpha > 0$, then shrinking $\alpha$ from $\frac{1}{2}$ down
  toward $0^+$ could never drop a zero along the way — forcing every zero in $0 < \Re \rho < 1$ to
  lie on $\Re \rho = \frac{1}{2}$!

Even before checking a single lemma, a functional analyst's radar lights up at once: *in a strip
identity where the right-hand side is independent of $\alpha > 0$ and the left-hand side sums over
zeros in $\bigl[\frac{1}{2} - \alpha, \frac{1}{2} + \alpha\bigr]$, 100% of the mathematical difficulty
of GRH has been compressed into two analytical claims — (A) that the convolution operator on the
quotient $W_I^{s,2}\mathcal H_F$ is genuinely nuclear/trace-class with trace equal to the sum over
zeros in $\frac{1}{2} + I$, and (B) that the geometric kernel surgery in $W_I^{s,2}$ commutes with
taking traces without picking up hidden boundary residues from zeros outside $\frac{1}{2} + I$!*

### 14.1.3 Essential distinction: Masullo's $\mathrm{GL}_1$ adelic $\theta$-sum versus Chapter 7's Weil oscillator $\theta$-kernel

Because both routes prominently feature the phrase **"theta function"**, let us prevent a fatal
terminological confusion right away (`notes/proof-map.md`, node `P17`) [Expository]:

| Feature | Alpöge–Claude Chapter 7 $\theta$-kernel | Masullo Chapter 2 "adelic $\theta$-function" |
|---|---|---|
| Underlying group | Reductive dual pair $U(X_{j-1}) \times U(X_j) \subset \mathrm{Sp}_{2N}(\mathbb A_F)$ `[Weil1964]`, `[Howe1979]` | Multiplicative group $\mathrm{GL}_1(\mathbb A_F) = \mathbb A_F^\times$ acting linearly on $\mathbb A_F$ `[Tate1967]` [Paper; Masullo p. 77] |
| Formula | $\Theta_\Phi(g, h) = \sum_{v \in V(F)} \bigl(\omega(g, h)\Phi\bigr)(v)$ where $\omega$ is the **quadratic/Hermitian Weil oscillator representation** | $\Psi_F(f)(g, 0) = \sum_{\xi \in F^\times} f(g\xi)$, a **purely linear multiplicative $F^\times$-orbit sum** (`(2.2.2.1)`, p. 77) |
| Why classical $\sum e^{-\pi n^2 t}$ appears | Because $n \mapsto n^2$ is the **norm form of a rank-$1$ quadratic space**, transformed by $\mathrm{Mp}_2(\mathbb R)$! | Only if one manually plugs a Gaussian $f_\infty(x) = e^{-\pi x^2}$ into $f(t^{1/2}\xi)$ (`t` replaced by $t^{1/2}$); $g \mapsto g\xi$ itself has **no quadratic form** and **no $\mathrm{SL}_2$ modularity**! |
| Role in the proof | Transfers automorphic forms up a chain of $m \asymp \sqrt{x}$ higher-rank unitary groups $U(X_0) \to \cdots \to U(X_m)$ (`P7`, `P17`) | Generates the principal divisor submodule $\Phi_F(\mathcal S_0(\mathbb A_F)) \subset \mathcal S_E(C_F)$ whose Mellin transform carries $L(s + \tfrac{1}{2}, \chi)$ (`Chs. 2–3`) |

---

## 14.2 Worked examples

Let us make every piece of Masullo's machinery completely concrete by computing three worked examples
by hand: (1) an explicit $\mathrm{GL}_1(\mathbb A_{\mathbb Q})$ $\theta$-sum for the odd character
$\chi_{-4}$ together with Masullo's dilated-group toy model $\mathbb R_{>0}/\gamma^{\mathbb Z}$;
(2) a clean analytical model showing how strip-independence of a trace would force zero-freeness via
Masullo's one-sided test family $\varphi_z(t) = t^{-z}\mathbf{1}_{t > 1}$; and (3) a four-line
hand proof of why **Terminology 10.2.1.2(2) (p. 444)** fails on close critical-line zeros [Expository].

### 14.2.1 Hand calculation of $\Psi_{\mathbb Q}(f)(g, 0)$ for $\chi_{-4}$ and the dilated-group toy model $\mathbb R_{>0}/\gamma^{\mathbb Z}$

**Part A: Rational and $2$-adic $\mathrm{GL}_1$ $\theta$-sums (`Lemma 2.2.2.1`, p. 77).** Take
$F = \mathbb Q$, so $\mathbb A_{\mathbb Q} = \mathbb R \times \mathbb A_{\mathbb Q, f}$ and
$$C_{\mathbb Q} = \mathbb A_{\mathbb Q}^\times / \mathbb Q^\times \;\cong\; \mathbb R_{>0} \times \widehat{\mathbb Z}^\times,$$
because every nonzero rational idele $g = (g_\infty, (g_p)_p) \in \mathbb A_{\mathbb Q}^\times$ can be
multiplied by a unique $\xi \in \mathbb Q^\times$ (`|\xi|_\infty = \prod_p |g_p|_p` and appropriate
sign) so that $\xi g = (t, u)$ with $t = \lvert g \rvert_{\mathbb Q} \in \mathbb R_{>0}$ and
$u = (u_p)_p \in \widehat{\mathbb Z}^\times = \prod_p \mathbb Z_p^\times$!

First, test the unramified even Schwartz–Bruhat function
$f_{\mathrm{even}}(x_\infty, x_f) = e^{-\pi x_\infty^2} \prod_p \mathbf{1}_{\mathbb Z_p}(x_p)$ at
$g = (t, 1) \in \mathbb R_{>0} \times \widehat{\mathbb Z}^\times$: a nonzero rational $\xi \in \mathbb Q^\times$
satisfies $u_p \xi = \xi \in \mathbb Z_p$ for every prime $p$ if and only if $\xi = n \in \mathbb Z \setminus \{0\}$,
giving
$$\Psi_{\mathbb Q}(f_{\mathrm{even}})\bigl((t, 1), 0\bigr)
= \sum_{n \in \mathbb Z \setminus \{0\}} e^{-\pi (t n)^2}
= 2 \sum_{n = 1}^\infty e^{-\pi n^2 t^2} = \vartheta(t^2) - 1.$$
Look at why $n^2$ appeared in the exponent: **only because we chose $f_\infty(x_\infty) = e^{-\pi x_\infty^2}$!**
If instead we pick the non-Gaussian Schwartz function $f_\infty(x_\infty) = (1 - 2\pi x_\infty^2)e^{-\pi x_\infty^2}$
(satisfying $f_\infty(0) = 1 \neq 0$, or better, the polar-free difference $f_1(x_\infty) = x_\infty^2 e^{-\pi x_\infty^2} - \frac{1}{2\pi}\widehat{\dots}$),
$\Psi_{\mathbb Q}(f)\bigl((t, 1), 0\bigr) = \sum_{n \neq 0} f_\infty(t n)$ scales $n$ **linearly**
as $t n$, with Mellin transform $\int_0^\infty t^s \bigl(\sum_{n \ge 1} f_\infty(t n)\bigr)\frac{dt}{t} = \zeta(s) \int_0^\infty t^s f_\infty(t)\frac{dt}{t}$!

Even cleaner, take the odd Dirichlet character $\chi_{-4} \bmod 4$ ($\chi_{-4}(1) = 1$, $\chi_{-4}(3) = -1$),
viewed as a continuous character of $\widehat{\mathbb Z}^\times \twoheadrightarrow (\mathbb Z/4\mathbb Z)^\times$
via its $2$-adic component $\chi_2 : \mathbb Z_2^\times \to \{\pm 1\}$ (`\chi_2(1 + 4\mathbb Z_2) = +1`,
`\chi_2(3 + 4\mathbb Z_2) = -1`). Choose the factorizable Schwartz–Bruhat function
$$f_{\chi_{-4}}(x_\infty, (x_p)_p) := x_\infty e^{-\pi x_\infty^2} \cdot
\bigl(\mathbf{1}_{1 + 4\mathbb Z_2}(x_2) - \mathbf{1}_{3 + 4\mathbb Z_2}(x_2)\bigr) \cdot
\prod_{p \ge 3} \mathbf{1}_{\mathbb Z_p}(x_p).$$
Check three facts by hand:

1. **Automatic membership in $\mathcal S_0(\mathbb A_{\mathbb Q})$ (`Def. 2.2.4.4`, p. 91):** At
   $x = 0$, $f_\infty(0) = 0 \cdot e^0 = 0$, and on the Fourier side $f_\infty$ is odd so
   $\widehat{f}_\infty(0) = \int_{\mathbb R} x e^{-\pi x^2}\,dx = 0$ (and at $p = 2$,
   $\int_{\mathbb Z_2} (\mathbf{1}_{1+4\mathbb Z_2} - \mathbf{1}_{3+4\mathbb Z_2})\,dx_2 = \frac{1}{4} - \frac{1}{4} = 0$
   too!). Thus **no pole-killing subtraction at $0$ or $\widehat{0}$ is needed** when $\chi$ is nontrivial!
2. **Evaluation of $\Phi_{\mathbb Q}(f_{\chi_{-4}})(t, u)$ on $C_{\mathbb Q} \cong \mathbb R_{>0} \times \widehat{\mathbb Z}^\times$:**
   For $(t, u) \in \mathbb R_{>0} \times \widehat{\mathbb Z}^\times$, a rational $\xi \in \mathbb Q^\times$
   has $u_p \xi \in \mathbb Z_p$ for all $p \ge 3$ and $u_2 \xi \in \mathbb Z_2^\times$ if and only if
   $\xi = n \in \mathbb Z$ is an **odd integer**! Moreover, since $\mathrm{sgn}(n)\cdot n = \lvert n \rvert$
   and $\chi_2(-1) = -1 = \mathrm{sgn}(-1)$, pairing positive and negative odd integers $n = \pm(2k+1)$
   gives
   $$\Phi_{\mathbb Q}(f_{\chi_{-4}})(t, u)
   = \sum_{\substack{n \in \mathbb Z \\ n\text{ odd}}} (t n) e^{-\pi t^2 n^2} \chi_2(u_2 n)
   = 2\,\chi_2(u_2) \sum_{k = 0}^\infty (-1)^k (2k + 1)\,t\,e^{-\pi (2k + 1)^2 t^2}!$$
3. **Critical-line Mellin transform (`§1.2.1`, p. 13):** Multiply by $\lvert g \rvert_{\mathbb Q}^{1/2} = t^{1/2}$
   and integrate against $\overline{\chi_2(u_2)}\,t^s\,\frac{dt}{t}\,du$:
   $$\int_{C_{\mathbb Q}} t^{1/2}\,\Phi_{\mathbb Q}(f_{\chi_{-4}})(t, u)\,\overline{\chi_2(u_2)}\,t^s\,\frac{dt}{t}\,du
   = 2 \sum_{k = 0}^\infty \frac{(-1)^k}{(2k + 1)^{s + 1/2}} \int_0^\infty w^{s + 3/2} e^{-\pi w^2}\,\frac{dw}{w}
   = \pi^{-(s + 3/2)/2}\,\Gamma\Bigl(\frac{s + 3/2}{2}\Bigr)\,L\Bigl(s + \tfrac{1}{2},\, \chi_{-4}\Bigr)!$$
   Since $\Gamma\bigl(\frac{s + 3/2}{2}\bigr)$ has **no zeros anywhere in $\mathbb C$** and no poles on
   $\Re s > -\frac{3}{2}$, the zeros of this Mellin transform in the strip $-\frac{1}{2} < \Re s < \frac{1}{2}$
   are **with exact multiplicity** the nontrivial zeros of $L(s + \tfrac{1}{2}, \chi_{-4})$!

**Part B: Masullo's dilated-group toy model $G = \mathbb R_{>0} / \gamma^{\mathbb Z}$ (`§1.2.8`, pp. 16–17, and `Ch. 4`, pp. 155–220).**
Where do Masullo's "orbital Schauder bases" and vanishing prime-shell traces (`Theorem 11.3.2.1`, p. 495)
come from? Fix a prime $p$ (so $\gamma = p > 1$), and look at a single multiplicative periodic quotient
$G_p := \mathbb R_{>0} / p^{\mathbb Z} \cong \mathbb R / (\log p)\mathbb Z$ under $u = \log t$
[Paper; Masullo pp. 16–17] [Expository]!

On the circle $\mathbb R / (\log p)\mathbb Z$ of circumference $\log p$:

- The characters $\mathbf{e}_m(t) := t^{2\pi i m / \log p} = e^{2\pi i m u / \log p}$ ($m \in \mathbb Z$)
  form an orthogonal basis of $L^2(G_p, \frac{dt}{t\log p})$ and an unconditional Schauder basis of
  $C^\infty(G_p)$. Notice what those exponents $s_m = \frac{2\pi i m}{\log p}$ are: **they are the
  exact poles of the local Euler factor $(1 - p^{-s})^{-1}$!**
- Now take any smooth compactly supported test function $\varphi \in C_c^\infty(\mathbb R_{>0})$
  supported **strictly inside the open fundamental interval $(1, p)$** (so $\varphi(p^k) = 0$ for
  **every** $k \in \mathbb Z$, matching Masullo's shell-indentation condition around the identity!),
  and let $A_p(\varphi)$ act on $L^2(G_p)$ by convolution $(A_p(\varphi)\psi)(t) = \int_0^\infty \varphi(y)\,\psi(t/y)\,\frac{dy}{y}$.
- Each basis mode $\mathbf{e}_m$ is an eigenvector of $A_p(\varphi)$ with eigenvalue
  $\lambda_m = \int_0^\infty \varphi(y)\,y^{-2\pi i m / \log p}\,\frac{dy}{y} = \widehat{\Phi}\bigl(\frac{m}{\log p}\bigr)$
  (where $\Phi(u) := \varphi(e^u)$ is supported strictly inside $(0, \log p)$!). By the **classical
  Poisson summation formula** on $\mathbb R$:
  $$\operatorname{Tr}_{L^2(G_p)}\bigl(A_p(\varphi)\bigr)
  = \sum_{m \in \mathbb Z} \lambda_m
  = (\log p) \sum_{k \in \mathbb Z} \Phi(k \log p)
  = (\log p) \sum_{k \in \mathbb Z} \varphi(p^k) \;=\; 0!$$
  And what if $\varphi$ is supported on $(1, \infty)$ without vanishing at $p^k$ ($k \ge 1$)? Then
  $(\log p)\sum_{k \ge 1} \varphi(p^k)$ is the **exact prime-power sum at $p$ in Weil's explicit
  formula**! In Chapter 11 (`pp. 475–496`), Masullo tries to lift this one-prime circle calculation
  simultaneously across all primes $\mathfrak p$ of $F$!

### 14.2.2 Functional-analytic strip model: why $\alpha$-independence of the geometric side carries 100% of GRH

Suppose someone hands you the statement of **Main Theorem 12.5.1.1** ([Paper; Masullo pp. 519–520]):
for a fixed unitary character $\chi$ of $C_{\mathbb Q}^1$ (say $\chi = \chi_{-4}$, so $L(s, \chi_{-4})$
is entire and $\delta(\chi) = 0$), every compact symmetric strip $I = [-\alpha, \alpha]$ ($\alpha > 0$),
and every smooth compactly supported radial test function $\varphi \in C_c^\infty(\mathbb R_{>0})$
satisfying **pointwise vanishing at the identity shell $\varphi(1) = 0$** (the radial specialization of
$\varphi(C_F^1) = 0$, i.e. $\varphi\rvert_{C_F^1} \equiv 0$; [Paper; Masullo pp. 28, 30, 35, 514, 519]),
$$\sum_{\substack{\rho :\, \Lambda(\rho, \chi) = 0 \\ \lvert \Re \rho - 1/2 \rvert \le \alpha}}
N(\rho)\,\mathcal M(\varphi^\vee)\bigl(\rho - \tfrac{1}{2}\bigr)
\;=\; \mathcal W_{\mathrm{geom}}(\varphi),$$
where $\mathcal M(\psi)(s) = \int_0^\infty \psi(t)\,t^s\,\frac{dt}{t}$, $\varphi^\vee(t) = \varphi(t^{-1})$,
and **$\mathcal W_{\mathrm{geom}}(\varphi)$ does not depend on $\alpha$** (`§1.4.2–1.4.5`, [Paper;
Masullo pp. 28–30]) [Expository]!

Let us check by hand why **that single $\alpha$-independence assertion immediately implies GRH for
$L(s, \chi)$**! Suppose toward a contradiction that $\Lambda(s, \chi)$ had an off-line zero
$\rho_0 = \frac{1}{2} + \beta_0 + i\gamma_0$ with $0 < \beta_0 < \frac{1}{2}$. Pick two strip widths
$0 < \alpha_1 < \beta_0 < \alpha_2 < \frac{1}{2}$ such that no zero of $\Lambda(s, \chi)$ lies on the
boundary lines $\Re s = \frac{1}{2} \pm \alpha_1$ or $\Re s = \frac{1}{2} \pm \alpha_2$. Subtracting
the purported trace identity at $I_1 = [-\alpha_1, \alpha_1]$ from the one at $I_2 = [-\alpha_2, \alpha_2]$
**cancels $\mathcal W_{\mathrm{geom}}(\varphi)$ identically** ($\mathcal W_{\mathrm{geom}} - \mathcal W_{\mathrm{geom}} = 0$!)
and leaves
$$\sum_{\substack{\rho :\, \Lambda(\rho, \chi) = 0 \\ \alpha_1 < \lvert \Re \rho - 1/2 \rvert \le \alpha_2}}
N(\rho)\,\int_0^\infty \varphi(t)\,t^{1/2 - \rho}\,\frac{dt}{t} \;=\; 0$$
for **every** $\varphi \in C_c^\infty(\mathbb R_{>0})$ satisfying $\varphi(1) = 0$!

Now plug in Masullo's one-sided smooth cutoff family (`§1.4.2`, [Paper; Masullo pp. 28–29])
**or** an explicitly zero-mean radial difference kernel [Expository]:
- **Masullo's one-sided cutoff family (`pp. 28–29`):** Because $\varphi(1) = 0$ is a **pointwise**
  condition at $t = 1$ (needed on `p. 514` `(12.4.1.3)` to annihilate the divergent diagonal term
  $\varphi(1)\log(\lambda\lambda')$), any smooth cutoff $\varphi_{R, \varepsilon, z}(t) := \chi_{R,\varepsilon}(t)\,(t^{-z}\mathbf{1}_{t > 1} * \rho_\varepsilon)(t)$
  supported strictly inside $(1 + \varepsilon, R) \subset (1, \infty)$ satisfies $\varphi_{R,\varepsilon,z}(1) = 0$
  **identically**! Letting $R \to \infty$ for $\Re z > \alpha_2$ (justified on the finite vertical strip
  $\alpha_1 < \lvert \Re\rho - \frac{1}{2} \rvert \le \alpha_2$ by rapid vertical decay of
  $\widehat{\rho}_\varepsilon$ and $N(T+1) - N(T) = O(\log(\lvert T \rvert + 2))$) evaluates
  $\int_1^\infty t^{-z} t^{1/2 - \rho}\frac{dt}{t} = \frac{1}{z - (1/2 - \rho)}$, giving
  $$F(z) \;:=\; \sum_{\alpha_1 < \lvert \Re \rho - 1/2 \rvert \le \alpha_2} \frac{N(\rho)\,\widehat{\rho}_\varepsilon(\rho - \tfrac{1}{2})}{z - (1/2 - \rho)} \;=\; 0 \qquad (\forall\,\Re z > \alpha_2)!$$
- *(Sanity check — even under an added zero-mean constraint $\int_0^\infty \psi(t)\frac{dt}{t} = 0$):*
  If one further restricts to test functions of **zero multiplicative integral** on $\mathbb R_{>0}$,
  one replaces $t^{-z}\mathbf{1}_{t > 1}$ by the genuinely zero-mean difference
  $$\psi_z^{\mathrm{zm}}(t) \;:=\; \Bigl(t^{-z} - \frac{1}{z}\,t^{-1}\Bigr)\,\mathbf{1}_{t > 1}
  \qquad \Bigl(\int_1^\infty \psi_z^{\mathrm{zm}}(t)\,\frac{dt}{t} = \frac{1}{z} - \frac{1}{z} = 0\text{ for }\Re z > 0\Bigr),$$
  supported in $(1, \infty)$ after one-sided smoothing on $(1 + \varepsilon, R)$ with zero mean preserved;
  since $\int_1^\infty t^{-1} t^{1/2 - \rho}\frac{dt}{t} = \frac{1}{1 - (1/2 - \rho)}$ for
  $\lvert \Re\rho - \frac{1}{2} \rvert < \frac{1}{2} < 1$, the resulting identity is
  $$F_{\mathrm{zm}}(z) \;:=\; \sum_{\alpha_1 < \lvert \Re \rho - 1/2 \rvert \le \alpha_2} N(\rho)\,\widehat{\rho}_\varepsilon\bigl(\rho - \tfrac{1}{2}\bigr)\Bigl(\frac{1}{z - (1/2 - \rho)} - \frac{1}{z\bigl(1 - (1/2 - \rho)\bigr)}\Bigr) \;=\; 0 \qquad (\forall\,\Re z > \alpha_2)!$$
Look at $F(z)$ (or $F_{\mathrm{zm}}(z)$ for $z \neq 0$): it is meromorphic on $\mathbb C$ with simple
poles at $z = \frac{1}{2} - \rho \neq 0$ and vanishes identically on the half-plane $\Re z > \alpha_2$.
By **analytic continuation**, $F(z) \equiv 0$ (and $F_{\mathrm{zm}}(z) \equiv 0$) on $\mathbb C$, so its
residue at $z_1 = \beta_0 - i\gamma_0 \neq 0$ (corresponding to the reflected zero
$1 - \overline{\rho}_0 = \frac{1}{2} - \beta_0 + i\gamma_0$, where $z_1 - (\frac{1}{2} - (1 - \overline{\rho}_0)) = 0$)
must vanish:
$$N(1 - \overline{\rho}_0)\,\widehat{\rho}_\varepsilon(-\beta_0 + i\gamma_0) = 0.$$
Choosing $\varepsilon > 0$ small enough that $\widehat{\rho}_\varepsilon(-\beta_0 + i\gamma_0) \neq 0$
forces $N(1 - \overline{\rho}_0) = N(\rho_0) = 0$, contradiction! (Indeed, by the evening of 20
November, David Loeffler reported formalizing in Lean 4 that RH follows from Masullo's stated
`Theorem 12.5.1.1` `[Community]`.)

And **why** did that proof feel "too easy"? Because **subtracting $I_1$ from $I_2$ assumed that
both sides of Theorem 12.5.1.1 exist and agree with the same $\mathcal W_{\mathrm{geom}}(\varphi)$!**
In reality, changing the space from $W_{I_2}^{s,2}$ to $W_{I_1}^{s,2}$ changes the topology in which
the quotient $\mathcal H_F$ is completed; if an off-line zero $\rho_0$ existed between $I_1$ and $I_2$,
shifting the contour of a Mellin trace from $\Re s = \alpha_2$ to $\Re s = \alpha_1$ would cross the
pole at $\rho_0 - \frac{1}{2}$ and **change the geometric integral by that exact residue** — unless one
has rigorously proved both spectral nuclearity on $W_I^{s,2}\mathcal H_F$ and strip-invariance of the
geometric trace!

### 14.2.3 Four-line hand proof of biorthogonal blow-up on close zeros (refuting Terminology 10.2.1.2(2), p. 444)

Let us now verify by hand the exact functional-analytic error on **p. 444** and **p. 451** of
Masullo's draft (`chapters/02-the-story-so-far.md`, `[Community]`) [Expository].

On **p. 444** (`Terminology 10.2.1.2`, [Paper; Masullo p. 444]), Masullo considers a Markushevich
basis $\{x_m\}_{m \in M}$ with biorthogonal dual functionals $\{f_m\}_{m \in M} \subset E_\beta'$
($f_m(x_n) = \delta_{m,n}$). After defining $\{x_m\}$ to be *normalized* if $\{x_m\}$ is bounded in $E$
and bounded away from $0$, item `(2)` asserts verbatim that *if $\{x_m\}$ is normalized, then
$\{f_m\} \subset E_\beta'$ is also normalized (in particular, **uniformly bounded in norm**)* — and on
**p. 451 after `(10.3.1.18)`** (`Theorem 10.3.1.1`, [Paper; Masullo p. 451]) and **p. 463 at
`(10.4.2.24)`** ([Paper; Masullo p. 463]), the proof invokes that uniform bound $\lVert \psi_{\chi, t, m} \rVert \le C$
across all critical-line (or strip) zeros $\rho = \frac{1}{2} + it$ to make the nuclear series
$\sum_\rho \lvert \widehat{\varphi}(\rho - \frac{1}{2}) \rvert\,\lVert \eta_\rho \rVert \cdot \lVert \psi_\rho \rVert$
converge!

Why is `Terminology 10.2.1.2(2)` false even in a $2$-dimensional Euclidean plane $\mathbb C^2$? Take
$x_1 = (1, 0)$ and $x_2 = (\cos\theta,\, \sin\theta)$ for a small angle $\theta \in (0, \frac{\pi}{2})$.
Both vectors have **exact unit norm** $\lVert x_1 \rVert = \lVert x_2 \rVert = 1$ (bounded and bounded
away from $0$!), yet their unique biorthogonal dual vectors in $\mathbb C^2$ are
$$f_1 = \bigl(1,\, -\cot\theta\bigr), \qquad f_2 = \bigl(0,\, \csc\theta\bigr),
\qquad\text{so}\qquad
\lVert x_2 \rVert \cdot \lVert f_2 \rVert = \frac{1}{\sin\theta} \;\xrightarrow{\;\theta \to 0^+\;}\; +\infty!$$

Now carry out the **exact same calculation** directly inside Masullo's $0$-line Sobolev dual space
$W_{\{0\}}^{-s, 2}(\mathbb R_{>0})$! Watch Masullo's exponent convention carefully (`§1.1.3` p. 11,
`Definition 9.1.1.1` `(9.1.1.3)` p. 396 — *"related to our $s$ by doubling"* — and `Proposition 10.2.1.3`
p. 443, [Paper; Masullo pp. 11, 396, 443]): under the logarithmic coordinate $u = \log t \in \mathbb R$
($\frac{dt}{t} = du$), Masullo's **squared** $W_{\{0\}}^{-s,2}$ norm integrates against **`(1 + u^2)^{-s/2}`**
(matching standard Sobolev space $H^{-s/2}(\mathbb R)$, convergent for **$s > 1$**!), so the dual
eigenmode $t \mapsto t^{it}$ corresponds in unweighted $L^2(\mathbb R)$ to
$$\eta_t(u) \;:=\; e^{i t u}\,(1 + u^2)^{-s/4} \;\in\; L^2(\mathbb R) \qquad (s > 1).$$
Let us check **both** Masullo's minimal degree $s = 2[\mathbb Q : \mathbb Q] = 2$ and the smooth-derivative
regime $s > 3$ by hand [Expository]:

1. **Exact Gram-overlap blow-up at $s = 2$ ($s > 1$):** At $s = 2$, $(1 + u^2)^{-s/2} = (1 + u^2)^{-1}$,
   so $\lVert \eta_t \rVert_{-2, 2}^2 = \int_{-\infty}^\infty \frac{du}{1 + u^2} = \pi$ (whereas
   $\int_{-\infty}^\infty \frac{u^2\,du}{1 + u^2} = +\infty$), and for any two critical-line zeros
   $\frac{1}{2} + i t_1, \frac{1}{2} + i t_2$ ($\Delta t := t_2 - t_1 > 0$) residue calculus at $u = i$
   gives $\langle \eta_{t_1}, \eta_{t_2} \rangle_{-2,2} = \int_{-\infty}^\infty \frac{e^{-i\Delta t\,u}}{1 + u^2}\,du = \pi\,e^{-\Delta t}$!
   By the two-vector Gram bound of Section 14.2.1 with $\lvert \cos\theta \rvert = e^{-\Delta t}$, any
   biorthogonal functional $\psi_{t_2}$ satisfies
   $$\lVert \eta_{t_2} \rVert_{-2, 2} \cdot \lVert \psi_{t_2} \rVert_{2, 2}
   \;\ge\; \frac{1}{\sqrt{1 - e^{-2\Delta t}}} \;\sim\; \frac{1}{\sqrt{2\,\Delta t}} \;\longrightarrow\; +\infty \qquad (\Delta t \to 0^+)!$$
2. **Universal derivative bound for every $s > 3$:** For any $s > 3$, both $\eta_t$ and
   $\partial_t \eta_t(u) = i u\,e^{i t u}(1 + u^2)^{-s/4}$ lie in $L^2(\mathbb R)$, and Euler's Beta
   integral ($u = \tan\theta$, $du = \sec^2\theta\,d\theta$) gives:
   $$\lVert \eta_t \rVert_{-s,2}^2 = \int_{-\infty}^\infty \frac{du}{(1 + u^2)^{s/2}}
   = \frac{\sqrt{\pi}\,\Gamma\bigl(\tfrac{s - 1}{2}\bigr)}{\Gamma\bigl(\tfrac{s}{2}\bigr)},
   \qquad
   \bigl\lVert \partial_t \eta_t \bigr\rVert_{-s,2}^2 = \int_{-\infty}^\infty \frac{u^2\,du}{(1 + u^2)^{s/2}}
   = \frac{\sqrt{\pi}\,\Gamma\bigl(\tfrac{s - 3}{2}\bigr)}{2\,\Gamma\bigl(\tfrac{s}{2}\bigr)}
   = \frac{\lVert \eta_t \rVert_{-s,2}^2}{s - 3}!$$
   Pause to admire that exact identity: **for every $s > 3$ and $t \in \mathbb R$, $\lVert \eta_t \rVert_{-s,2}$
   is independent of $t$ and $\lVert \partial_t \eta_t \rVert_{-s,2} = \frac{\lVert \eta_t \rVert_{-s,2}}{\sqrt{s - 3}}$!**
   (At $s = 4$, $(1 + u^2)^{-s/2} = (1 + u^2)^{-2}$, $\int_{-\infty}^\infty \frac{du}{(1+u^2)^2} = \frac{\pi}{2} = \int_{-\infty}^\infty \frac{u^2\,du}{(1+u^2)^2}$,
   and $\sqrt{s - 3} = \sqrt{4 - 3} = 1$!)

Now let $\frac{1}{2} + i t_1$ and $\frac{1}{2} + i t_2$ ($t_1 < t_2$, spacing $\Delta t := t_2 - t_1 > 0$)
be **any two distinct simple critical-line zeros of $\zeta(s)$**, and for $s > 3$ let $\psi_{t_2}$ be
**any** continuous linear functional on the quotient Hilbert space biorthogonal to the zero modes
($\langle \psi_{t_2}, \eta_{t_2} \rangle = 1$ and $\langle \psi_{t_2}, \eta_{t_1} \rangle = 0$). By
Cauchy–Schwarz and $\eta_{t_2} - \eta_{t_1} = \int_{t_1}^{t_2} \partial_t \eta_\tau\,d\tau$:
$$1 = \bigl\lvert \langle \psi_{t_2},\, \eta_{t_2} - \eta_{t_1} \rangle \bigr\rvert
\le \lVert \psi_{t_2} \rVert_{s,2} \int_{t_1}^{t_2} \bigl\lVert \partial_t \eta_\tau \bigr\rVert_{-s,2}\,d\tau
= \frac{\Delta t}{\sqrt{s - 3}}\,\lVert \eta_{t_2} \rVert_{-s,2}\,\lVert \psi_{t_2} \rVert_{s,2},$$
which rearranges in one line to:
$$\lVert \eta_{t_2} \rVert_{-s,2} \cdot \lVert \psi_{t_2} \rVert_{s,2} \;\ge\; \frac{\sqrt{s - 3}}{t_2 - t_1}!$$
Look at what happens as $T \to \infty$: by the Riemann–von Mangoldt formula and Selberg's positive-proportion
theorem (`[Selberg1956]` / classical critical-line zero counting), $\zeta(\tfrac{1}{2} + it)$ has
$\gg T \log T$ critical-line zeros on $[0, T]$, so by the pigeonhole principle infinitely many pairs of
adjacent critical-line zeros satisfy $\Delta t = t_{k+1} - t_k \ll \frac{1}{\log T} \to 0$! (Even at
low height, real ball-arithmetic isolation of close $\zeta$-zeros with $\Delta \gamma \approx 0.0377$
already forces the norm product above $20.4$ in Masullo's exact $s = 4$ norm, closely matching our
one-line $L^2(\mathbb R)$ bound $\frac{\sqrt{4 - 3}}{0.0377} \approx \mathbf{26.5}$; see
`chapters/02-the-story-so-far.md` `[Community]`.) Hence **no finite constant $C$ can ever bound
$\lVert \eta_\rho \rVert \cdot \lVert \psi_\rho \rVert$ across all zeros of $\zeta(s)$**!

---

## 14.3 Exact definitions from Masullo's manuscript

We now record the precise objects defined across Chapters 1–13 of *The Music of the Primes*, citing
Masullo's exact section and printed page numbers `[Paper; Masullo p. …]`.

### 14.3.1 Adelic $\theta$-sums, polar hyperplanes, and the Fundamental Divisor Exact Sequence (`Chs. 1–3`)

**Definition 14.1 (Adelic $\theta$-operator, polar hyperplanes, and the quotient $\mathcal H_F$, `§1.2.1` pp. 13–15, `Lemma 2.2.2.1` p. 77, `Def. 2.2.4.4` p. 91).**
Let $F$ be a number field with adele ring $\mathbb A_F$, idele class group $C_F = \mathrm{GL}_1(\mathbb A_F)/F^\times$,
norm-one subgroup $C_F^1$, and character space $\Omega(C_F) := \operatorname{Hom}_{\mathrm{cont}}(C_F, \mathbb C^\times) \cong \widehat{C_F^1} \times \mathbb C$
(writing $c = \chi \lvert \cdot \rvert_F^{\sigma(c) + i t(c)}$ with unitary $\chi \in \widehat{C_F^1}$
and real part $\sigma(c) \in \mathbb R$):

1. **Averaging over $F^\times$-orbits (`Lemma 2.2.2.1`, `(2.2.2.1)`, [Paper; Masullo p. 77], and $\Phi_F$, [Paper; Masullo p. 81]).**
   For $f \in \mathcal S(\mathbb A_F)$, $g \in \mathrm{GL}_1(\mathbb A_F)$, and $x \in \mathbb A_F$, set
   $$\Psi_F(f)(g, x) := \sum_{\xi \in F^\times} f\bigl(g(\xi + x)\bigr),
   \qquad
   \Phi_F(f)(g) := \Psi_F(f)(g, 0) = \sum_{\xi \in F^\times} f(g\xi).$$
   By $F^\times$-invariance in $g$, $\Phi_F(f)$ descends to a continuous function on $C_F$.
2. **Global polar hyperplanes (`Definition 2.2.4.4`, [Paper; Masullo p. 91]).** Set
   $$\mathcal S_0(\mathbb A_F) := \bigl\{f \in \mathcal S(\mathbb A_F) : f(0) = 0 \text{ and } \widehat{f}(0) = 0\bigr\},$$
   and let $H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbb A_F))$ denote the Hausdorff continuous
   $F^\times$-coinvariant space induced by $\Phi_F\rvert_{\mathcal S_0(\mathbb A_F)}$.
3. **Fundamental Divisor Exact Sequence (`§1.2.1`, `(1.2.1.1)`, [Paper; Masullo pp. 13–14]).** Inside
   the space $\mathcal S_E(C_F)$ of smooth functions on $C_F$ with super-exponential/Gaussian decay in
   $\log\lvert g \rvert_F$, multiplication by $\lvert \cdot \rvert_F^{1/2}$ embeds the image of
   $\Phi_F(\mathcal S_0(\mathbb A_F))$ into $\mathcal S_E(C_F)$, defining the topological quotient
   $\mathcal H_F$ via
   $$0 \longrightarrow \lvert \cdot \rvert_F^{1/2}\,H_{0,\mathrm{cont}}\bigl(F^\times, \mathcal S_0(\mathbb A_F)\bigr)
   \longrightarrow \mathcal S_E(C_F) \longrightarrow \mathcal H_F \longrightarrow 0.$$
   On each $\chi$-isotypic component ($\chi \in \widehat{C_F^1}$), the Mellin transform centered at
   $\frac{1}{2}$ maps this exact sequence to (`§1.2.1`, [Paper; Masullo p. 13]):
   $$0 \longrightarrow \Lambda\bigl(s + \tfrac{1}{2}, \chi\bigr)\,\bigl(s^2 - \tfrac{1}{4}\bigr)^{\delta(\chi)}\mathcal O(\mathbb C) \cap AS(\mathbb C)
   \longrightarrow AS(\mathbb C) \longrightarrow \prod_{z :\, \Lambda(z + 1/2, \chi) = 0} \mathbb C^{N(z + 1/2, \chi)} \longrightarrow 0,$$
   where $\delta(\chi) = 1$ if $\chi\rvert_{C_F^1} = \mathbf{1}$ and $0$ otherwise [Paper; Masullo p. 13].

### 14.3.2 Weil's principal value operators, Structure Theorems I–V, and Polar Multiplicities (`Chs. 3–7`)

To relate the global quotient $\mathcal H_F$ to individual finite primes $\mathfrak p$, Masullo restricts
from $\mathbb A_F$ to $S$-adeles $\mathbb A_{F, S}$ for finite sets of places $S \supset S_\infty$
(`Chs. 5–7`, [Paper; Masullo pp. 221–380]):

**Definition 14.2 (Weil principal value operators and polar multiplicities, `§3.4` p. 143, `§5.2` p. 230, `§5.3` pp. 240, 264, `§7.1` p. 324).**

1. **Weil's Identity (`Theorem 3.4.1.1`, `(3.4.1.6)`, [Paper; Masullo p. 143]) and local transition operators $PV_v$ (`§5.3`, [Paper; Masullo pp. 240, 264]).**
   At an unramified non-Archimedean place $v$ with uniformizer $\pi_v$ and residue cardinality
   $q_v = \lvert \mathcal O_{F_v} / (\pi_v) \rvert$, the difference operator
   $(PV_v f_v)(x_v) := f_v(x_v) - f_v(\pi_v^{-1} x_v)$ multiplies the local Tate zeta integral by
   $(1 - \chi_v(\pi_v) q_v^{-s}) = L_v(s, \chi_v)^{-1}$, stripping the local Euler factor $L_v(s, \chi_v)$
   from $\Lambda(s, \chi)$ when passing from $S \cup \{v\}$ down to $S$ (`Structure Theorems I–V`,
   `Theorem 5.2.1.1` p. 230 through `Ch. 6` p. 296) [Paper; Masullo pp. 230–298].
2. **Polar Multiplicities (`Theorem 7.1.3.2`, [Paper; Masullo p. 324], summarized as `Theorem 1.7.1.1`, [Paper; Masullo p. 35]).**
   For a finite set of places $S \supset S_\infty$, the $S$-incomplete reciprocal Euler product
   $\prod_{v \in S} L_v(s, \chi_v)^{-1}$ (or rather the $S$-local zeta meromorphic family) has poles on
   vertical lines controlled as follows:
   - At any finite place $v \in S_f$, the poles of $L_v(s, \chi_v) = (1 - \chi_v(\pi_v) q_v^{-s})^{-1}$
     lie on $\Re s = 0$ spaced vertically by $\frac{2\pi i}{\log q_v}$. Because **$\log p_1$ and $\log p_2$
     are $\mathbb Q$-linearly independent for distinct rational primes $p_1 \neq p_2$**, at most
     $[F : \mathbb Q]$ finite places $v \in S_f$ (those lying above the **same** rational prime $p$!)
     can ever share a pole at the same non-central point $s_0 \neq 0$, bounding the combined finite-place
     polar multiplicity at any point by $[F : \mathbb Q]$ (and including $S_\infty$ at $s_0 = 0$, below
     $2[F : \mathbb Q]$) [Paper; Masullo pp. 35, 324]!
   - This bound is why Masullo imposes the **Sobolev regularity threshold $s \ge 2[F : \mathbb Q]$** in
     Chapters 10–12 (`Theorem 10.3.1.1` p. 448, `Theorem 12.5.1.1` p. 519, and `§14.1` p. 533): an
     $(m - 1)$-st derivative functional $\delta^{(m-1)}$ on $\mathbb R$ belongs to standard $H^{-\sigma}(\mathbb R)$
     for $\sigma > m - \frac{1}{2}$, i.e., in Masullo's doubled parameter $W^{-s,2}$ ($s = 2\sigma$)
     whenever **$s > 2m - 1$**, so choosing $s \ge 2[F : \mathbb Q]$ accommodates all non-central local
     polar derivatives up to order $[F : \mathbb Q]$!

### 14.3.3 Strip-weighted Hardy–Sobolev spaces $W_I^{s,2}(C_F)$ and Spectral Markushevich Bases (`Chs. 9–10`)

**Definition 14.3 (Hardy–Sobolev spaces and spectral bases, `§1.1.3` pp. 11–12, `Def. 9.1.1.1` p. 396, `§9.2` pp. 403–418, `§10.2` pp. 438–447).**
Let $I = [a, b] \subset \mathbb R$ be a compact interval (most importantly the critical line $I = \{0\}$
when $a = b = 0$, or the symmetric strip $I = [-\alpha, \alpha]$ for $\alpha > 0$), and let $s \ge 0$:

1. **Hardy–Sobolev norm on $C_F$ (`§1.1.3`, [Paper; Masullo pp. 11–12], and `§9.2`, [Paper; Masullo pp. 403–414]).**
   Define $W_I^{s,2}(C_F)$ (written $W_I^s(C_F)$ in Chapter 9) as the completion of smooth rapidly
   decaying functions under the weighted Sobolev norm coupled to $\log\lvert g \rvert_F$ (and
   vertical derivatives along $\widehat{C_F^1}$, weighted by $w$ in `Def. 9.1.1.1`, p. 396): on each
   fixed $\chi$-isotypic sector ($\chi \in \widehat{C_F^1}$, identifying $C_F / C_F^1 \cong \mathbb R_{>0}$),
   its norm has the shape [Paper; Masullo pp. 11–12]
   $$\lVert \phi \rVert_{s, I}
   \;:=\; \left(\int_{C_F} \lvert \phi(g) \rvert^2\,\max\bigl\{\lvert g \rvert_F^{2a},\, \lvert g \rvert_F^{2b}\bigr\}\,\bigl(1 + \lvert \log\lvert g \rvert_F \rvert^2\bigr)^{s/2}\,d\mu(g)\right)^{1/2}$$
   (defined on Mellin transforms via Paley–Wiener conditions on the strip $a < \Re z < b$ with $H^{s/2}$
   boundary traces on $\Re z = a$ and $\Re z = b$ in `Theorem 9.2.1.2` p. 404 and `§9.2.2` p. 411; in
   `Proposition 9.2.1.8` `(9.2.1.28)` on p. 409, Masullo pairs $W_I^s(\mathbb R_{>0}) \times W_I^{-s}(\mathbb R_{>0})$
   by inverting the weight $w_{I,s}^{-1}$ without negating $I$).
   Completing the Fundamental Divisor Exact Sequence in this topology produces the Hilbert/Banach
   quotient $W_I^{s,2}\mathcal H_F$ (and character fibers $W_I^{s,2}\mathcal H_F(\chi)$) (`§10.1`,
   [Paper; Masullo pp. 433–437]).
2. **Spectral Markushevich basis (`Proposition 10.2.1.3` p. 443, `Terminology 10.2.1.2` p. 444, `Theorem 10.2.2.1` p. 446).**
   For each character zero $c = \chi \lvert \cdot \rvert_F^{\sigma(c) + i t(c)} \in \Omega(C_F)$ of
   $\Lambda(z, \chi)$ whose real part satisfies $\sigma(c) \in \frac{1}{2} + I$ (i.e.
   $\sigma(c) - \frac{1}{2} \in I$), and each integer $0 \le m < N_s(c)$ (where
   $N_s(c) = \min\bigl\{N(c),\ \lfloor (s - 1)/2 \rfloor + 1\bigr\}$ at `(10.3.1.4)` on `p. 448` is the
   truncated spectral multiplicity allowed by Sobolev parameter $s > 2m + 1$), the dual space $(W_I^{s,2}\mathcal H_F)'$
   contains the generalized eigenfunctional
   $$\eta_{c, m}(g) := \chi(g)\,\lvert g \rvert_F^{\sigma(c) - 1/2 + i t(c)}\,\bigl(\log\lvert g \rvert_F\bigr)^m,$$
   paired with Mellin Taylor-coefficient functionals $\psi_{c, m}$ evaluating derivatives of
   $\mathcal M(\phi) / \Lambda(\cdot + \frac{1}{2}, \chi)$ at $z = \sigma(c) - \frac{1}{2} + i t(c)$
   (`§10.2`, [Paper; Masullo pp. 443–447]).

### 14.3.4 Shell stratification, diagonal smoothening, Main Theorem 12.5.1.1, and placeholder Chapter 13 (`Chs. 11–13`)

**Definition 14.4 (Shell partition, $H$-indentations, and Main Theorem 12.5.1.1, `§11.3.1` pp. 492–494, `§12.1–12.2` pp. 498–513, `§12.5` pp. 519–520, `§13.3` pp. 521–522).**

1. **Divisorial shell stratification (`§11.3.1`, [Paper; Masullo pp. 492–494]).** Masullo partitions
   the non-Archimedean ideles according to the finite set $P_k$ of places where $\lvert g_v \rvert_v \neq 1$
   ("divisorial shells" $\alpha_k = \mathbf{1}_{\mathrm{GL}_1(\mathbb A_F)_{P_k}}$), expressing the
   quotient projection kernel as an alternating inclusion–exclusion sum over prime-power shells (`Ch. 11`)
   plus an $S$-local remainder (`Ch. 12`).
2. **Idelic Lebesgue differentiation and $H$-indentations (`Def. 12.1.1.1` p. 498, `Def. 12.2.1.3` p. 506).**
   Because individual shell kernels have jump discontinuities along norm spheres $\lvert g \rvert_F = N(\mathfrak p)^k$,
   Masullo restricts to test functions $\varphi \in D(C_F)$ satisfying **pointwise vanishing along the
   unit-norm subgroup** $\varphi(C_F^1) = 0$ (meaning $\varphi\rvert_{C_F^1} \equiv 0$, i.e. radially
   $\varphi(1) = 0$, killing the singular term $\varphi(1)\log(\lambda\lambda')$ in `(12.4.1.3)` on
   p. 514; see `Theorem 12.5.1.1`, p. 519) and defines diagonal traces by excising small neighborhoods
   ("$H$-indentations") around the
   diagonal before letting the indentation shrink (`§12.1–12.2`, [Paper; Masullo pp. 498–513]; note
   that `§12.3`, *"Putting the pieces together: global to $S$-local deconstruction of the geometric
   kernel"*, is an empty heading on **p. 514** with footnote 1 *"Include section"*!).
3. **The Main Trace Formula (`Theorem 12.5.1.1`, [Paper; Masullo pp. 519–520]).** Let $F$ be a number
   field, let $\varphi \in D(C_F)$ be a smooth compactly supported test function satisfying
   $\varphi(C_F^1) = 0$, let $I = [-\alpha, \alpha] \subset \mathbb R$ ($\alpha \ge 0$), and let
   $s \ge 2[F : \mathbb Q]$. Masullo states (`pp. 519–520`) that $A(\varphi)$ acting on
   $W_I^{s,2}\mathcal H_F$ defines a trace whose **spectral side** (summing over
   $\Omega(C_F)_I := \{c \in \Omega(C_F) : \sigma(c) \in \frac{1}{2} + I\}$) equals an **$\alpha$-independent
   geometric side** built from archimedean local Weil distributions $W_v(\varphi)$ ($v \mid \infty$)
   and non-Archimedean prime-power sums $-\sum_{\mathfrak p}\sum_{n \neq 0} \log N(\mathfrak p)\,N(\mathfrak p)^{-\lvert n \rvert / 2}\dots$
   [Paper; Masullo pp. 519–520]!
4. **Placeholder Chapter 13 (`Theorem 13.3.1.1` and `Theorem 13.3.1.2`, [Paper; Masullo pp. 521–522]).**
   Chapter 13 occupies only two pages (`pp. 521–522`): `§13.1` and `§13.2` are one-line headings;
   `Theorem 13.3.1.1` (`p. 522`, carrying footnote 1 *"Correct statement."*) restates `Theorem 12.5.1.1` with multiplicity
   $N_{\mathrm{spec}}(c) = \min\{N(c), [F : \mathbb Q]\}$; the line *"Upon combining Theorem 13.3.1.1
   and Theorem ??, we obtain the following:"* leads to an empty **`Theorem 13.3.1.2 (Divisor of
   $L(s, \chi)$)`** carrying footnote 2 *"Insert statement"* and footnote 3 *"State and prove the Main
   Theorems, also explaining how to deduce them by approximation $\varphi \to e^{-s\lvert\log(t)\rvert}$
   as $\operatorname{Re}(s) > 1$"* [Paper; Masullo p. 522].

---

## 14.4 Lemmas, proof architecture, and anatomy of the Chapter 10 spectral gap

Let us now examine the three genuine mathematical mechanisms inside Masullo's manuscript — and then
dissect with surgical precision **where the proof breaks in Chapter 10 and why Pei's critical-line
window argument does not rescue the positive-width strip $I = [-\alpha, \alpha]$**.

### 14.4.1 Why $a = \frac{1}{2}$ is forced on the geometric side (`§1.2.3` p. 16 and `§12.4.1` pp. 517–518)

In Chapter 5 of this book, we saw that Alpöge's archive produces the critical exponent $\frac{1}{2}$
by choosing chain length $m \asymp \sqrt{x}$ to balance $x/m + m$. Where does $\frac{1}{2}$ come from
in Masullo's route?

Look at Masullo's $S$-local Connes–Meyer trace calculation (`§1.2.3`, [Paper; Masullo p. 16], and
`§12.4.1`, `(12.4.1.17)`, [Paper; Masullo pp. 517–518], building on `[Connes1999]` and `[Meyer2005]`)
[Expository]: suppose one had tried to embed $\Phi_F(\mathcal S_0(\mathbb A_F))$ into $\mathcal S_E(C_F)$
with a general power $\lvert \cdot \rvert_F^a$ ($a \in \mathbb R$) instead of $\lvert \cdot \rvert_F^{1/2}$!
On a finite set of places $S \supset S_\infty$, the $S$-local integral kernel formed from pairing a
Schwartz function $f_S(x)$ against its $S$-Fourier transform $\widehat{f}_S(y)$ along multiplicative
Haar measure $d\mu_S(x) = \lvert x \rvert_{F, S}^{-1}\,d\nu_S(x)$ ($d\nu_S$ = additive Haar measure on
$\mathbb A_{F, S}$) carries the prefactor $\lvert x \rvert_{F, S}^a \lvert y \rvert_{F, S}^a$. When
one restricts that kernel to the **diagonal $x = y$** to compute its trace against $d\mu_S(x)$, the
measure becomes:
$$\lvert x \rvert_{F, S}^a \cdot \lvert x \rvert_{F, S}^a \, d\mu_S(x)
\;=\; \lvert x \rvert_{F, S}^{2a - 1}\,d\nu_S(x)!$$
Look at the exponent $2a - 1$: **if and only if $a = \frac{1}{2}$** does $\lvert x \rvert_{F, S}^{2a - 1} = 1$,
turning multiplicative Haar measure $d\mu_S(x)$ into **exact additive Haar measure $d\nu_S(x)$**, on
which additive Fourier/Plancherel inversion ($\int f_S \overline{g_S}\,d\nu_S = \int \widehat{f}_S \overline{\widehat{g}_S}\,d\nu_S$)
holds! Any other shift $a \neq \frac{1}{2}$ inserts a singular or growing power $\lvert x \rvert_{F, S}^{2a - 1}$
that destroys additive Fourier duality at $0$ and $\infty$ [Paper; Masullo pp. 16, 517–518]!

### 14.4.2 Poisson summation with jumps and vanishing of unramified orbital traces (`Prop. B.4.1.2` p. 608 & `Thm. 11.3.2.1` p. 495)

**Lemma 14.1 (Why unramified primes outside the support of $\varphi$ vanish on the geometric side, `Proposition B.4.1.2` p. 608 and `Theorem 11.3.2.1` p. 495).**
*Let $\varphi \in D(C_F)$ have compact support on $C_F$, so there exists $R > 1$ such that
$\varphi(g) = 0$ whenever $\lvert g \rvert_F \notin [R^{-1}, R]$. For any prime ideal $\mathfrak p$ of
$\mathcal O_F$ with norm $N(\mathfrak p) > R$ (and unramified for $\varphi$), the classical prime-power
explicit-formula contribution of $\mathfrak p$ to $\varphi$ is identically zero:*
$$-\log N(\mathfrak p) \sum_{k \in \mathbb Z \setminus \{0\}} N(\mathfrak p)^{-\lvert k \rvert / 2}\,\varphi_{\chi}(\mathfrak p^k) \;=\; 0.$$
[Expository] / [Paper; Masullo pp. 495, 608]

*Proof.* Since $N(\mathfrak p) > R > 1$, for every nonzero integer $k \in \mathbb Z \setminus \{0\}$
the idele norm of $\mathfrak p^k$ satisfies either $\lvert \mathfrak p^k \rvert_F = N(\mathfrak p)^{-k} < R^{-1}$
($k \ge 1$) or $\lvert \mathfrak p^k \rvert_F = N(\mathfrak p)^{\lvert k \rvert} > R$ ($k \le -1$),
lying strictly outside the compact norm support $[R^{-1}, R]$ of $\varphi$! On the spectral/orbital
side (`Proposition B.4.1.2`, p. 608, and `Theorem 11.2.2.1` / `11.3.2.1`, pp. 490, 495), Masullo
interprets this vanishing via the periodic Schauder expansion over the local Euler poles
$s_{m, \mathfrak p} = \frac{2\pi i m}{\log N(\mathfrak p)}$ (just as in our toy example of Section
14.2.1 Part B), aiming to reduce the infinite product of primes to the finite set $S$ of places where
$N(\mathfrak p) \le R$ or $\varphi$ ramifies (`pp. 495–496, 520`). $\square$

*(Audit caution on `Theorem 11.3.2.1`, `[Open]`.)* While Lemma 14.1 is elementary for a fixed smooth
compactly supported $\varphi$, Masullo's Chapter 11 applies it after multiplying kernels by sharp
divisorial shell indicators $\alpha_k$ and taking indentation limits; in `mccorvie/riemann-masullo`
issue `#1358` (and the Refine audit report), Yi Cao noted two shell-cutoff and indentation steps on
**pp. 495–496** where discontinuities created by the shell indicator must be tracked separately before
quoting smooth Poisson vanishing `[Community]` `[Open]`.

### 14.4.3 Surgical anatomy of the Chapter 10 gap, Pei's $I = \{0\}$ window note, and why $I = [-\alpha, \alpha]$ remains `[Open]`

We can now state with complete mathematical precision **what goes wrong in Chapter 10**, **what Yan Ru
Pei's Zenodo note (`doi:10.5281/zenodo.24409811`) proposes for $I = \{0\}$**, and **why the strip case
$I = [-\alpha, \alpha]$ ($\alpha > 0$) needed for GRH remains open**!

**Proposition 14.2 (Anatomy of the spectral nuclearity step in Chapter 10: line $I = \{0\}$ versus strip $I = [-\alpha, \alpha]$).**

1. **Where Masullo's proof breaks (`p. 444`, `p. 451`, `p. 463`).** *In `Theorem 10.3.1.1` ([Paper;
   Masullo pp. 448–452], $0$-line case $I = \{0\}$) and `§10.4.2` ([Paper; Masullo pp. 462–464], strip
   case $I = [-\alpha, \alpha]$), Masullo expands the transpose action $A(\varphi)^t$ on
   $(W_I^{s,2}\mathcal H_F)'$ term by term in the individual zero-mode Markushevich pairs
   $(\eta_{c, m}, \psi_{c, m})$:*
   $$A(\varphi)^t \;=\; \sum_{c \in \Omega(C_F)_I} \sum_{m = 0}^{N_s(c) - 1} \psi_{c, m} \otimes A(\varphi)^t(\eta_{c, m}).$$
   *To prove nuclearity (projective tensor-product convergence $\sum \lVert \psi_{c, m} \rVert \cdot \lVert A(\varphi)^t \eta_{c, m} \rVert < \infty$)
   on **p. 451 after `(10.3.1.18)`** (and **p. 463 at `(10.4.2.24)`**, followed by footnote 8 on
   **p. 464**: "Return here and complete proof"), he invokes `Terminology 10.2.1.2(2)` (**p. 444**) to
   claim $\lVert \psi_{c, m} \rVert \le C$ uniformly across all zeros $c$. By Section 14.2.3
   ($\lVert \eta_{t_2} \rVert_{-s,2} \cdot \lVert \psi_{t_2} \rVert_{s,2} \ge \frac{\sqrt{s - 3}}{t_2 - t_1}$ for $s > 3$, and $\ge (1 - e^{-2\Delta t})^{-1/2}$ at $s = 2$),
   that uniform bound is **provably false** whenever zeros have arbitrarily small vertical gaps!*
   [Paper; Masullo pp. 444, 451, 463–464] `[Community]` [Expository]
2. **How Pei's unreviewed window argument bypasses individual biorthogonals on the critical line $I = \{0\}$ (`doi:10.5281/zenodo.24409811`, `[Community]`).**
   *Restrict strictly to the **single line $I = \{0\}$** ($\sigma(c) = \frac{1}{2}$). Under Mellin/Fourier
   duality between $u = \log\lvert g \rvert_F \in \mathbb R$ and real frequency $t \in \mathbb R$, the
   $0$-line Sobolev space $W_{\{0\}}^{s,2}(\mathbb R_{>0})$ is isometrically the **classical Sobolev
   space $H^s(\mathbb R_t)$** ($L^2$ of $s$ derivatives in $t$)! On a unit frequency interval
   $J_n = [n, n + 1] \subset \mathbb R_t$ ($n \in \mathbb Z$), suppose a cluster of $M_n$ critical-line
   zeros $t_{n, 1}, \dots, t_{n, M_n} \in J_n$ ($M_n = O(\log(\lvert n \rvert + 2))$) occurs, however
   closely spaced (or even coalescing!). Although the Lagrange basis functionals $\delta_{t_{n, j}}$
   blow up like $(t_{n, 2} - t_{n, 1})^{-1}$, their $M_n$-dimensional span inside $H^{-s}(J_n)$ has an
   **orthonormal basis** (obtained by Gram–Schmidt on divided differences / Hermite interpolation on
   $J_n$!), and multiplying by a smooth partition of unity $\{\chi_n(t)\}_{n \in \mathbb Z}$ on
   $\mathbb R_t$ allows one to sum trace-class norms **block by block over unit windows $J_n$**, using
   rapid decay $\lvert \widehat{\varphi}(it) \rvert \ll_N (1 + \lvert t \rvert)^{-N}$ and polynomial
   zero-count growth $M_n = O(\log(\lvert n \rvert + 2))$ without ever bounding $\lVert \psi_{t_{n,j}} \rVert$
   individually!* `[Community]` *(Note: Pei's 19-page Zenodo note is AI-assisted and has **not** been
   peer-reviewed by human specialists; it is tagged `[Community]` / `[Open]`.)*
3. **Why the positive-width strip $I = [-\alpha, \alpha]$ ($\alpha > 0$) required by Theorem 12.5.1.1 is NOT repaired (`[Open]`).**
   *First, knowing nuclearity for $I = \{0\}$ alone tells us **nothing** about whether off-line zeros
   exist — just as Connes's critical-line trace formula `[Connes1999]` is unconditional on $I = \{0\}$
   without proving RH! Second, to deduce GRH via Section 14.2.2, Theorem 12.5.1.1 **must** hold on
   positive-width strips $I = [-\alpha, \alpha]$ ($\alpha > 0$). Why does the $I = \{0\}$ Fourier
   partition-of-unity trick fail on $I = [-\alpha, \alpha]$?* [Expository] `[Open]`
   - *On $I = \{0\}$, $z = it$ is purely imaginary, and the Fourier transform converts spatial weight
     $(1 + u^2)^{s/2}$ into a **local differential norm on $\mathbb R_t$** where smooth cutoffs
     $\chi_n(t)$ act boundedly!*
   - *On $I = [-\alpha, \alpha]$ ($\alpha > 0$), functions in $W_{[-\alpha, \alpha]}^{s,2}$ have Mellin
     transforms **holomorphic across the open strip $-\alpha < \Re z < \alpha$** (`Theorem 9.2.1.2`,
     p. 404). You **cannot** multiply a holomorphic function on a strip $-\alpha < \Re z < \alpha$ by a
     compactly supported smooth bump $\chi_n(\Im z)$ without **destroying holomorphy** ($\bar\partial \neq 0$)!*
   - *Equivalently, in spatial coordinates $u = \log\lvert g \rvert_F$, modes $\eta_{\sigma + it}(u) = e^{(\sigma + it)u}$
     at different real parts $\sigma \in [-\alpha, \alpha]$ grow exponentially at opposite ends $u \to \pm\infty$,
     and because the Hardy–Sobolev quotient $W_I^{s,2}\mathcal H_F$ divides out the **non-orthogonal
     global subspace $\overline{\lvert \cdot \rvert_F^{1/2}\Phi_F(\mathcal S_0(\mathbb A_F))}$**, the
     projection onto a vertical block $[n, n+1] \times [-\alpha, \alpha]$ in the quotient norm couples
     all heights $n$ together through the global divisor relation $L(z + \frac{1}{2}, \chi)$! Whether
     $A(\varphi)$ is nuclear on $W_{[-\alpha, \alpha]}^{s,2}\mathcal H_F$ — and, even more crucially,
     whether its trace equals an $\alpha$-independent geometric side without picking up Cauchy residues
     from hypothetical zeros outside $\frac{1}{2} + I$ — remains completely `[Open]`.*

Look how transparently Proposition 14.2 exposes the heart of the problem! Even if one proved abstractly
(say by lidskii/Fredholm determinant theory on Bergman/Hardy spaces of strips; cf. `leecrossley`'s
partial comment on `mccorvie/riemann-masullo` issue `#1169` `[Community]` `[Open]`) that $A(\varphi)$
were trace-class on $W_{[-\alpha, \alpha]}^{s,2}\mathcal H_F$ with trace $\sum_{\lvert\Re\rho - 1/2\rvert \le \alpha} \widehat{\varphi}(\rho - \frac{1}{2})$,
**any** valid calculation of the geometric side in $W_{[-\alpha, \alpha]}^{s,2}$ must confront the
question raised by `AVBlom` (`#587`) and Tim Gehrunger on Lean Zulip (`chapters/02-the-story-so-far.md`
`[Community]`): *for classical Weil explicit formulas (`Theorem B.4.4.7`, p. 623), the geometric side
equals the sum over **all** nontrivial zeros in $0 < \Re \rho < 1$; how could the exact same geometric
expression equal the sum restricted to $\lvert \Re \rho - \frac{1}{2}\rvert \le \alpha$ unless one had
already ruled out zeros in $\alpha < \lvert \Re \rho - \frac{1}{2}\rvert < \frac{1}{2}$?*

In Masullo's architecture, that exclusion is supposed to happen inside **Chapters 5–7 and 11–12** —
specifically, in claiming that the periodic prime-shell expansions (`Chs. 7, 11`) span the **entire**
$I$-completed quotient $W_I^{s,2}\mathcal H_F$ (`Structure Theorems I–V` and `§12.3`) so that no
off-strip residue slips between the spectral quotient and the geometric shells. And as we see next, it
is right inside Chapter 5 (`Theorem 5.2.1.1`) and Chapter 12 (`§12.3`) that the manuscript's geometric
scaffolding is currently incomplete or disputed `[Community]` `[Open]`.

---

## 14.5 Remarks, formalization status, and chapter map

### 14.5.1 Chapter 14 of Masullo's draft: zero multiplicities and why $\mathbb F_q(X)$ fails (`pp. 523–536`)

Before leaving Masullo's manuscript, two sections of **Chapter 14 ("Complements", pp. 523–536)** deserve
special attention from readers of this textbook:

1. **Zero-multiplicity predictions (`§14.1`, [Paper; Masullo pp. 524–533], and `Expectation 1.7.1`, p. 38):**
   Because the Sobolev degree $s \ge 2[F : \mathbb Q]$ truncates spectral Jordan blocks at
   $N_{\mathrm{spec}}(c) = \min\{N(c), [F : \mathbb Q]\}$ in `Theorem 13.3.1.1` (`p. 522`), Masullo
   notes that if his trace formula held for every test function, matching residue orders would force
   **every non-central zero $\rho \neq \frac{1}{2}$ of $L(s, \chi)$ to have multiplicity
   $N(\rho) \le [F : \mathbb Q]$** (in particular, **all zeros of $\zeta(s)$ and Dirichlet $L(s, \chi)$
   away from $s = \frac{1}{2}$ would have to be simple**, $N(\rho) \le [\mathbb Q : \mathbb Q] = 1$!)
   [Paper; Masullo pp. 38, 528–533]! Intriguingly, on **pp. 531–532** (`Proposition 14.1.2.5` and
   `Remark 14.1.2.6`, followed by `Remark 14.1.2.7` on Elkies's rank $\ge 17$ curve), Masullo
   checks this against CM Mordell elliptic curves $E_d : y^2 = x^3 + d$ over $\mathbb Q$ (whose
   $L$-function equals the Hecke $L$-function of a Grossencharacter over $F = \mathbb Q(\sqrt{-3})$,
   $[F : \mathbb Q] = 2$): since Quer constructed Mordell curves of algebraic rank $12$ (and Elkies of
   rank $\ge 17$, so analytic order $\ge 12 > 2 = [F : \mathbb Q]$ under BSD at the **central point**!),
   Masullo points out that central zeros at $s = \frac{1}{2}$ genuinely violate $N(\rho) \le [F : \mathbb Q]$
   and require separate treatment at $c = \chi\lvert \cdot \rvert_F^{1/2}$ [Paper; Masullo pp. 531–532]!
2. **Why global function fields $\mathbb F_q(X)$ break Masullo's trace method (`§14.2`, [Paper; Masullo pp. 534–536]):**
   Over a smooth projective curve $X / \mathbb F_q$ of genus $g$, **every** closed point $x \in \lvert X \rvert$
   has residue cardinality $q^{\deg x}$, a power of the **same** integer $q$! Consequently, all local
   Euler factors $(1 - \chi_x(\pi_x) q^{-s \deg x})^{-1}$ share infinitely many common poles along the
   single vertical lattice $\frac{2\pi i}{\log q}\mathbb Z$, **destroying the Polar Multiplicities
   Theorem (`Theorem 7.1.3.2`, p. 324)** (which relied on $\mathbb Q$-linear independence of $\log p$
   across distinct rational primes!) and invalidating the orbital trace bound `Theorem 11.2.2.1` [Paper;
   Masullo pp. 35, 534–535]! Moreover, maximal curves over $\mathbb F_{q^2}$ attain Frobenius
   eigenvalue multiplicity $2g$, exceeding gonality $g + 1 = [F : \mathbb F_{q^2}(t)]$ [Paper; Masullo
   pp. 39, 535]. We will return to this striking contrast with Stepanov's method in Chapter 15!

### 14.5.2 Status of the `mccorvie/riemann-masullo` Lean 4 formalization (`2026-11-22`)

Under Ryan McCorvie's coordination (`mccorvie/riemann-masullo`, pinned to Lean `v4.36.0` / Mathlib
`v4.36.0`), an open community of ~30 contributors and coding agents is formalizing Masullo's draft
from the ground up in three waves (`sources/SOURCES.md`, Part I `§3` and entry `V13`, re-checked `2026-11-22 04:35 UTC`)
`[Community]`:

- **Scale achieved so far:** Roughly **4,700 theorems and 820 definitions** stated in Lean, with
  **~3,950 theorems proved** across **~1,360 merged pull requests**, alongside a page-indexed
  `ERRATA.md` of **~200 entries** (~45 statements false as printed, ~135 imprecise or wrongly
  justified, ~16 placeholders/missing pieces, and 9 reader reports on later chapters) `[Community]`.
- **Wave 1 (Appendices A, C, D; Chapters 2–4 and 9):** Fully stated in Lean and mostly proved (standard
  adelic/idelic background, locally convex spaces, Schwartz–Bruhat functions, periodic Schauder bases
  on $\mathbb R_{>0}$-modulated groups, and Hardy–Sobolev spaces $W_I^s(G)$) `[Community]`.
- **Wave 2 (Chapters 5–7 and Appendix B):** Currently being stated and tested; notably, the project's
  README reports (`2026-11-21/22`) that **the printed proof of Structure Theorem I (`Theorem 5.2.1.1`,
  p. 230, governing the locally convex topology of adelic $\theta$-spaces) does not work as written**
  and whether the theorem itself holds is currently under test in Lean, while the local terms and
  measure normalizations of the idelic explicit formulas in `§B.4` (`pp. 606–625`, cf. issue `#587`
  noting a missing $\mu_1(C_F^1)$ factor on $\mathbb Q(i)$ and $\mathbb Q(\sqrt{-3})$) require
  recomputation `[Community]` `[Open]`.
- **Wave 3 (Chapters 10–12, the trace formula) and Chapter 13:** Seeded as section issues in
  `mccorvie/riemann-masullo`, with Lean statements in progress in dependency order and proofs not yet
  started `[Community]` `[Open]`.

### 14.5.3 Consolidated map of Masullo's *The Music of the Primes*

| Chapter / Appendix | Pages | Core mathematical content | Current status (`2026-11-22`) |
|---|---|---|---|
| Ch. 1 Introduction | pp. 11–56 | Informal overview (`pp. 9–10` Index of Symbols): Hardy–Sobolev spaces (`§1.1.3` p. 11), Fundamental Divisor Exact Sequence (`§1.2.1` p. 13), $\mathbb R_{>0}/\gamma^{\mathbb Z}$ toy model (`§1.2.8` p. 16), intended test-family GRH deduction (`§1.4.2–1.4.5` pp. 28–30), avoidance of Weil positivity (`§1.4.6` p. 30), letter to Sarnak (`§1.7` pp. 33–45). | `[Paper; Masullo pp. 11–56]` |
| Ch. 2 Adelic $\theta$-functions | pp. 57–116 | Orbit-averaging operator $\Psi_F(f)(g, x)$ and $\Phi_F(f)(g) = \sum_{\xi \in F^\times} f(g\xi)$ (`Lemma 2.2.2.1` p. 77), super-polynomial decay (`Thm. 2.2.3.4` pp. 82–83), global polar hyperplanes $\mathcal S_0(\mathbb A_F)$ (`Def. 2.2.4.4` p. 91). | Wave 1 stated & mostly proved in `mccorvie/riemann-masullo` `[Community]` |
| Ch. 3 Idelic Zeta Functions | pp. 117–154 | Tate's thesis, meromorphic continuation and functional equation (`Thm. 3.3.1.1`), eigendistributions and Weil's Identity (`Thm. 3.4.1.1` p. 143). | Wave 1 stated & mostly proved `[Community]` |
| Ch. 4 Periodic Schauder Bases | pp. 155–220 | Exponential Schauder bases on $\mathbb R_{>0}$-modulated locally compact abelian groups and periodic quotients. | Wave 1 stated & mostly proved `[Community]` |
| Chs. 5–6 Spaces of $\theta$/$Z$-functions & Local–Global | pp. 221–310 | Structure Theorems I–V (`Thm. 5.2.1.1` p. 230 to `Ch. 6` p. 296), Weil principal value operators $PV_v$ (`§5.3` pp. 240, 264). | Wave 2 in progress; printed proof of `Thm. 5.2.1.1` reported non-working as written `[Community]` `[Open]` |
| Chs. 7–8 Polar Multiplicities & Orbits | pp. 311–394 | Polar Multiplicities (`Thm. 7.1.3.2` p. 324, using $\mathbb Q$-independence of $\log p$), periodic Schauder bases of $S$-idelic zeta spaces, topological stacks. | `§7.1` stated in Wave 2; `§7.2–7.5` and `Ch. 8` open `[Community]` `[Open]` |
| Ch. 9 Hardy–Sobolev Topologies | pp. 395–432 | Weighted Sobolev spaces $W^{s,2}(G)$ (`Def. 9.1.1.1` p. 396), strip Hardy–Sobolev spaces $W_I^s(G)$ & Paley–Wiener theorems (`Thm. 9.2.1.2` p. 404), duality (`Prop. 9.2.1.8` p. 409), $D(G)$-modules (`§9.3` p. 419). | Wave 1 stated & mostly proved `[Community]` |
| Ch. 10 Trace Formula: Spectral Side | pp. 433–474 | $W_I^{s,2}$ completions of $\mathcal H_F$ (`§10.1` pp. 433–437), Spectral Markushevich Bases (`§10.2` pp. 438–447), **false `Terminology 10.2.1.2(2)` (`p. 444`)**, **public biorthogonal-bound gap on `p. 451` after `(10.3.1.18)` and `p. 463` `(10.4.2.24)`** (fn. 8 `p. 464`). | Pei (`doi:10.5281/zenodo.24409811`) unreviewed $I=\{0\}$ window proposal `[Community]`; **strip case $I=[-\alpha,\alpha]$ unrepaired `[Open]`** |
| Chs. 11–12 Shell Structure & Geometric Side | pp. 475–520 | Divisorial shells $\alpha_k$ (`§11.3.1` p. 492), Orbital Nuclearity & Traces (`Thms. 11.2.2.1`, `11.3.2.1` pp. 490, 495), $H$-indentations (`§12.1–12.2`), **omitted `§12.3` (`p. 514`)**, $S$-local $a = \frac{1}{2}$ Fourier trace (`§12.4` p. 518), **Main `Theorem 12.5.1.1` (`p. 519`)**. | Unverified; issues `#1358` (`pp. 495–496`), `#587` ($\mu_1(C_F^1)$ factor), and omitted `§12.3` `[Open]` |
| Ch. 13 Zeros of Hecke $L$-functions | pp. 521–522 | Two-page placeholder: `Theorem 13.3.1.1` (`p. 522`, fn. 1 *"Correct statement."*) restates trace formula; **`Theorem 13.3.1.2` (`p. 522`, fn. 2 *"Insert statement"*) unwritten** (Loeffler formalized RH from `Thm. 12.5.1.1` `[Community]`). | Unwritten in draft `[Paper; Masullo pp. 521–522]` `[Open]` |
| Ch. 14 Complements, Appendices A–E & Bibliography | pp. 523–940 | Zero-multiplicity bounds & Mordell CM curves (`§14.1` pp. 524–533), **breakdown over $\mathbb F_q(X)$ (`§14.2` pp. 534–536)**, higher rank (`§14.3` p. 536), Appendices A–E (`pp. 537–932`, `App. B` explicit formulas `pp. 587–656`), and Bibliography (`pp. 933–940`). | Apps. A, C, D in Wave 1; App. B in Wave 2 (`§B.4` local normalizations under review) `[Community]` `[Open]` |

**Summary of the chapter.** Starting from Tate's idelic zeta integral `[Tate1967]` on
$C_F = \mathbb A_F^\times / F^\times$ and the polar-free $\mathrm{GL}_1$ orbit sum
$\Phi_F(f)(g) = \sum_{\xi \in F^\times} f(g\xi)$ (`p. 77`), Masullo forms the quotient
$\mathcal H_F = \mathcal S_E(C_F) / \overline{\lvert \cdot \rvert_F^{1/2}\Phi_F(\mathcal S_0(\mathbb A_F))}$
(`§1.2.1` p. 13) whose Mellin spectrum is the zero set of $\Lambda(s, \chi)$, and completes it in
strip-weighted Hardy–Sobolev topologies $W_I^{s,2}(C_F)$ (`Ch. 9`) to filter zeros into strips
$\Re \rho \in \frac{1}{2} + I$ without invoking Weil positivity (`§1.4.6` p. 30) [Paper; Masullo
pp. 11–16, 30, 395–432]. Our hand-worked examples showed why $\lvert \cdot \rvert_F^{1/2}$ is forced
by matching multiplicative to additive Haar measure on the diagonal (`p. 518`), why strip-independence
of `Theorem 12.5.1.1` (`p. 519`, with $\varphi(C_F^1) = 0$) would immediately force GRH via one-sided
test functions $\varphi_{R,\varepsilon,z} \to t^{-z}\mathbf{1}_{t > 1}$ (`pp. 28–30`), and why
`Terminology 10.2.1.2(2)` (`p. 444`) fails with $\lVert \eta_{t_2} \rVert_{-s,2} \cdot \lVert \psi_{t_2} \rVert_{s,2} \ge \frac{\sqrt{s-3}}{t_2 - t_1}$
($s > 3$, giving $26.5$ at $s = 4, \Delta\gamma \approx 0.0377$) on close critical-line zeros — leaving the spectral nuclearity step (`pp. 451, 463`), the omitted
geometric assembly `§12.3` (`p. 514`), and placeholder Chapter 13 (`pp. 521–522`) open in the positive-width
strip case $I = [-\alpha, \alpha]$ `[Open]`. In Chapter 15 we place Alpöge–Claude's Lean proof and
Masullo's trace-formula route side by side across all five structural dimensions!
