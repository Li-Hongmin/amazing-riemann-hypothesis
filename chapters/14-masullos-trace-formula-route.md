# Chapter 14. Masullo's trace-formula route

> **Status tags used in this chapter:** `[Paper; Masullo p. …]` for definitions, statements,
> equations, and author footnotes read directly in Alessandro Maria Masullo's 940-page draft
> *The Music of the Primes* (`sha256 e039d3f6…97bf5`); `[Paper; remark p. …]` for Alpöge's four-page
> note; `[Lean, read]` for cross-references to declarations in Alpöge's archive verified in earlier
> chapters and the specified Mathlib declarations in §14.4.2; `[Community]` for public community
> audits, Zenodo notes, and formalization repositories
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

### 14.4.2 Poisson summation and jumps on the local logarithmic lattice

**Motivation.** The logarithm turns the multiplicative progression of powers of a prime norm
$q$ into the equally spaced grid $(log q)\mathbb Z$. Reading a test function on that grid and
reading its Mellin transform at frequencies spaced by $2\pi/\log q$ are two ways of evaluating
the same periodization. Masullo uses this classical mechanism in Proposition B.4.1.2.
Lemma 14.1 below gives the support cutoff for the arithmetic samples. The question here is
how those samples agree with the frequency calculation, including what a jump does to a
sample. [Paper; Masullo pp. 608–610] [Expository]

**A smooth compactly supported example.** Over $\mathbb Q$ with trivial character, put $a=\log 2$,
$c=3a/2$, and define the radial test by
$$
 B(v)=\begin{cases}\exp(1-1/(1-v^2)),& |v|<1,\\0,& |v|\ge 1,\end{cases}
 \qquad \varphi(t)=B((\log t-c)/a).
$$
Every derivative at $v=\pm1$ vanishes because the exponential tends to zero faster than every
power of $1-v^2$. Thus $\varphi$ is smooth, with support $[\sqrt{2},4\sqrt{2}]$ and
$\varphi(1)=0$. In the norm convention of Lemma 14.1 a uniformizer has norm $p^{-1}$, so
$k\ge 0$ contributes zero. With $j=-k>0$ a nonzero sample requires
$$
 \tfrac12\log 2<j\log p<\tfrac52\log 2
 \qquad\Longleftrightarrow\qquad \sqrt{2}<p^j<4\sqrt{2}.
$$
The endpoints have value zero. The cutoff in Lemma 14.1 can be taken to be $R=4\sqrt{2}$.
Since $5<4\sqrt{2}<6$, the complete list is $2,3,4,5$ (the terms following $4$ at $p=2$,
$3$ at $p=3$ and $5$ at $p=5$ are $8,9,25$). At $2$ and $4$ the bump arguments are
$-1/2$ and $1/2$, giving $e^{-1/3}$ in both cases. Write
$$v_3=\log 3/a-3/2,\qquad v_5=\log 5/a-3/2.$$
The signed contributions in the normalization of Lemma 14.1 are

| $p^j$ | $(p,k)$ | $-\log(p)\,p^{-j/2}\varphi(p^j)$ |
|---|---|---|
| $2$ | $(2,-1)$ | $-a e^{-1/3}/\sqrt{2}$ |
| $3$ | $(3,-1)$ | $-(\log 3)\exp(1-1/(1-v_3^2))/\sqrt{3}$ |
| $4$ | $(2,-2)$ | $-a e^{-1/3}/2$ |
| $5$ | $(5,-1)$ | $-(\log 5)\exp(1-1/(1-v_5^2))/\sqrt{5}$ |

Each is strictly negative. The $p^{-j/2}$ factor comes from the prescribed prime-power
weight. In this one-sided model it can be incorporated into the smooth function
$g(u)=e^{-u/2}\varphi(e^u)$ on the logarithmic axis. This function vanishes for $u\le 0$.
The signed contribution at $p$ is then $-h\sum_{j\in\mathbb Z} g(jh)$ with $h=\log p$.
[Expository]

**Periodization and Fourier conventions.** For a compactly supported function $g$ on
$\mathbb R$ and $h>0$, write
$$
 P_hg(x)=\sum_{j\in\mathbb Z}g(x+jh),\qquad
 \widehat g(\xi)=\int_{\mathbb R} g(u)e^{-2\pi i\xi u}\,du,\qquad
 c_m=\frac1h\int_0^h P_hg(x)e^{-2\pi i m x/h}\,dx .
$$
The first sum is locally finite and reindexing makes it $h$-periodic. The factor $1/h$
comes from the probability measure on a period of the circle. For a function $\psi$
of the multiplicative variable, let $\Phi(s)=\int_0^\infty\psi(t)t^s\,dt/t$. Substituting
$t=e^u$ gives $dt/t=du$ and $\widehat{\psi\circ\exp}(\xi)=\Phi(-2\pi i\xi)$.
[Expository]

**Classical Poisson lemma.** For $g\in C_c^2(\mathbb R)$ and $h>0$, the Fourier series
below converges absolutely and uniformly in $x$, and
$$
 P_hg(x)=\frac1h\sum_{m\in\mathbb Z}\widehat g(m/h)e^{2\pi i m x/h}.
$$

**Proof.** On $[0,h]$ only finitely many translates intersect the support. Integrate
each term, put $u=x+jh$, and use $e^{2\pi i mj}=1$. The intervals tile the line up to
endpoints, so
$$
 h c_m=\sum_{j\in\mathbb Z}\int_{jh}^{(j+1)h}g(u)e^{-2\pi i m u/h}\,du
       =\widehat g(m/h).
$$
For nonzero $\xi$, integrate by parts twice on an interval containing the support in
its interior. Both boundary terms vanish and
$$
 \widehat g(\xi)=\frac{\widehat{g''}(\xi)}{(2\pi i\xi)^2},
 \qquad |\widehat g(\xi)|\le\frac{\lVert g''\rVert_1}{(2\pi|\xi|)^2}.
$$
The zero-frequency term is the integral of $g$. Since $\sum_{m\ne 0}m^{-2}$ converges,
the series with coefficients $c_m$ converges uniformly to a continuous periodic
function. Integrating that series term by term and using orthogonality gives exactly
the coefficients $c_m$. The [circle reconstruction theorem](#14421-fourier-completeness-on-the-circle-and-pointwise-reconstruction)
identifies the two continuous functions pointwise from these coefficients.
This proves the identity. $\square$ [Expository]

At $x=0$ the factor $h$ in the prime contribution cancels the factor $1/h$ in the lemma.
For the bump above, this gives the signed frequency expression
$$
 -h\sum_{j\in\mathbb Z}g(jh)
 =-\sum_{m\in\mathbb Z}\widehat g(m/h)
 =-\sum_{m\in\mathbb Z}\mathcal M(\varphi)(-1/2-2\pi i m/h).
$$
Here $\mathcal M(\varphi)(s)=\int_0^\infty\varphi(t)t^s\,dt/t$. The real shift
$-1/2$ comes from $e^{-u/2}$, the negative imaginary sign from the Fourier convention,
and the outer minus sign from the prime contribution. Absolute convergence also
allows $m\mapsto-m$. For example, at $p=2$ this sum is
$-a e^{-1/3}(1/\sqrt 2+1/2)$. [Expository]

**Correspondence with Mathlib.** At the archive's Mathlib pin
`0df444a360eaa60ab8c11dca51a86af692955474`,
`Real.fourierCoeff_tsum_comp_add` (lines 52–100) identifies the coefficient at unit
period. Its hypothesis is summability of the sup norms of the translates on every
compact set. The proof bounds multiplication by the unit-modulus Fourier character,
exchanges sum and integral, and rejoins the translated intervals using integrability
on the line. `Real.tsum_eq_tsum_fourier` (lines 103–117) assumes in addition summability
of the sampled transforms as an unordered family. It lifts the continuous
periodization to the circle, applies the coefficient identity, and evaluates
`has_pointwise_sum_fourier_series_of_summable`. The latter uses the circle's
$L^2$ Fourier basis and uniform convergence for summable coefficients. In our proof
local finiteness supplies the first hypothesis and the derivative estimate supplies
the second. [Section 14.4.2.1](#14421-fourier-completeness-on-the-circle-and-pointwise-reconstruction) gives the production proof for the circle basis.
Applying the unit-period statement to $y\mapsto g(hy)$ at $x/h$
recovers the factor $1/h$ by change of variables. These are read classical
declarations [Lean, read]. The imported circle $L^2$ completeness is read below [Lean, read]. General summation and
integration machinery remain named library inputs [Lean]. The chapter
has no corresponding Alpöge–Claude P node.
[Mathlib, `PoissonSummation.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/PoissonSummation.lean#L52-L117)
· [Mathlib, `AddCircle.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L480-L507)

**Non-smooth boundary values.** For a compactly supported piecewise $C^1$ function $g$
with finitely many breakpoints and finite one-sided limits of the function and its
derivative, $P_hg$ is piecewise $C^1$ on the circle. Finite periodization still gives
$c_m=h^{-1}\widehat g(m/h)$, since changing finitely many point values leaves the
integrals unchanged. The classical pointwise Fourier convergence theorem gives
$$
 \lim_{M\to\infty}\sum_{|m|\le M}c_m e^{2\pi i m x/h}
 =\frac{P_hg(x-)+P_hg(x+)}{2}
 =\sum_{j\in\mathbb Z}\frac{g((x+jh)-)+g((x+jh)+)}{2}.
$$
This is the classical literature input used in Masullo's proof at (B.4.1.11)–(B.4.1.13).
For $\theta>1$, take $h=\log\theta$ and
$g(u)=e^{\lambda u/h}\psi(e^u)$, where $e^\lambda=\chi(\theta)$.
At $x=0$ the one-sided values acquire the factor $\chi(\theta)^j$ and
$\widehat g(m/h)=\Phi((\lambda-2\pi i m)/h)$. Reversing the symmetric index
$m\mapsto-m$ gives the plus sign in (B.4.1.7). This calculation treats the positive
logarithmic period and compact support. The jump theorem here is a literature
citation. [Paper; Masullo pp. 608–610]
[Masullo, pp. 608–610](https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=608)

Masullo's own example (B.4.1.8)–(B.4.1.9) takes $\psi=\mathbf{1}_{[1,2]}$,
$h=\log 2$, and trivial character. The only lattice samples with nonzero one-sided
averages are at $1$ and $2$, each with weight $1/2$. Their sum times $h$ is $h$.
On the frequency side $\Phi(s)=(2^s-1)/s$ takes the value $h$ at zero and vanishes at
all other points of $2\pi i\mathbb Z/h$. Any assigned values at the two endpoints
give the same Fourier coefficients. This particular frequency series is finite.
In general the piecewise integration by parts bound is only $O(1/|m|)$, and the
jump theorem uses symmetric partial sums. [Paper; Masullo p. 608] [Expository]

For smooth approximations $g_\varepsilon$ tending to $g$ in $L^1$, every fixed
Fourier coefficient converges. An $\varepsilon$-independent summable
majorant of the sampled coefficients would justify passing to the limit in the
whole series. For symmetric partial sums it also suffices to control their tails
uniformly in $\varepsilon$ at the point of evaluation. On the sampling side a common
compact support reduces passage to the limit to finitely many sample values.
For example, take a nonnegative even smooth bump of integral one supported in
$[-1,1]$, and dilate it to $[-\varepsilon,\varepsilon]$ preserving its integral.
In the convolution at a jump, each half of this bump has mass $1/2$. After
rescaling to $[-1,1]$, dominated convergence gives half the left limit and half
the right limit. This sampling
argument gives the limit of the smooth identities in that model. An identification
with the symmetric Fourier limit of $g$ can then use the jump theorem directly.
[Expository]

**Application boundary.** Yi Cao's issue #1358 reports an annihilating cutoff and a
vanishing indentation integral in the printed proof on pp. 495–496. Those concern
the construction of the orbital trace. Applying the scalar formula there would
require a justified reduction to a local periodization and control of the trace
limits. The orbital-trace application of Theorem 11.3.2.1 remains [Open].
[Issue #1358](https://github.com/mccorvie/riemann-masullo/issues/1358) [Community]

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

#### 14.4.2.1 Fourier completeness on the circle and pointwise reconstruction

The coefficient calculation in §14.4.2 gives the same coefficients for
the periodization and its uniformly convergent series. To identify the
two functions, we need the characters to detect every nonzero difference.
Orthonormality alone would detect only the projection onto their closed span.

**An average by hand.** Let $h>0$ and $e_m(x)=\exp(2\pi i m x/h)$ on
$X_h=\mathbb R/h\mathbb Z$. For the polynomial $1+2e_1+e_{-2}$, the
symmetric frequency cutoffs at $0,1,2$ give $1$, $1+2e_1$, and
$1+2e_1+e_{-2}$. Their average is $1+\frac43e_1+\frac13e_{-2}$.
The constant occurs in all three sums, frequency $1$ occurs in two, and
frequency $-2$ occurs in one. The uniform error is $4/3$ by the triangle
inequality with equality at $x=0$. In general, averaging the first $N$
cutoffs multiplies frequency $m$ by $1-|m|/N$ when $|m|<N$ and removes
all other frequencies. This weighting produces a positive kernel.

**Definitions.** Use probability Haar measure $d\mu_h=dx/h$ on one period
and put
$$
 c_m(F)=\int_{X_h}F\,\overline{e_m}\,d\mu_h,\qquad
 S_M F=\sum_{|m|\le M}c_m(F)e_m,\qquad
 \sigma_N F=\frac1N\sum_{M=0}^{N-1}S_M F .
$$
These integrals exist for $F\in L^2(\mu_h)$ by Cauchy–Schwarz and depend
only on its almost-everywhere class. The trigonometric polynomials are
the finite complex linear combinations of the $e_m$.

**Density lemma.** The trigonometric polynomials are dense in $C(X_h)$
in the supremum norm and in $L^2(\mu_h)$ in the norm of that space.

**Proof.** For $N\ge1$ define the Fejér kernel and expand its square:
$$
 K_N(t)=\frac1N\left|\sum_{j=0}^{N-1}e_j(t)\right|^2
       =\sum_{|m|<N}(1-|m|/N)e_m(t).
$$
Indeed, there are $N-|m|$ pairs of indices with difference $m$.
Integration over a period gives $\int e_m\,d\mu_h=0$ for $m\ne0$ by
the exponential antiderivative and gives $1$ for $m=0$. Thus $K_N\ge0$
and $\int K_N\,d\mu_h=1$. The geometric sum gives
$$
 K_N(t)=\frac{\sin^2(\pi Nt/h)}{N\sin^2(\pi t/h)}
 \qquad (t\notin h\mathbb Z),
$$
with value $N$ at the origin of the circle. Translating and reversing
the integration variable in each term of the finite expansion yields
$\sigma_N F(x)=\int K_N(t)F(x-t)\,d\mu_h(t)$.

Given continuous $F$ and $\varepsilon>0$, uniform continuity supplies
$0<\delta<h/2$ such that $|F(x-t)-F(x)|<\varepsilon$ when the
distance of $t$ to $h\mathbb Z$ is less than $\delta$. On the
complement, using a representative in $[-h/2,h/2]$, the geometric
sum formula bounds $K_N$ by $1/(N\sin^2(\pi\delta/h))$. Subtract
$F(x)\int K_N\,d\mu_h$ and split the integral. This gives
$$
 \|\sigma_N F-F\|_\infty
 \le \varepsilon+\frac{2\|F\|_\infty}{N\sin^2(\pi\delta/h)}.
$$
Hence the polynomial averages converge uniformly to $F$.

For the second assertion, approximate an $L^2$ function by simple
functions, using truncation followed by quantization of the real and
imaginary parts. For a measurable set $A$, regularity of circle measure
gives a compact $C\subset A$ and an open $U\supset A$ with
$\mu_h(U\setminus C)<\eta$, taking a Borel representative if needed.
There is a continuous $v$ valued in $[0,1]$ equal to $1$ on $C$ and
$0$ outside $U$. For nonempty $C$ and $X_h\setminus U$ use
$d(x,X_h\setminus U)/(d(x,X_h\setminus U)+d(x,C))$, with $d$ the
circle distance to a set. If either set is empty, the corresponding
constant $0$ or $1$ suffices. Then
$\|\mathbf 1_A-v\|_2^2\le\mu_h(U\setminus C)<\eta$. Finite linear
combinations give continuous approximants to simple functions.
Finally $\|F-P\|_2\le\|F-P\|_\infty$ for continuous $F$ and a
polynomial $P$, by the probability normalization. This transfers
the uniform density to $L^2$. $\square$

**Reconstruction theorem.** If two functions in $L^2(\mu_h)$ have the
same Fourier coefficients, they agree almost everywhere. If both have
continuous representatives, those representatives agree at every
point. In particular, if $F\in C(X_h)$ and $\sum_{m\in\mathbb Z}|c_m(F)|$
is finite, its Fourier series converges absolutely and uniformly to $F$.

**Proof.** Integrating $\overline{e_j}e_k=e_{k-j}$ gives the
orthonormality relations. If $D$ is the difference of two functions
with identical coefficients, it is orthogonal to every polynomial.
For polynomials $P$ tending to $D$ in $L^2$,
$\|D\|_2^2=\langle D-P,D\rangle$ with the convention that the inner
product is conjugate linear in its first slot. Its absolute value is
bounded by $\|D-P\|_2\|D\|_2$. Consequently $D=0$ in $L^2$.
If a continuous representative of $D$ had a nonzero value, continuity
would give an open arc on which its modulus was bounded below by a
positive constant. Every such arc has positive $\mu_h$ measure, which
contradicts zero $L^2$ norm.

In the summable case the bound $\|c_m(F)e_m\|_\infty=|c_m(F)|$ gives
a continuous uniform sum. Integration against each character
commutes with uniform convergence by finiteness of $\mu_h$. By
orthonormality the sum has coefficients $c_m(F)$. Continuous
uniqueness identifies it with $F$ at every point. For §14.4.2 take
$F=P_hg$ and use the coefficient and summability estimates already
proved there. Substitution of $c_m(F)=\widehat g(m/h)/h$ recovers the
stated pointwise identity, including at $x=0$. $\square$

**A sawtooth by hand.** Let $B(x)=x/h-1/2$ for $0<x<h$ and set
$B(0)=1$ on the circle. The mean coefficient is zero. For $m\ne0$ put
$u=x/h$ and integrate by parts:
$$
 \begin{aligned}
 c_m(B)
 &=\int_0^1 (u-\tfrac12)e^{-2\pi i m u}\,du\\
 &=\left[-\frac{(u-\tfrac12)e^{-2\pi i m u}}{2\pi i m}\right]_0^1
   +\frac{1}{2\pi i m}\int_0^1e^{-2\pi i m u}\,du
 =-\frac{1}{2\pi i m}.
 \end{aligned}
$$
Thus $\sum_m|c_m(B)|=\frac1\pi\sum_{m\ge1}1/m=\infty$,
and pairing terms gives
$$
 S_M B(x)=-\frac1\pi\sum_{m=1}^M\frac{\sin(2\pi m x/h)}{m}.
$$
At the seam $x=0$ every partial sum is zero, the average of the two
one-sided limits. For $x$ in any closed subinterval of $(0,h)$,
geometric summation bounds the sums of $e_m(x)$ over every finite
consecutive block by $2/|1-e_1(x)|$, uniformly on the subinterval.
Summation by parts from $m=p$ through $q$ then bounds the exponential
tail with weights $1/m$ by $2/(p|1-e_1(x)|)$: the bound multiplies
$1/q+\sum_{m=p}^{q-1}(1/m-1/(m+1))=1/p$. The sine series
therefore has a continuous limit on each such interval.

To identify that limit, $S_M F$ is the orthogonal projection onto
the span of $\{e_m:|m|\le M\}$. Its $L^2$ error is at most that of
any polynomial in this span, by the Pythagorean identity. Density
gives $\|F-S_M F\|_2\to0$ for every $F\in L^2$. For $B$, the
limit on each closed subinterval of $(0,h)$ consequently agrees
with $B$ there, by uniqueness of the restricted $L^2$ limit and
continuity on the interior. Thus the symmetric sums converge to
$B$ almost everywhere and fail to recover its prescribed value
at $0$. Their everywhere pointwise limit has a jump, so convergence
on the whole circle cannot be uniform. This example also shows why
pointwise convergence of symmetric sums can coexist with divergence
of the series of absolute values.

**Convergence and the pinned proof.** Norm convergence in $L^2$
concerns equivalence classes. Almost-everywhere convergence of an
entire sequence is a pointwise assertion outside a null set and
does not follow from the projection estimate alone. Everywhere
pointwise convergence specifies all values, while uniform convergence
bounds the error simultaneously at all points. The Fejér estimate
gives uniform convergence of the averages for continuous $F$.
The reconstruction theorem gives uniform convergence of the original
Fourier series under the additional absolute summability hypothesis.

The following declaration ranges all refer to the archive manifest's
Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`.
The Fejér proof and sawtooth are textbook arguments [Expository].
The pinned proof uses the following steps.

- `AddCircle.haarAddCircle` (85–90), `fourier` (123–125),
  `fourier_coe_apply` (132–138), `fourierCoeff` (298–299), and
  `fourierCoeff_eq_intervalIntegral` (303–310) give the probability
  measure, positive phase in synthesis and negative phase in analysis.
  Lean's period `T` is $h$ here. [Lean, read]
  [`Mathlib/Analysis/Fourier/AddCircle.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L84-L310)
- `fourierSubalgebra` (199–207) adjoins the characters and uses
  conjugation $e_m\mapsto e_{-m}$ on the generators.
  `fourierSubalgebra_coe` (211–221) proves that the generated
  algebra is already the span, since $e_0=1$ and
  $e_m e_n=e_{m+n}$. In `fourierSubalgebra_separatesPoints`
  (231–237), $e_1$ separates circle points because
  $e_1(x)=e_1(y)$ implies $x-y\in h\mathbb Z$.
  `fourierSubalgebra_closure_eq_top` (240–242) invokes complex
  Stone–Weierstrass and `span_fourier_closure_eq_top` (245–248)
  transports that closure identity to the linear span. [Lean, read]
  [`AddCircle.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L199-L248)
- `span_fourierLp_closure_eq_top` (261–269) maps the dense span
  through the continuous linear map taking continuous functions to
  their $L^p$ classes. Its range is dense for finite $p$, so the
  closure of the image contains that range. Mapping the span gives
  precisely the span of `fourierLp` (252–253). In
  `orthonormal_fourier` (272–283), the diagonal integral has mass
  one. Off the diagonal, translation by $h/(2(k-j))$ negates
  $e_{k-j}$ and preserves the integral, so the integral vanishes.
  [Lean, read]
  [`AddCircle.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L250-L283)
- `fourierBasis` (411–412) passes those two proofs to
  `HilbertBasis.mk`. The resulting basis vectors are `fourierLp 2`
  by `coe_fourierBasis` (417–418). In `fourierBasis_repr`
  (423–430), the coordinate inner product integrates the conjugate
  character, which agrees almost everywhere with the conjugate
  of the continuous representative. The coordinates are therefore
  the Fourier coefficients. `hasSum_fourier_series_L2` (433–436)
  now applies Hilbert basis expansion, yielding $L^2$ convergence
  over finite sets of frequencies. [Lean, read]
  [`AddCircle.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L407-L436)
- `fourierCoeff_toLp` (485–488) preserves the coefficients under
  passage to the $L^2$ class. `hasSum_fourier_series_of_summable`
  (494–500) obtains a sum in the sup norm by summability of the
  term norms. It uses `ContinuousMap.hasSum_of_hasSum_Lp`
  (190–194) to compare that sum with the $L^2$ sum. The comparison
  maps the uniform limit into $L^2$, uses uniqueness of the norm
  limit there, and applies `ContinuousMap.toLp_injective`
  (178–180) under positivity on open sets. Finally,
  `has_pointwise_sum_fourier_series_of_summable` (504–506)
  applies the bounded evaluation map at $x$. This is the result
  consumed by `Real.tsum_eq_tsum_fourier` (103–117) at unit period.
  [Lean, read]
  [`AddCircle.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L485-L506)
  · [`Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean#L178-L194)
  · [`Mathlib/Analysis/Fourier/PoissonSummation.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/PoissonSummation.lean#L103-L117)

[§14.4.2.2](#14422-stoneweierstrass-for-the-circle-character-algebra) reads the
general Stone–Weierstrass proof used in this chain, and
[§14.4.2.3](#14423-continuous-functions-are-dense-in-l2-of-the-circle) reads the
dense-range proof `ContinuousMap.toLp_denseRange`. The Hilbert-space
machinery retains [Lean] at this reading boundary. The section gives
the circle-specific approximation and uniqueness arguments above
[Expository]. [`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`, `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean`, line 401](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean#L401)
· [`ContinuousMap.toLp_denseRange`, `Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`, lines 361–365](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean#L361-L365)
· [`HilbertBasis.hasSum_repr`, `Mathlib/Analysis/InnerProductSpace/l2Space.lean`, lines 446–447](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L446-L447)
· [`HilbertBasis.mk`, same file, lines 540–541](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L540-L541)

#### 14.4.2.2 Stone–Weierstrass for the circle character algebra

**Motivation.** The library proof behind the circle Fourier basis starts
in the uniform norm. Why does the finite character span approximate
every continuous function? Its multiplication law makes it an algebra,
and its conjugation law lets us turn a complex separator into a
real-valued one. In the real uniform closure we can then take maxima
and minima, which lets us patch local estimates on the compact circle.

**Example 1 (a continuous function of infinite Fourier support).**
Write $X=\mathbb R/h\mathbb Z$ with $h>0$ and $z=e^{2\pi i x/h}$ for the
unit-circle coordinate. Take $F(x)=(2-z^{-1})^{-1}$. This is continuous
since $|2-z^{-1}|\ge 1$. Let $P_N=\frac12\sum_{j=0}^N (z^{-1}/2)^j$.
Multiplying by $2-z^{-1}$ telescopes to give
$F-P_N=(z^{-1}/2)^{N+1}/(2-z^{-1})$. Hence
$\|F-P_N\|_\infty=2^{-(N+1)}$, with equality at $z=1$.
To see why the series never terminates, suppose $(2-z^{-1})P=1$ for
a nonzero Laurent polynomial $P$ whose least and greatest exponents
are $a$ and $b$. The product has a nonzero term of degree $a-1$ from
$-z^{-1}P$ and one of degree $b$ from $2P$. The powers are linearly
independent on the circle: integrating $z^k$ over one period gives zero
for $k\ne 0$ and one for $k=0$ with normalized measure. Thus both
extreme degrees would have to be zero, forcing $a=1>b=0$.

**Example 2 (analytic polynomials and a missing frequency).**
Let $Q(z)=\sum_{j=0}^N a_jz^j$. These polynomials contain the constants,
are closed under multiplication and separate points via $z$, but
conjugation takes $z$ to $z^{-1}$. Here is the uniform obstruction.
For $m\ge1$ put $L_m(G)=h^{-1}\int_0^h z^m G(x)\,dx$. Then
$|L_m(G)|\le\|G\|_\infty$ and $L_m(Q)=0$, since
$h^{-1}\int_0^h e^{2\pi i (m+j)x/h}\,dx=0$ for every $j\ge0$.
On the other hand $L_m(z^{-m})=1$. Therefore
$\|z^{-m}-Q\|_\infty\ge1$, and $Q=0$ attains the bound. Every uniform
limit of analytic polynomials still has $L_m=0$ for each $m\ge1$.
For the first example the same calculation on $P_N$ and uniform
convergence give $L_m(F)=2^{-(m+1)}$ for every $m\ge1$. So the obstruction
also applies to that continuous function of infinite Fourier support.

**Definition (the star algebra and its real part).**
Let $K$ be a compact Hausdorff space. A unital complex star subalgebra
$A$ of $C(K,\mathbb C)$ contains the constant $1$ and is closed under
complex linear combinations, pointwise multiplication and pointwise
conjugation. It separates points if for each $x\ne y$ some $f\in A$
satisfies $f(x)\ne f(y)$. Write $I(u)(x)=u(x)$, viewed as a complex
number, for the real-to-complex inclusion and set
$B=\{u\in C(K,\mathbb R): I(u)\in A\}$. This is a unital real
subalgebra. In the pinned proof, $B$ is obtained by restricting scalars
to $\mathbb R$ and then taking the comap, or inverse image, along the
continuous algebra homomorphism induced by the scalar inclusion.
The complex theorem also uses the same inclusion as a continuous
real-linear map.

**Lemma (real separators and uniform approximation).** If $A$ separates
points, so does $B$. Every unital point-separating real subalgebra of
$C(K,\mathbb R)$ is uniformly dense. Consequently, $A$ is uniformly dense
in $C(K,\mathbb C)$.

**Proof.** Given $x\ne y$, choose a complex separator $f\in A$ and put
$g=f-f(y)1$. The constant is available by unitality and complex scalar
multiplication. Conjugation gives $\overline g\in A$, and multiplication
gives $g\overline g\in A$. Its real-valued function $|g|^2$ belongs
to $B$, is zero at $y$, and is strictly positive at $x$. This is the
norm-square construction in the pinned realification lemma.

Let $B$ now be any unital point-separating real subalgebra and set
$D=\overline B$ for the sup norm. Continuity of the algebra operations
makes $D$ a closed real subalgebra. For $u\in D$, its range lies
in $[-\|u\|_\infty,\|u\|_\infty]$. By ordinary interval Weierstrass,
for any $\eta>0$ there is a real polynomial $p$ uniformly within
$\eta$ of $|t|$ on that interval. The zero-norm case gives $|u|=0$
directly. Substituting $u$ into $p$ gives $p(u)\in D$ using constants
and multiplication, and $\|p(u)-|u|\|_\infty<\eta$. Thus $|u|\in D$.
In the source this substitution is expressed by bounding the codomain
of $u$, approximating on that interval, and pulling the polynomial
approximants back along the bounded continuous map. Now $D$ contains
both pointwise extrema of $u,v\in D$, since the minimum and maximum
are $(u+v-|u-v|)/2$ and $(u+v+|u-v|)/2$, respectively.

Take $w\in C(K,\mathbb R)$ and $\varepsilon>0$. The empty-space case
is immediate since it has only one function. For each $x,y\in K$
choose $g_{xy}\in B$ interpolating $w$ at $x$ and $y$. When $x=y$ use
the constant $w(x)$. When $x\ne y$, choose $s\in B$ separating them
and take
$g_{xy}=w(y)1+\frac{w(x)-w(y)}{s(x)-s(y)}(s-s(y)1)$.
This is the strong separation condition used by the lattice proof.

For fixed $x$, the open sets
$U_{xy}=\{t:g_{xy}(t)>w(t)-\varepsilon\}$ cover $K$, because
$y\in U_{xy}$. Choose a finite nonempty subcover indexed by $Y_x$.
The pointwise maximum $H_x=\max_{y\in Y_x}g_{xy}$ belongs to $D$,
satisfies $H_x(x)=w(x)$ and is strictly above $w-\varepsilon$
everywhere. Next the open sets $V_x=\{t:H_x(t)<w(t)+\varepsilon\}$
cover $K$, since each contains $x$. Choose a finite nonempty subcover
indexed by $E$. The pointwise minimum $P=\min_{x\in E}H_x$ is in $D$.
At any $t$ every term in this minimum is above $w(t)-\varepsilon$, and
at least one term is below $w(t)+\varepsilon$. Hence
$|P(t)-w(t)|<\varepsilon$ at every point. Its continuous error attains
its maximum by compactness, so $\|P-w\|_\infty<\varepsilon$. Varying
$\varepsilon$ and using closedness gives $w\in D$. This explains why
the finite maximum comes first and the finite minimum second.

Returning to the real part $B$ of $A$, its density means
$I(C(K,\mathbb R))\subseteq\overline A$: the inclusion is isometric
and sends each approximant in $B$ into $A$. For $F=u+iv$, choose
$b,c\in B$ within $\varepsilon/2$ of $u,v$ respectively. Then
$I(b)+iI(c)\in A$ and its distance from $F$ is less than
$\varepsilon$. In the source, continuity of $I$ gives the closure
inclusion through the image of the comap, followed by addition and
scalar multiplication of the two real-valued parts in the closure. $\square$

**Corollary (circle character density).** For $h>0$, any
$F\in C(\mathbb R/h\mathbb Z,\mathbb C)$ and $\varepsilon>0$ admit a
finite sum $P=\sum_{m\in S}a_m e_m$, where $e_m(x)=e^{2\pi i m x/h}$
and $S\subset\mathbb Z$, with $\|F-P\|_\infty<\varepsilon$.

**Proof.** The quotient is compact, as the image of $[0,h]$, and
Hausdorff, since $h\mathbb Z$ is closed. The span is the unital
algebra generated by the characters: $e_0=1$ and
$e_me_n=e_{m+n}$, so products introduce only other characters.
Conjugation sends $e_m$ to $e_{-m}$ and conjugates the coefficients.
Finally $e_1(x)=e_1(y)$ implies that representatives differ by
a multiple of $h$, so $e_1$ separates the quotient points. Apply
the lemma to this star subalgebra. In particular, the real separator
built from $e_1$ at $y$ is
$|e_1(x)-e_1(y)|^2=2-e_1(x)\overline{e_1(y)}-e_{-1}(x)e_1(y)$,
an explicit real trigonometric polynomial. $\square$

**Notes on the proof and its consumer.** The finite-cover argument
is textbook exposition [Expository]. The proof-body correspondence
below is [Lean, read] at Mathlib pin
`0df444a360eaa60ab8c11dca51a86af692955474`, fixed by the archive
manifest. The archive bundle SHA-256 is
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

| File and lines at the pin | Role | Reading |
|---|---|---|
| [`Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean:64–160`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean#L64-L160) | `attachBound`, polynomial substitution, pullback into the closure and the absolute-value formulas for the extrema. | Read here |
| [`StoneWeierstrass.lean:165–279`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean#L165-L279) | `sublattice_closure_eq_top` uses two finite subcovers. `subalgebra_topologicalClosure_eq_top_of_separatesPoints` applies it to the closed real algebra. | Read here |
| [`StoneWeierstrass.lean:369–437`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean#L369-L437) | `Subalgebra.SeparatesPoints.rclike_to_real` uses the shifted norm square. `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints` transports the real closure through the inclusion and recombines the two parts over an `RCLike` scalar field. | Read here |
| [`Mathlib/Analysis/Fourier/AddCircle.lean:199–269`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L199-L269) | The character star algebra, its equality with the span, separation by `fourier 1`, the actual complex Stone–Weierstrass call, and transfer of the dense span into $L^p$. | Inherited from §14.4.2.1 |
| [`Mathlib/Topology/ContinuousMap/Weierstrass.lean:83–86`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/Weierstrass.lean#L83-L86) | `continuousMap_mem_polynomialFunctions_closure` and its interval Weierstrass supply. The algebraic strong-separation helper, submodule closure-map lemmas and general measure and Hilbert machinery are library inputs as well. | Retained inputs [Lean] |

For the connection to Poisson, use the
[preceding $L^2$ and pointwise consumer](#14421-fourier-completeness-on-the-circle-and-pointwise-reconstruction).
Its dense-range step sends the uniform result into $L^2$ of normalized
Haar measure, using $\|P-F\|_2\le\|P-F\|_\infty$ on continuous
functions. Thus a continuous difference with zero Fourier coefficients
is orthogonal to a dense span, vanishes in $L^2$, and vanishes
everywhere by positivity of Haar measure on nonempty open arcs.
In the existing Poisson argument, the difference is the
periodization minus the continuous sum of its absolutely summable
Fourier series. This gives precisely the uniqueness used there.
The pinned consumer passes through `ContinuousMap.toLp_denseRange`
and `HilbertBasis.hasSum_repr` before identifying the continuous
representative. The measure-density proof is read in
[§14.4.2.3](#14423-continuous-functions-are-dense-in-l2-of-the-circle); the
Hilbert-expansion proof remains a named input [Lean]. The real-strip trace application
retains its [Open] status.

#### 14.4.2.3 Continuous functions are dense in $L^2$ of the circle

**Motivation.** The uniqueness argument that closes the Poisson proof in
§14.4.2.1 needs the trigonometric polynomials to be dense in $L^2(\mu_h)$,
not only in $C(X_h)$. [§14.4.2.2](#14422-stoneweierstrass-for-the-circle-character-algebra)
proved uniform density. The passage from uniform to $L^2$ density has two
parts. The first is the one-line inequality $\|F\|_2\le\|F\|_\infty$ for a
probability measure. The second is the statement that every $L^2$ function
is an $L^2$ limit of continuous functions. The second part is where
measure theory enters, and it was left as a named library input in both
preceding subsections. This subsection expands it, following the pinned
Mathlib proof of `ContinuousMap.toLp_denseRange` step by step, and checks
each topological and measure-theoretic hypothesis against the circle.

**Why the norm inequality alone is not enough.** Write $X_h=\mathbb R/h\mathbb Z$
with probability Haar measure $\mu_h$, and let $A\subset X_h$ be a closed
arc of length $h/2$. For any continuous $v$, the two one-sided limits of
$\mathbf 1_A$ at an endpoint of the arc are $0$ and $1$, while $v$ has a
single value there. Hence $\|\mathbf 1_A-v\|_\infty\ge\frac12$. No uniform
approximation argument, and in particular no consequence of
$\|F\|_2\le\|F\|_\infty$, can reach $\mathbf 1_A$. The inequality shows
that the $L^2$ closure of the trigonometric polynomials contains $C(X_h)$,
and nothing more. The claim that $C(X_h)$ is itself $L^2$ dense is a
statement about the measure. The Mathlib file header records the same
obstruction for $p=\infty$: the indicator of $[0,\infty)$ on $\mathbb R$
has no continuous approximants in $L^\infty$ [Lean, read].

**Example 1 (a continuous cap on an arc).** Take $h=1$, so $\mu_1$ is
Lebesgue measure on $[0,1)$, and $A=[\frac14,\frac34]$. For
$0<\delta<\frac18$ define the cap $v_\delta$ to be $1$ on
$[\frac14+\delta,\frac34-\delta]$, to be $0$ outside
$(\frac14-\delta,\frac34+\delta)$, and to be linear on the two ramps of
width $2\delta$ in between. This is the Urysohn function for the closed
set $s=[\frac14+\delta,\frac34-\delta]$ inside the open set
$u=(\frac14-\delta,\frac34+\delta)$. On the outer half of each ramp the
error is $v_\delta$ itself, which runs linearly from $0$ to $\frac12$, and
on the inner half the error is $1-v_\delta$, which runs from $\frac12$ to
$0$. Each of the four half-ramps has length $\delta$ and contributes
$$
 \int_0^{\delta}\Bigl(\frac{t}{2\delta}\Bigr)^2dt=\frac{\delta}{12},
 \qquad\text{so}\qquad
 \|\mathbf 1_A-v_\delta\|_2^2=\frac{\delta}{3}.
$$
The proof below bounds this error by $\mu_1(u\setminus s)^{1/2}=(4\delta)^{1/2}$,
since $|\mathbf 1_A-v_\delta|\le\mathbf 1_{u\setminus s}$ pointwise. For
$\delta=\frac1{48}$ the exact error is $\frac1{12}$ and the bound is
$\frac1{\sqrt{12}}\approx0.289$. A midpoint quadrature with $2\cdot10^5$
cells reproduces $\frac1{144}$ for the squared error. The uniform error
stays at $\frac12$ for every $\delta$.

**Example 2 (a two-step function).** Still with $h=1$, let
$f=2\cdot\mathbf 1_{[0,\frac14)}-\mathbf 1_{[\frac12,\frac34)}$, a simple
function with two disjoint steps. Approximate each indicator by a cap
with ramp half-width $\delta<\frac18$ as in Example 1 and add the results
with the coefficients $2$ and $-1$. The ramps of the two caps are disjoint,
so the two errors are orthogonal in $L^2$, and
$$
 \|f-g_\delta\|_2^2=4\cdot\frac{\delta}{3}+1\cdot\frac{\delta}{3}=\frac{5\delta}{3}.
$$
The triangle inequality alone gives the weaker bound
$2\sqrt{\delta/3}+\sqrt{\delta/3}=\sqrt{3\delta}$. For $\delta=\frac1{300}$
the exact error is $\sqrt{1/180}\approx0.0745$ and the triangle bound is
$0.1$. To bring the error below $\frac1{10}$ it suffices to take
$\delta<\frac{3}{500}$. The pinned proof does not use orthogonality. It
halves the target error at each addition, which is what the triangle
estimate records.

**Definitions (the hypotheses of the pinned theorem).** Let $\alpha$ be a
topological space with its Borel $\sigma$-algebra and let $\mu$ be a
measure on it. The space is *normal* if any two disjoint closed sets have
disjoint open neighbourhoods. The measure is *outer regular* if for every
Borel $A$ and $r>\mu(A)$ there is an open $U\supseteq A$ with $\mu(U)<r$.
It is *weakly regular* if in addition every open $U$ satisfies
$\mu(U)=\sup\{\mu(F):F\subseteq U\text{ closed}\}$. It is *regular* if it
is finite on compact sets, outer regular, and every open $U$ satisfies
$\mu(U)=\sup\{\mu(K):K\subseteq U\text{ compact}\}$. In an
$\mathrm R_1$ space, where the closure of a compact subset of an open set
stays inside that open set, a regular measure is weakly regular, because
the closure of an inner compact is an inner closed set of no smaller
measure. These are the classes `OuterRegular`, `WeaklyRegular` and
`Regular` of the pinned `Mathlib/MeasureTheory/Measure/Regular.lean`,
lines 308–326, and the instance `Regular.weaklyRegular` at lines 341–346
[Lean, read].

For a normed space $E$ and $p\in[1,\infty)$, write $\mathcal L^p$ for the
strongly measurable functions $f\colon\alpha\to E$ with
$\int\|f\|^p\,d\mu<\infty$ and $L^p$ for its quotient by almost-everywhere
equality. The map `ContinuousMap.toLp` sends a continuous function on a
compact space to its $L^p$ class, and `BoundedContinuousFunction.toLp`
does the same for bounded continuous functions on an arbitrary space.
Both are continuous linear maps.

**The circle satisfies every hypothesis.** The following table aligns the
instance arguments of `ContinuousMap.toLp_denseRange` with the circle
$X_h$, the field $E=\mathbb C$, the exponent $p=2$ and the measure
$\mu_h=$ `haarAddCircle`.

| Hypothesis in Lean | Where it holds for the circle |
|---|---|
| `[CompactSpace α]` | `AddCircle.compactSpace` (`Mathlib/Topology/Instances/AddCircle/Real.lean:33`): the quotient is the image of a compact interval. |
| `[NormalSpace α]` | $X_h$ is Hausdorff because $h\mathbb Z$ is closed in $\mathbb R$, and a compact Hausdorff space is normal: `NormalSpace.of_compactSpace_r1Space` (`Mathlib/Topology/Separation/Regular.lean:523–525`) separates two disjoint compact sets. |
| `[MeasurableSpace α] [BorelSpace α]` | The Borel structure of the circle. Instance supply retained [Lean]. |
| `[μ.WeaklyRegular]` | Two routes. `haarAddCircle` is `addHaarMeasure ⊤` (`AddCircle.lean:85–87`), and Haar measure is regular (`regular_haarMeasure`, additive version by `to_additive`, `Mathlib/MeasureTheory/Measure/Haar/Basic.lean:550–557`), hence weakly regular by the instance above. Alternatively, any finite measure on a metrizable space is weakly regular (`WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure`, `Regular.lean:1072–1076`). The statement of either instance is read; the bodies are retained [Lean]. |
| `[IsFiniteMeasure μ]` | `haarAddCircle` is a probability measure (`AddCircle.lean:89–90`). |
| `[SecondCountableTopologyEither α E]` | $E=\mathbb C$ is second countable. |
| `[Fact (1 ≤ p)]`, `hp : p ≠ ∞` | $p=2$. |

Only the `NormalSpace`, `OuterRegular` and `WeaklyRegular` hypotheses are
used in the proof bodies below, together with finiteness of the measure
of the set being approximated. The compactness hypothesis enters only to
make every continuous function bounded, so that `ContinuousMap.toLp` is
defined.

**Lemma A (small sets have small indicator norm).** Let $p\in(0,\infty)$,
$c\in E$ and $\varepsilon>0$. There is $\eta>0$ such that every measurable
$s$ with $\mu(s)\le\eta$ satisfies $\|c\,\mathbf 1_s\|_{L^p}\le\varepsilon$.

**Proof.** The norm equals $\|c\|\,\mu(s)^{1/p}$, and $t\mapsto\|c\|t^{1/p}$
is continuous at $0$ with value $0$. Choose $\eta$ so that
$\|c\|\eta^{1/p}\le\varepsilon$ and use monotonicity in $\mu(s)$. This is
`exists_eLpNorm_indicator_le` (`Mathlib/MeasureTheory/Function/LpSpace/Indicator.lean:39–59`),
which handles $p=0$ separately and proves the continuity claim from the
continuity of real powers at zero [Lean, read]. $\square$

**Lemma B (inner approximation by closed sets).** Let $\mu$ be a finite
measure on a metric space with its Borel $\sigma$-algebra. For every Borel
set $A$ and $\eta>0$ there is a closed $F\subseteq A$ with
$\mu(A\setminus F)<\eta$ and an open $U\supseteq A$ with
$\mu(U\setminus A)<\eta$.

**Proof.** Call a Borel set *good* if it has both properties for every
$\eta$. A closed set $F$ is good: take $F$ itself inside, and outside take
$U_n=\{x:d(x,F)<1/n\}$, open with $\bigcap_nU_n=F$ because $F$ is closed.
Continuity from above for the finite measure $\mu$ gives $\mu(U_n)\to\mu(F)$.
The complement of a good set is good, since complements exchange closed
with open and $A^c\setminus U^c=U\setminus A$. For a countable union
$A=\bigcup_nA_n$ of good sets, choose closed $F_n\subseteq A_n$ and open
$U_n\supseteq A_n$ with errors below $\eta2^{-n-1}$. Then $U=\bigcup U_n$
is open and $\mu(U\setminus A)\le\sum\mu(U_n\setminus A_n)<\eta/2$. The
union $\bigcup F_n$ need not be closed, but $\mu(A\setminus\bigcup_{n\le N}F_n)$
decreases to $\mu(A\setminus\bigcup F_n)<\eta/2$ as $N\to\infty$ by
continuity from above, so a finite union of the $F_n$ serves as the closed
inner set. Good sets therefore form a $\sigma$-algebra containing the
closed sets, hence all Borel sets. $\square$

In the pinned library this is split. Outer approximation is
`MeasurableSet.exists_isOpen_sdiff_lt` (`Regular.lean:385–390`), which takes
an open $U$ with $\mu(U)<\mu(A)+\eta$ from outer regularity and subtracts
the finite measure of $A$ [Lean, read]. Inner approximation is
`MeasurableSet.exists_isClosed_sdiff_lt` (`Regular.lean:1036–1041`), which
assumes only `WeaklyRegular` and finite $\mu(A)$ and quotes the lemma
`exists_isClosed_lt_add` from the inner regularity of measurable sets by
closed sets. That inner regularity is produced from weak regularity by
`InnerRegularWRT.weaklyRegular_of_finite`, the general form of the
good-sets argument above. Its body is retained [Lean]. The metric proof
given here covers the circle, whose quotient metric is the distance to
$h\mathbb Z$. The Lean theorem has no metric hypothesis.

**Lemma C (the continuous cap for a closed set).** Let $\alpha$ be normal
with $\mu$ outer regular, let $s\subseteq u$ with $s$ closed, $u$ open and
$\mu(s)<\infty$, let $c\in E$, $p\in(0,\infty)$ and $\varepsilon>0$. There
is a continuous $f\colon\alpha\to E$ with $\|f(x)\|\le\|c\|$ for all $x$,
support contained in $u$, $f\in\mathcal L^p$, and
$\|f-c\,\mathbf 1_s\|_{L^p}\le\varepsilon$.

**Proof.** Take $\eta$ from Lemma A for $c$ and $\varepsilon$. Outer
regularity gives an open $V\supseteq s$ with $\mu(V)<\infty$ and
$\mu(V\setminus s)<\eta$. Put $v=u\cap V$, which is open, contains $s$ and
has finite measure. The sets $v^c$ and $s$ are closed and disjoint, so
Urysohn's lemma for the normal space $\alpha$ gives a continuous
$g\colon\alpha\to[0,1]$ with $g=0$ on $v^c$ and $g=1$ on $s$. Set
$f(x)=g(x)\,c$. Then $\|f(x)\|=g(x)\|c\|\le\|c\|$, and the support of $f$
lies in $v\subseteq u$.

The key estimate is pointwise. If $x\in s$, then $f(x)=c=c\mathbf 1_s(x)$,
so the difference vanishes. If $x\in v\setminus s$, then
$\|f(x)-0\|\le\|c\|=\|c\,\mathbf 1_{v\setminus s}(x)\|$. If $x\notin v$,
then $f(x)=0$ and $x\notin s$, so both sides vanish. Hence
$\|f-c\,\mathbf 1_s\|\le\|c\,\mathbf 1_{v\setminus s}\|$ at every point,
and monotonicity of the $\mathcal L^p$ norm with
$\mu(v\setminus s)\le\mu(V\setminus s)<\eta$ gives the bound
$\varepsilon$ by Lemma A. Finally $f$ is the product of the bounded
function $g$ with the constant $c$, and $\|f\|\le\|c\|\mathbf 1_v$ with
$\mu(v)<\infty$, so $f\in\mathcal L^p$. $\square$

This is `exists_continuous_eLpNorm_sub_le_of_closed`
(`Mathlib/MeasureTheory/Function/ContinuousMapDense.lean:79–131`) [Lean, read].
The proof obtains $\eta$ at lines 86–88, the open $V$ at lines 90–91,
the Urysohn function at lines 95–97 with the disjointness of $v^c$ and $s$
supplied by $s\subseteq v$, the three pointwise cases at lines 106–115,
the support at lines 116–118, the $\mathcal L^p$ membership at lines
119–128, and the final monotonicity step at lines 129–131. Urysohn's
lemma itself, `exists_continuous_zero_one_of_isClosed`
(`Mathlib/Topology/UrysohnsLemma.lean:322`), is used as a named input:
its statement was read, its construction by iterated midpoint
interpolation was not [Lean].

**Lemma D (the indicator of a measurable set).** Let $\alpha$ be normal
and $\mu$ weakly regular. For every measurable $t$ with $\mu(t)<\infty$,
every $c\in E$ and $\varepsilon>0$ there is a bounded continuous
$f\colon\alpha\to E$ in $\mathcal L^p$ with
$\|f-c\,\mathbf 1_t\|_{L^p}<\varepsilon$.

**Proof.** Choose $\delta>0$ such that any two functions of
$\mathcal L^p$ norm at most $\delta$ have a sum of norm less than
$\varepsilon$. For $p\ge1$ the triangle inequality allows
$\delta=\varepsilon/3$. Take $\eta$ from Lemma A for $c$ and $\delta$, and
a closed $s\subseteq t$ with $\mu(t\setminus s)<\eta$ from inner
approximation. Then $c\mathbf 1_s-c\mathbf 1_t=-c\mathbf 1_{t\setminus s}$
has norm at most $\delta$. Apply Lemma C with $u=\alpha$ to get a
continuous $f$ with $\|f\|\le\|c\|$ and $\|f-c\mathbf 1_s\|_{L^p}\le\delta$.
Writing $f-c\mathbf 1_t=(f-c\mathbf 1_s)+(c\mathbf 1_s-c\mathbf 1_t)$
gives the claim. $\square$

In Example 2, the sets $t$ are the two intervals, the closed inner sets
are the intervals shrunk by $\delta$, and the Urysohn functions are the
caps. The halving device is `exists_Lp_half`
(`Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean:81–85`),
which covers $p<1$ through the constant in the quasi-triangle inequality.
Its statement was read and its body is retained [Lean].

**Lemma E (from simple functions to all of $\mathcal L^p$).** Let
$p\in(0,\infty)$ and let $P$ be a class of almost-everywhere strongly
measurable functions $\alpha\to E$ that is closed under addition and
satisfies Lemma D in the form: for every $c\in E$, measurable $t$ with
$\mu(t)<\infty$ and $\varepsilon>0$ there is $g\in P$ with
$\|g-c\mathbf 1_t\|_{L^p}\le\varepsilon$. Then for every
$f\in\mathcal L^p$ and $\varepsilon>0$ there is $g\in P$ with
$\|f-g\|_{L^p}\le\varepsilon$.

**Proof.** First, every $f\in\mathcal L^p$ is within $\eta$ of a simple
function $f'\in\mathcal L^p$. On the circle with $E=\mathbb C$ and
$p=2$ one can see this directly. Let $f_n$ round the real and imaginary
parts of $f$ towards zero to the nearest multiple of $2^{-n}$ and set
the result to $0$ where $|f|>n$. Then $f_n$ takes finitely many values,
$|f_n|\le|f|$, and $f_n\to f$ pointwise. Dominated convergence with the
integrable dominator $4|f|^2$ gives $\|f-f_n\|_2\to0$. Fix such an $f'$
with $\|f-f'\|_{L^p}\le\eta$, where $\eta$ is chosen so that two norms at
most $\eta$ add to less than $\varepsilon$.

Second, argue by induction on the simple function $f'$. A simple function
is a finite sum of terms $c\mathbf 1_s$ with pairwise disjoint supports.
If $c=0$ the term is zero and the hypothesis applied to $0\cdot\mathbf 1_\emptyset$
gives an approximant. If $c\ne0$ and $c\mathbf 1_s\in\mathcal L^p$, then
$\mu(s)<\infty$, so Lemma D applies directly. For a sum $f_1+f_2$ with
disjoint supports and $f_1+f_2\in\mathcal L^p$, both summands lie in
$\mathcal L^p$ because $\|f_1+f_2\|^p=\|f_1\|^p+\|f_2\|^p$ pointwise.
Halve the target, approximate each summand by $g_1,g_2\in P$, and use
$g_1+g_2\in P$ with the triangle estimate. $\square$

This is `MemLp.induction_dense`
(`Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean:847–894`) [Lean, read].
The proof dismisses $p=0$ at lines 855–858, reduces to simple functions
at lines 859–868 through `exists_Lp_half` and
`MemLp.exists_simpleFunc_eLpNorm_sub_lt`, and runs
`SimpleFunc.induction` (`Mathlib/MeasureTheory/Function/SimpleFunc.lean:1260`)
at lines 869–894 with the two cases above. The zero case at lines
871–878, the finite-measure deduction `measure_lt_top_of_memLp_indicator`
(`SimpleFuncDenseLp.lean:343`) at line 879, and the disjoint splitting
`memLp_add_of_disjoint` at lines 885–886 are the places where the
hypotheses are consumed. The density of simple functions in $L^p$ behind
`exists_simpleFunc_eLpNorm_sub_lt` and `Lp.simpleFunc.denseRange`
(`SimpleFuncDenseLp.lean:671–673`) is a retained input; the dominated
convergence proof above covers the circle case [Lean].

**Theorem (continuous functions are dense in $L^p$).** Let $\alpha$ be a
normal space with its Borel $\sigma$-algebra, $\mu$ a weakly regular
measure, $E$ a normed space, and $1\le p<\infty$. Then the classes of
bounded continuous functions are dense in $L^p(\mu;E)$. If $\alpha$ is
compact and $\mu$ is finite, the continuous linear map
$C(\alpha,E)\to L^p(\mu;E)$ has dense range. In particular, for every
$h>0$, $C(X_h,\mathbb C)$ is dense in $L^2(\mu_h)$.

**Proof.** Take $P$ to be the class of bounded continuous functions in
$\mathcal L^p$. It is closed under addition and consists of measurable
functions. Lemma D supplies the indicator step: the function produced
there is bounded by $\|c\|$. Lemma E then gives, for any representative
$f$ of a class in $L^p$ and any $\varepsilon>0$, a bounded continuous
$g$ with $\|f-g\|_{L^p}\le\varepsilon$. The distance in $L^p$ between the
class of $f$ and the class of $g$ is this norm, so the classes with
bounded continuous representatives are dense. For compact $\alpha$ every
continuous function is bounded, so the range of $C(\alpha,E)\to L^p$
contains the range of the bounded continuous map, and a superset of a
dense set is dense. The circle case follows from the alignment table. $\square$

The pinned chain is `MemLp.exists_boundedContinuous_eLpNorm_sub_le`
(`ContinuousMapDense.lean:233–280`), which applies `induction_dense` to the
class of bounded continuous functions and proves the indicator step at
lines 255–280 exactly as in Lemma D; `Lp.boundedContinuousFunction_dense`
(lines 321–330), which passes from the representative to the $L^p$ class
through `Lp.edist_toLp_toLp`; `BoundedContinuousFunction.toLp_denseRange`
(lines 349–352), which identifies the subgroup with the range of `toLp` by
`range_toLp` (`Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean:108`);
and `ContinuousMap.toLp_denseRange` (lines 361–365), which uses
`DenseRange.mono` with the inclusion of ranges given by
`f.toContinuousMap`. All four bodies are read [Lean, read]. The identity
`Lp.edist_toLp_toLp` and the general `DenseRange.mono` are named inputs
[Lean].

**Remark (where regularity is really used).** Lemma C uses only outer
regularity, and Lemma D adds the inner approximation by closed sets. On
the circle both come for free from Lemma B, because the measure is finite
and the space is metric. The library hypothesis `WeaklyRegular` is the
abstract form of exactly these two approximations, and nothing stronger
is consumed: the inner-by-compact clause of `Regular` is never invoked in
the compact-space theorem, although the Haar instance provides it. The
version with compactly supported approximants,
`MemLp.exists_hasCompactSupport_eLpNorm_sub_le` (lines 135–185), does use
`Regular` together with local compactness, inserting a compact $k$ with
$s\subseteq\operatorname{int}k$ at lines 169–170. The circle does not
need it.

**Remark (Lusin and Urysohn are not the same lemma).** Urysohn's lemma
is purely topological and produces one function between two disjoint
closed sets. Lusin's theorem states that a measurable function agrees
with a continuous function outside a set of small measure. The pinned
proof uses Urysohn, applied once per indicator, and never Lusin. The
textbook route through Lusin would also prove the theorem, but it is a
different argument, with a different dependency on the measure, and it is
not what the archive's Mathlib pin does.

**Consumer (back to Poisson).** The Lean chain
`span_fourier_closure_eq_top` $\to$ `span_fourierLp_closure_eq_top`
(`AddCircle.lean:261–269`) maps the uniformly dense character span through
`ContinuousMap.toLp` and uses the dense range just proved: the closure of
the image of a dense submodule under a continuous linear map with dense
range is everything. With this supply, the density lemma of §14.4.2.1 is
complete without named gaps on its measure-theoretic side: uniform density
of trigonometric polynomials (§14.4.2.2), the inequality
$\|P-F\|_2\le\|P-F\|_\infty$ on continuous functions, and the present
theorem together give $L^2$ density of the trigonometric polynomials.
The reconstruction theorem of §14.4.2.1 then yields the uniqueness of
Fourier coefficients used at the end of the Poisson proof. The Hilbert
basis machinery `HilbertBasis.mk` and `HilbertBasis.hasSum_repr` remains a
named input for the $L^2$ expansion, and the real-strip trace application
keeps its [Open] status.

**Notes on the reading.** The pinned Mathlib commit is
`0df444a360eaa60ab8c11dca51a86af692955474`, fixed by the archive manifest
(`lean/lake-manifest.json:6–13`) of the bundle with SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The
file `ContinuousMapDense.lean` at that pin has SHA-256
`cfc609acec4ddfb845c07c6628ddb6b67d6114899ef6080a560144608dde245a`. The
two hand calculations and the metric good-sets proof of Lemma B are
textbook exposition [Expository]. Reading the source and building this
book do not constitute a kernel check.

| File and lines at the pin | Role | Reading |
|---|---|---|
| [`Mathlib/MeasureTheory/Function/ContinuousMapDense.lean:79–131`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean#L79-L131) | Lemma C: outer open set, Urysohn cap, three pointwise cases, support and membership. | Read here |
| [`ContinuousMapDense.lean:233–280`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean#L233-L280) | Lemma D inside the bounded continuous version of the density theorem: halving, inner closed set, the cap, the triangle step. | Read here |
| [`ContinuousMapDense.lean:321–336,349–352,361–365`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean#L321-L365) | From representatives to $L^p$ classes, to the range of `toLp`, to the compact-space statement. | Read here |
| [`Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean:847–894`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean#L847-L894) | Lemma E: reduction to simple functions and the two-case induction. | Read here |
| [`Mathlib/MeasureTheory/Function/LpSpace/Indicator.lean:39–59`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/LpSpace/Indicator.lean#L39-L59) | Lemma A. | Read here |
| [`Mathlib/MeasureTheory/Measure/Regular.lean:308–346,385–390,1036–1041`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Regular.lean#L308-L346) | Regularity classes, regular implies weakly regular, and the two approximation statements of Lemma B. | Classes and the two short bodies read; `exists_isClosed_lt_add` and `weaklyRegular_of_finite` retained |
| [`Mathlib/Topology/Separation/Regular.lean:523–525`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Separation/Regular.lean#L523-L525) · [`Mathlib/Topology/Instances/AddCircle/Real.lean:33`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Instances/AddCircle/Real.lean#L33) · [`Mathlib/MeasureTheory/Measure/Haar/Basic.lean:550–557`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L550-L557) | The circle instances of the alignment table. | Statements read; bodies retained [Lean] |
| [`Mathlib/Topology/UrysohnsLemma.lean:322`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UrysohnsLemma.lean#L322) · [`Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean:81–85`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean#L81-L85) · [`SimpleFuncDenseLp.lean:343,671–673`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean#L671-L673) | Urysohn's lemma, the halving constant, the finite-measure deduction and the density of simple functions. | Retained inputs [Lean] |
| [`Mathlib/Analysis/Fourier/AddCircle.lean:261–269`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L261-L269) | The consumer `span_fourierLp_closure_eq_top`. | Inherited from §14.4.2.1 |

For the classical background see Terence Tao's 245A notes, where Theorem
15 lists simple functions, step functions and continuous compactly
supported functions as dense in $L^1$ and Theorem 18 is Lusin's theorem
[Tao, 245A Notes 2](https://terrytao.wordpress.com/2010/09/19/245a-notes-2-the-lebesgue-integral/).
The Mathlib file is by Heather Macbeth (2021) and its header describes
the same three-step plan followed here
[Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ContinuousMapDense.html).


#### Factorial ratios and the infinite radius of the Banach exponential

**Motivation.** Power series in a Banach algebra come in two distinct regimes. A geometric series $\sum_{n\ge 0} x^n = (1-x)^{-1}$ has constant scalar coefficients $c_n = 1$, so consecutive terms change in size roughly by $\|x\|$, confining convergence to the open unit ball $\|x\| < 1$. By contrast, the exponential series $\exp(x) = \sum_{n\ge 0} x^n / n!$ divides the $n$-th step by $n$: even if $\|x\| = 10^6$, the first million terms grow enormously, yet once $n + 1 > 2\|x\|$ each new factor $\|x\|/(n+1)$ shrinks the scalar majorant by more than half. Historically, Jean le Rond d'Alembert already isolated this phenomenon in 1768 when analyzing factorial series at large arguments: initial growth is harmless provided the eventual consecutive ratio stays strictly below one. In Mathlib's formalization of Banach-algebra exponentials, the bridge from scalar coefficient ratios to an unbounded multilinear convergence radius is carried by `FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto` and consumed by `NormedSpace.expSeries_radius_eq_top`, which had remained a named statement-level input behind the inside-ball Cauchy-product and spectral-inclusion arguments. Reading that production chain in full reveals three structural subtleties that a one-line "$\text{radius} = \infty$" citation hides: why the coefficient ratio must go in the forward decay direction $\|c_{n+1}\|/\|c_n\| \to 0$ rather than its reciprocal, why eventual nonvanishing $c_n \ne 0$ is mandatory under totalized division $y/0 = 0$, and why separating degree $n = 0$ from $n \ge 1$ avoids assuming $\|1_A\| = 1$ or completeness when computing the radius—a generality directly exploited in the archive's Frobenius-norm matrix estimates. [Pinned scalar-series ratio test](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/OfScalars.lean#L243-L260) · [Pinned exponential top radius](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Algebra/Exponential.lean#L446-L460) · [d'Alembert 1768, Mémoire XXXV, §I, pp. 171–183](https://archive.org/details/opusculesmathma00conggoog)

**First calculation (infinite-dimensional scaled shift on $\ell^2(\mathbb N_0)$ and exact operator-norm tails).** Let $H = \ell^2(\mathbb N_0)$ be the complex Hilbert space of square-summable sequences $h = (h_0, h_1, \dots)$ with $\|h\|_2^2 = \sum_{k\ge 0} |h_k|^2$, and let $\mathcal B(H)$ be the unital Banach algebra of bounded linear operators on $H$ with the operator norm $\|T\|_{\mathrm{op}} = \sup_{\|h\|_2 = 1} \|Th\|_2$. Let $S e_k = e_{k+1}$ be the unilateral shift on the standard orthonormal basis, and consider $T = 2S$. Unlike a shift matrix on $\mathbb C^m$, which satisfies $S^m = 0$ and has a terminating exponential, every power $S^n$ ($n \ge 0$) on $\ell^2(\mathbb N_0)$ shifts coordinates without loss of norm: $\|S^n h\|_2 = \|h\|_2$, so $\|S^n\|_{\mathrm{op}} = 1$ for all $n \ge 0$. Consequently $\|T\|_{\mathrm{op}} = 2 > 1$ lies strictly outside the Neumann unit ball, and every degree-$n$ exponential term has exact operator norm
$$
 \left\|\frac{T^n}{n!}\right\|_{\mathrm{op}} = \frac{2^n}{n!}\,\|S^n\|_{\mathrm{op}} = \frac{2^n}{n!}.
$$
Writing $E_N(T) = \sum_{n=0}^{N-1} T^n / n!$ for the $N$-term partial sum, coordinate evaluation $u \mapsto u_k$ is continuous of norm one and $(S^n h)_k = h_{k-n}$ for $n \le k$ (and $0$ for $n > k$), so $\exp(2S)$ acts by causal factorial convolution:
$$
 \bigl(\exp(2S)h\bigr)_k = \sum_{n=0}^k \frac{2^n}{n!}\,h_{k-n}\qquad (k \ge 0).
$$
Let $\Delta_N = \exp(2S) - E_N(2S) = \sum_{n\ge N} (2^n/n!)S^n$ be the truncation remainder for $N \ge 1$. On the single basis vector $e_0$, the images $S^n e_0 = e_n$ are pairwise orthogonal, giving the $\ell^2$ tail
$$
 \|\Delta_N e_0\|_2 = \left(\sum_{n=N}^\infty \frac{4^n}{(n!)^2}\right)^{1/2},
$$
which is strictly smaller than the scalar tail $\sum_{n\ge N} 2^n/n!$. However, testing $\Delta_N$ on $e_0$ alone underestimates the operator norm! To capture phase alignment across shifted coordinates, test $\Delta_N$ on the unit-norm flat block vectors $v^{(L)} = L^{-1/2}\sum_{j=0}^{L-1} e_j \in \ell^2(\mathbb N_0)$. Fix integers $M \ge N$ and $L > M$. For each interior index $k \in \{M, \dots, L-1\}$ (there are $L - M$ such indices), every shift $n \in \{N, \dots, M\}$ satisfies $0 \le k - n \le L - 1$, so $(S^n v^{(L)})_k = L^{-1/2}$, while terms with $n > M$ are nonnegative. Hence $(\Delta_N v^{(L)})_k \ge L^{-1/2}\sum_{n=N}^M 2^n/n!$ on those $L - M$ coordinates, and summing squares gives
$$
 \|\Delta_N\|_{\mathrm{op}}^2 \ge \|\Delta_N v^{(L)}\|_2^2 \ge \frac{L - M}{L}\left(\sum_{n=N}^M \frac{2^n}{n!}\right)^2.
$$
Letting $L \to \infty$ and then $M \to \infty$, while combining with the triangle inequality $\|\Delta_N\|_{\mathrm{op}} \le \sum_{n\ge N} (2^n/n!)\|S^n\|_{\mathrm{op}}$, proves that the operator-norm remainder equals the exact scalar factorial tail:
$$
 \|\exp(2S) - E_N(2S)\|_{\mathrm{op}} = \sum_{n=N}^\infty \left\|\frac{(2S)^n}{n!}\right\|_{\mathrm{op}} = \sum_{n=N}^\infty \frac{2^n}{n!} = e^2 - \sum_{n=0}^{N-1} \frac{2^n}{n!}.
$$
Using the ratio majorant proved in Lemma 2 below, for every $N \ge 2$ we have $(N+k)! \ge N!(N+1)^k$ and hence
$$
 \frac{2^N}{N!} < \|\exp(2S) - E_N(2S)\|_{\mathrm{op}} \le \frac{2^N}{N!}\cdot\frac{N+1}{N-1}.
$$
To guarantee operator-norm accuracy $\varepsilon = 10^{-4}$, evaluate at $N = 10$ and $N = 11$: at $N = 10$ the upper bound is $\frac{2^{10}}{10!}\frac{11}{9} = \frac{44}{127575} \approx 3.45 \times 10^{-4} > 10^{-4}$, whereas at $N = 11$ the first omitted term and ratio bound bracket the exact infinite-dimensional operator error tightly inside $10^{-4}$:
$$
 \frac{8}{155925} < \|\exp(2S) - E_{11}(2S)\|_{\mathrm{op}} \le \frac{16}{259875} < 10^{-4}
$$
(numerically $5.13 \times 10^{-5} < 6.07 \times 10^{-5} \le 6.16 \times 10^{-5}$; meanwhile $\|\Delta_{11} e_0\|_2 \approx 5.20 \times 10^{-5}$, whereas at $M = 15, L = 300$ the block vector already gives $\|\Delta_{11} v^{(300)}\|_2 \ge \sqrt{7297550476 / 2038493457703828125} \approx 5.98 \times 10^{-5} > \|\Delta_{11} e_0\|_2$). For $\varepsilon = 10^{-6}$, the minimal ratio-certified cutoff is $N = 14$. [Expository]

**Second calculation (noncommutative, non-normal $2\times 2$ matrix in operator and Frobenius norms).** In $M_2(\mathbb C)$ with the Euclidean operator norm $\|M\|_{\mathrm{op}} = \sup_{\|u\|_2=1}\|Mu\|_2$, put
$$
 B = \begin{pmatrix}1 & 2 \\ 0 & -1\end{pmatrix} = D + V,\qquad
 D = \begin{pmatrix}1 & 0 \\ 0 & -1\end{pmatrix},\qquad
 V = \begin{pmatrix}0 & 2 \\ 0 & 0\end{pmatrix}.
$$
Here $DV = V$ whereas $VD = -V$, so $DV - VD = 2V \ne 0$ and the summands do not commute; moreover $B^* B = \begin{pmatrix}1 & 2 \\ 2 & 5\end{pmatrix} \ne \begin{pmatrix}5 & -2 \\ -2 & 1\end{pmatrix} = B B^*$, so $B$ is non-normal. Because $\operatorname{tr}(B^* B) = 6$ and $\det(B^* B) = 1$, the eigenvalues of $B^* B$ are $3 \pm 2\sqrt{2} = (\sqrt{2} \pm 1)^2$, giving the exact operator norm $R = \|B\|_{\mathrm{op}} = \sqrt{2} + 1 \approx 2.4142$. Yet direct multiplication yields $B^2 = I_2$, so $B^{2k} = I_2$ ($\|B^{2k}\|_{\mathrm{op}} = 1$) and $B^{2k+1} = B$ ($\|B^{2k+1}\|_{\mathrm{op}} = \sqrt{2} + 1$) for all $k \ge 0$, strictly below $(\sqrt{2}+1)^n$ at every degree $n \ge 2$. Grouping even and odd degrees in the absolutely convergent series gives
$$
 \exp(B) = \sum_{k=0}^\infty \frac{I_2}{(2k)!} + \sum_{k=0}^\infty \frac{B}{(2k+1)!}
 = \cosh(1)I_2 + \sinh(1)B
 = \begin{pmatrix}e & e - e^{-1} \\ 0 & e^{-1}\end{pmatrix}.
$$
Notice without expanding any antidiagonal product that $\exp(D)\exp(V) = \begin{pmatrix}e & 2e \\ 0 & e^{-1}\end{pmatrix}$ and $\exp(V)\exp(D) = \begin{pmatrix}e & 2e^{-1} \\ 0 & e^{-1}\end{pmatrix}$ both miss the off-diagonal entry $e - e^{-1}$ because $DV \ne VD$. For any cutoff $N \ge 1$, set $\alpha_N = \sum_{n\ge N,\,n\text{ even}} 1/n!$ and $\beta_N = \sum_{n\ge N,\,n\text{ odd}} 1/n!$. The exact matrix remainder is
$$
 \Delta_N(B) = \exp(B) - E_N(B) = \alpha_N I_2 + \beta_N B
 = \begin{pmatrix}\alpha_N + \beta_N & 2\beta_N \\ 0 & \alpha_N - \beta_N\end{pmatrix}.
$$
Because $B + B^* = \begin{pmatrix}2 & 2 \\ 2 & -2\end{pmatrix}$ has spectral norm $2\sqrt{2} < 2(\sqrt{2}+1)$, evaluating the characteristic polynomial of $\Delta_N(B)^*\Delta_N(B)$ at $\bigl(\alpha_N + (\sqrt{2}+1)\beta_N\bigr)^2$ shows a strict three-tier hierarchy at every $N \ge 2$:
$$
 \|\Delta_N(B)\|_{\mathrm{op}} < \alpha_N + (\sqrt{2}+1)\beta_N = \sum_{n=N}^\infty \left\|\frac{B^n}{n!}\right\|_{\mathrm{op}} < \sum_{n=N}^\infty \frac{(\sqrt{2}+1)^n}{n!} \le \frac{\bar R^N}{N!}\cdot\frac{N+1}{N + 1 - \bar R}
$$
for any rational upper bound $\bar R > \sqrt{2}+1$ with $N + 1 > \bar R$. Since $99^2 = 9801 > 2\cdot 70^2 = 9800$, we may take $\bar R = 1 + 99/70 = 169/70$. For $\varepsilon = 10^{-4}$, this coarse universal bound drops below $10^{-4}$ at $N = 13$, where $\frac{(169/70)^{13}}{13!}\frac{14}{14 - 169/70} < 1.84 \times 10^{-5}$ (the tighter Pell rational $\bar R = 33461/13860$ already certifies $N = 12$), while the actual term-norm tail $\alpha_{13} + (\sqrt{2}+1)\beta_{13}$ is below $4.02 \times 10^{-10}$ because $B^2 = I_2$ prevents norm growth. Finally, equip the same algebra $M_2(\mathbb C)$ with the submultiplicative Frobenius norm $\|M\|_F = (\sum_{i,j}|M_{ij}|^2)^{1/2}$. Then $\|I_2\|_F = \sqrt{2} > 1$ violates unit-norm normalization (`NormOneClass`), and at $n = 0$ the bound $\|B^0\|_F \le \|B\|_F^0$ fails ($\sqrt{2} > 1$); yet for all $n \ge 1$ we still have $\|B^n\|_F \le \|B\|_F^n = 6^{n/2}$, so separating $n = 0$ keeps the entire exponential convergence proof intact and yields $\|\exp(X)\|_F \le \|I_2\|_F + (e^{\|X\|_F} - 1) \le \sqrt{2}\,e^{\|X\|_F}$. [Expository]

**Definitions (scalar-coefficient formal multilinear series and convergence radius).** Let $\mathbb K$ be a nontrivially normed field, and let $A$ be a normed ring and normed $\mathbb K$-algebra (`‖ab‖ ≤ ‖a‖‖b‖` and `‖λa‖ = ‖λ‖‖a‖` for $\lambda \in \mathbb K$, $a,b \in A$, without assuming completeness of $A$, commutativity of $A$, nontriviality of $A$, or $\|1_A\| = 1$). Let $\Pi_n : A^n \to A$ denote ordered $n$-fold multiplication $\Pi_n(m_0,\dots,m_{n-1}) = m_0 m_1 \cdots m_{n-1}$, with empty product $\Pi_0() = 1_A$ (`ContinuousMultilinearMap.mkPiAlgebraFin`). Given a scalar sequence $c = (c_n)_{n\ge 0}$ in $\mathbb K$, the scalar formal multilinear series $p = \operatorname{ofScalars}(A, c)$ has degree-$n$ continuous multilinear map $p_n = c_n \Pi_n$, satisfying $p_n(x,\dots,x) = c_n x^n$. Its multilinear operator norm is $\|p_n\| = \inf\{M \ge 0 : \forall m \in A^n,\ \|p_n(m)\| \le M\prod_{i=0}^{n-1}\|m_i\|\}$, and its convergence radius in $[0, \infty]$ is
$$
 \operatorname{radius}(p) = \sup\bigl\{\,r \in \mathbb R_{\ge 0} : \exists C \in \mathbb R,\ \forall n \in \mathbb N,\ \|p_n\| r^n \le C\,\bigr\}.
$$
For $\mathbb K$ of characteristic zero, the exponential formal multilinear series is $\operatorname{expSeries}(\mathbb K, A) = \operatorname{ofScalars}(A, ((n!)^{-1})_{n\ge 0})$. Over any $\mathbb Q$-algebra $A$, Mathlib sets $\exp(x) = \sum'_{n\ge 0} ((n!)^{-1} : \mathbb Q) \cdot x^n$ (`NormedSpace.exp`), which coincides with $\sum'_{n\ge 0} ((n!)^{-1} : \mathbb K) \cdot x^n$ by unique rational scalar restriction. [Lean, read]

**Lemma 1 (positive-degree norm bound and ratio test for scalar formal multilinear series).** Let $\mathbb K$ be a nontrivially normed field, $A$ a normed ring and normed $\mathbb K$-algebra, and $c : \mathbb N \to \mathbb K$ a scalar sequence with $p = \operatorname{ofScalars}(A, c)$.
1. At degree $0$, $\|p_0\| = \|c_0\|\,\|1_A\|$. For every integer $n \ge 1$, $\|\Pi_n\| \le 1$ and $\|p_n\| \le \|c_n\|$, with equality for all $n \ge 0$ when $\|1_A\| = 1$.
2. Suppose there exists $N_0 \in \mathbb N$ such that $c_n \ne 0$ for all $n \ge N_0$, and suppose the forward consecutive scalar norm ratios satisfy
$$
 \lim_{n\to\infty} \frac{\|c_{n+1}\|_{\mathbb K}}{\|c_n\|_{\mathbb K}} = 0.
$$
Then $\sum_{n=0}^\infty \|p_n\| r^n < \infty$ for every $r \in \mathbb R_{\ge 0}$, and $\operatorname{radius}(p) = \infty$. Neither completeness of $A$ nor $\|1_A\| = 1$ is needed. [Lean, read]

**Proof.** For (1), $\Pi_0() = 1_A$ while the empty product of input norms equals $1$, so $\|\Pi_0\| = \|1_A\|$ and $\|p_0\| = \|c_0\|\,\|1_A\|$ (`norm_mkPiAlgebraFin_zero`, `ofScalars_norm_eq_mul`). When $n \ge 1$, the tuple $(m_0,\dots,m_{n-1})$ is nonempty; induction on $n \ge 1$ using $\|ab\| \le \|a\|\|b\|$ (`List.norm_prod_le'`) yields $\|m_0 \cdots m_{n-1}\| \le \prod_{i=0}^{n-1}\|m_i\|$ without invoking $1_A$. Thus $\|\Pi_n\| \le 1$ (`norm_mkPiAlgebraFin_le_of_pos`) and $\|p_n\| = \|c_n\|\,\|\Pi_n\| \le \|c_n\|$ (`ofScalars_norm_le`). If $\|1_A\| = 1$, testing $m = (1_A,\dots,1_A)$ gives $\|\Pi_n\| \ge 1$, hence $\|p_n\| = \|c_n\|$ for all $n \ge 0$.

For (2), fix $r \in \mathbb R_{\ge 0}$. If $r = 0$, then $\|p_n\| r^n = 0$ for all $n \ge 1$, so $\sum_{n\ge 0} \|p_n\| r^n = \|p_0\| < \infty$ (`OfScalars.lean:250–251`). Assume now $r > 0$, and define the scalar majorants $g_n(r) = \|c_n\|_{\mathbb K} r^n \ge 0$. Note the direction of the ratio: for every $n \ge N_0$, the hypothesis $c_n \ne 0$ and $r > 0$ force $g_n(r) > 0$, so we may divide legitimately by $g_n(r)$ and cancel $r^n$ (`tendsto_succ_norm_div_norm`, `:191–197`):
$$
 \frac{g_{n+1}(r)}{g_n(r)} = \frac{\|c_{n+1}\|_{\mathbb K}\,r^{n+1}}{\|c_n\|_{\mathbb K}\,r^n} = r\cdot\frac{\|c_{n+1}\|_{\mathbb K}}{\|c_n\|_{\mathbb K}} \xrightarrow[n\to\infty]{} r\cdot 0 = 0.
$$
(Equivalently, the reciprocal radius-oriented ratio $\|c_n\|/\|c_{n+1}\|$ tends to $+\infty$; requiring $\|c_n\|/\|c_{n+1}\| \to 0$ instead would force $g_{n+1}(r)/g_n(r) \to +\infty$ and collapse the radius to $0$, as in `ofScalars_radius_eq_zero_of_tendsto`.) Since $0 < 1/2 < 1$, there exists $N_1 \ge \max(1, N_0)$ such that $g_{n+1}(r)/g_n(r) \le 1/2$ for all $n \ge N_1$. Because $g_n(r) > 0$ for $n \ge N_1$, multiplying through by $g_n(r)$ yields $g_{n+1}(r) \le \frac{1}{2} g_n(r)$ (`summable_of_ratio_test_tendsto_lt_one`, `Normed.lean:649–655`), and induction on $k \ge 0$ (`le_geom`, `SpecificLimits/Basic.lean:248–251`) gives $g_{N_1+k}(r) \le g_{N_1}(r)\,2^{-k}$. Summing the geometric series $\sum_{k\ge 0} 2^{-k} = 2$ and restoring the finite prefix $0 \le n < N_1$ proves $\sum_{n\ge 0} g_n(r) < \infty$ (`summable_of_ratio_norm_eventually_le`). By part (1), $0 \le \|p_n\| r^n \le g_n(r)$ for every $n \ge 1$, i.e. off the finite set $\{0\}$ (`Summable.of_norm_bounded_eventually`, `OfScalars.lean:252–260`), so
$$
 \sum_{n=0}^\infty \|p_n\| r^n \le \|c_0\|_{\mathbb K}\,\|1_A\| + \sum_{n=1}^\infty g_n(r) < \infty.
$$
In particular, putting $C_r = \sum_{n=0}^\infty \|p_n\| r^n$, every term satisfies $\|p_n\| r^n \le C_r$, so $r \le \operatorname{radius}(p)$ (`le_radius_of_summable_norm`, `ConvergenceRadius.lean:233–235`). Since $r \in \mathbb R_{\ge 0}$ is arbitrary, $\operatorname{radius}(p) = \infty$ (`radius_eq_top_of_summable_norm`, `:264–266`). $\square$

**Lemma 2 (factorial ratio specialization, all-radius norm summability, and explicit uniform tail thresholds).**
1. (*General-field pinned theorem `expSeries_radius_eq_top`.*) Let $\mathbb K$ be a nontrivially normed field of characteristic zero with continuous $\mathbb Q$-scalar multiplication (`[CharZero 𝕂] [ContinuousSMul ℚ 𝕂]`), and let $A$ be a normed ring and normed $\mathbb K$-algebra. Then $\operatorname{expSeries}(\mathbb K, A)$ has convergence radius $\infty$, and $\sum_{n=0}^\infty \|((n!)^{-1} : \mathbb K)\cdot x^n\| < \infty$ for every $x \in A$. [Lean, read]
2. (*Quantitative uniform bounds and explicit non-circular thresholds.*) Suppose $\mathbb K \in \{\mathbb Q, \mathbb R, \mathbb C\}$ carries its standard Archimedean absolute value, and fix any radius $R \ge 0$. For every integer $N \ge \max(1, \lfloor R \rfloor)$ and every $x \in A$ with $\|x\| \le R$,
$$
 \sum_{n=N}^\infty \left\|\frac{x^n}{n!}\right\| \le \sum_{n=N}^\infty \frac{R^n}{n!} \le \frac{R^N}{N!}\cdot\frac{N+1}{N + 1 - R}.
$$
Moreover, put $K = \lfloor 2R \rfloor$ and $C_R = (2R)^K / K!$ (with $0^0 = 1$). Then $R^n / n! \le C_R\,2^{-n}$ for all $n \ge K$, and $\sum_{n=N}^\infty R^n / n! \le C_R\,2^{1-N}$ for all $N \ge \max(1, K)$. Consequently, for every $R \ge 0$ and $\varepsilon > 0$, the purely algebraic, logarithm-free integer threshold
$$
 N_{\mathrm{arch}}(R, \varepsilon) := \max\!\left(\lfloor 2R \rfloor,\ \left\lfloor \frac{C_R}{\varepsilon} \right\rfloor + 2\right) \ge 2
$$
(as well as the sharper dyadic threshold $N_{\mathrm{dyad}}(R,\varepsilon) = \max\bigl(1, \lfloor 2R \rfloor, 2 + \max(0, \lfloor \log_2(C_R/\varepsilon)\rfloor)\bigr)$ once $\log_2$ is available, and the minimal ratio cutoff $N_{\mathrm{ratio}}(R,\varepsilon) = \min\{N \ge \max(1,\lfloor R\rfloor) : \frac{R^N}{N!}\frac{N+1}{N+1-R} < \varepsilon\}$) satisfies, uniformly over all $x \in A$ with $\|x\| \le R$, all $N \ge N_{\mathrm{arch}}(R,\varepsilon)$, and all finite subsets $F \subset \{n \in \mathbb N : n \ge N\}$,
$$
 \left\|\sum_{n\in F} \frac{x^n}{n!}\right\| \le \sum_{n=N}^\infty \left\|\frac{x^n}{n!}\right\| \le \sum_{n=N}^\infty \frac{R^n}{n!} < \varepsilon.
$$
[Expository for the explicit thresholds] [Lean, read] for `expSeries_radius_eq_top` and `norm_expSeries_summable'`.

**Proof.** For (1), `expSeries_eq_ofScalars` (`Exponential.lean:111–112`) identifies $c_n = (n!)^{-1} \in \mathbb K$. Since $n! \ge 1$ in $\mathbb N$ and $\mathbb K$ has characteristic zero, $(n! : \mathbb K) \ne 0$ and hence $c_n \ne 0$ for every $n \ge 0$ (`:452, 460`). Using $(n+1)! = (n+1)n!$, the forward ratio simplifies to $\|c_{n+1}\|_{\mathbb K}/\|c_n\|_{\mathbb K} = \|((n+1) : \mathbb K)^{-1}\|_{\mathbb K}$ (`:455–456`). In $\mathbb Q_{\ge 0}$ with the order topology, Archimedean unboundedness of $\mathbb N$ gives $(n+1)^{-1} \to 0$ (`NNRat.tendsto_inv_atTop_nhds_zero_nat`), and `[ContinuousSMul ℚ 𝕂]` makes the canonical map $\mathbb Q_{\ge 0} \to \mathbb K$ continuous, so $((n+1) : \mathbb K)^{-1} \to 0$ and its norm tends to $0$ (`tendsto_inv_atTop_nhds_zero_nat`, `SpecificLimits/Basic.lean:35–48`; `Exponential.lean:457–459`). Lemma 1(2) gives $\operatorname{radius}(\operatorname{expSeries}(\mathbb K, A)) = \infty$. Thus every $x \in A$ satisfies $\operatorname{edist}(x,0) < \infty = \operatorname{radius}$, and the inside-ball evaluation lemma (`summable_norm_apply`, `Exponential.lean:275–285, 468–472`) gives $\sum_{n\ge 0}\|c_n x^n\| < \infty$.

For (2), whenever $n \ge 1$ and $\|x\| \le R$, nonempty submultiplicativity gives $\|x^n\| \le \|x\|^n \le R^n$, so $\|x^n/n!\| \le R^n/n!$. If $N \ge \max(1, \lfloor R \rfloor)$, then $N + 1 \ge \lfloor R \rfloor + 1 > R$, so $q = R/(N+1) \in [0, 1)$. For every $k \ge 0$, $(N+k)! = N!\prod_{j=1}^k(N+j) \ge N!(N+1)^k$, whence
$$
 \frac{R^{N+k}}{(N+k)!} \le \frac{R^N}{N!}\,q^k,\qquad
 \sum_{n=N}^\infty \frac{R^n}{n!} \le \frac{R^N}{N!}\sum_{k=0}^\infty q^k = \frac{R^N}{N!}\cdot\frac{N+1}{N + 1 - R}.
$$
Separating $n = 0$ (where $\|x^0/0!\| = \|1_A\|$) and setting $N_0 = \max(1, \lfloor 2R \rfloor)$ (where $q < 1/2$) already bounds the full norm sum by $\|1_A\| + \sum_{n=1}^{N_0-1} R^n/n! + 2 R^{N_0}/N_0! < \infty$. Next, for every $n \ge K = \lfloor 2R \rfloor$, each factor in $\prod_{j=K+1}^n (2R/j)$ satisfies $0 \le 2R/j \le 2R/(K+1) < 1$, so $(2R)^n/n! = C_R\prod_{j=K+1}^n(2R/j) \le C_R$. Multiplying by $2^{-n}$ gives $R^n/n! = 2^{-n}(2R)^n/n! \le C_R\,2^{-n}$, and summing over $n \ge N \ge \max(1, K)$ gives $\sum_{n=N}^\infty R^n/n! \le C_R\sum_{n=N}^\infty 2^{-n} = C_R\,2^{1-N}$. Finally, by induction (or the binomial expansion of $(1+1)^m$), $2^m \ge m + 1 > m$ for every $m \in \mathbb N$. If $N \ge N_{\mathrm{arch}}(R,\varepsilon)$, then $N \ge \max(1, K)$ and $m = N - 1 \ge \lfloor C_R/\varepsilon \rfloor + 1 > C_R/\varepsilon$, so $2^{N-1} > m > C_R/\varepsilon$, i.e. $C_R\,2^{1-N} < \varepsilon$. Notice that $N_{\mathrm{arch}}(R,\varepsilon)$ uses neither $\exp$ nor $\log$, avoiding any circularity when constructing $\exp$ itself; the dyadic and direct ratio cutoffs satisfy the same inequality by definition. $\square$

**Proposition 3 (how the uniform tail threshold supplies the Banach-algebra exponential consumers).** Let $A$ be a Banach algebra (`[NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]`, or over $\mathbb K \in \{\mathbb R, \mathbb C\}$ via rational scalar restriction).
1. (*Global value convergence, ball-uniform truncation error, and continuity.*) For every $x \in A$, the partial sums $E_N(x) = \sum_{n=0}^{N-1} x^n/n!$ converge in $A$ to $\exp(x)$, with uniform ball error $\|\exp(x) - E_N(x)\| \le \frac{R^N}{N!}\frac{N+1}{N+1-R} < \varepsilon$ for all $\|x\| \le R$ and $N \ge N_{\mathrm{arch}}(R,\varepsilon)$ (or $N_{\mathrm{ratio}}(R,\varepsilon)$). Consequently $\exp : A \to A$ is continuous everywhere (`expSeries_summable'`, `exp_continuous`).
2. (*Continuous ring homomorphisms and central scalars.*) If $B$ is a Banach $\mathbb Q$-algebra and $\varphi : A \to B$ is a continuous $\mathbb Q$-linear ring homomorphism, then $\varphi(\exp x) = \exp(\varphi x)$ for all $x \in A$ (`map_exp`). In particular, $\operatorname{algebraMap}_{\mathbb K,A}(\exp\zeta) = \exp(\zeta 1_A)$ for all $\zeta \in \mathbb K$ (`algebraMap_exp_comm`), and in a Banach $*$-algebra with continuous involution, $(\exp x)^* = \exp(x^*)$ (`star_exp`).
3. (*Global commuting addition, two-sided inverses, unitaries, and spectral/archive consumers.*) If $x, y \in A$ commute ($xy = yx$), then $\exp(x+y) = \exp(x)\exp(y)$ (`exp_add_of_commute`) regardless of how large $\|x\|$ and $\|y\|$ are. Hence $\exp(x)$ is invertible with two-sided inverse $\exp(-x)$ for every $x \in A$ (`invertibleExp`), and if $x^* = -x$ in a unital Banach $*$-algebra, then $\exp(x)$ is unitary (`exp_mem_unitary_of_mem_skewAdjoint`). [Lean, read]

**Proof.** (1) Fix $R \ge 0$ and $\|x\| \le R$. Given $\varepsilon > 0$, Lemma 2(2) implies that for every finite subset $F \subset \{n \in \mathbb N : n \ge N_{\mathrm{arch}}(R,\varepsilon)\}$, $\|\sum_{n\in F} x^n/n!\| < \varepsilon$. This is the finite-subset Cauchy criterion (`summable_iff_vanishing_norm`), so completeness of $A$ (`Summable.of_norm`) produces the unconditional sum $\exp(x) = \lim_{N\to\infty} E_N(x)$. Applying $\|\sum_{n=N}^{M-1} x^n/n!\| \le \sum_{n=N}^\infty R^n/n!$ and letting $M \to \infty$ gives the uniform ball remainder bound. Since each polynomial $E_N$ is continuous on $A$ and $E_N \to \exp$ uniformly on every ball $\overline{B}(0, R)$, $\exp$ is continuous on every open ball $B(0, R)$ and hence on all of $A$.

(2) Because $\varphi$ is a $\mathbb Q$-linear ring homomorphism, $\varphi(E_N(x)) = E_N(\varphi(x))$ for every $N \ge 1$. Put $R = \max(\|x\|_A, \|\varphi(x)\|_B)$. Given $\eta > 0$, continuity of $\varphi$ at $\exp(x)$ yields $\delta > 0$ such that $\|u - \exp(x)\|_A < \delta \implies \|\varphi(u) - \varphi(\exp(x))\|_B < \eta/2$. Taking $N = N_{\mathrm{arch}}(R, \min(\delta, \eta/2))$ gives both $\|E_N(x) - \exp(x)\|_A < \delta$ and $\|E_N(\varphi(x)) - \exp(\varphi(x))\|_B < \eta/2$, whence $\|\varphi(\exp x) - \exp(\varphi x)\|_B < \eta$. Letting $\eta \downarrow 0$ gives $\varphi(\exp x) = \exp(\varphi x)$ (applying this to $\operatorname{algebraMap}_{\mathbb K,A}$ and to the continuous conjugate-linear ring homomorphism $\operatorname{star}$ yields the scalar and adjoint identities).

(3) Let $xy = yx$ in $A$, and put $R = \|x\| + \|y\|$ (so $\|x\|, \|y\|, \|x+y\| \le R$) and $D_R = \|1_A\| + \sum_{n=1}^\infty R^n/n! < \infty$. Because $xy = yx$, the commuting binomial theorem identifies the degree-$n$ antidiagonal $\sum_{i+j=n} (x^i/i!)(y^j/j!)$ with $(x+y)^n/n!$. For any $M \ge 1$, the $M \times M$ product $E_M(x)E_M(y)$ sums $(x^i/i!)(y^j/j!)$ over $0 \le i,j < M$, which is contained in the triangle $i + j < 2M - 1$ whose antidiagonal sum is $E_{2M-1}(x+y)$. Bounding the omitted pairs $(i \ge M) \sqcup (i < M,\, j \ge M)$ by submultiplicativity gives
$$
 \bigl\|E_{2M-1}(x+y) - E_M(x)E_M(y)\bigr\| \le \left(\sum_{i=M}^\infty \frac{R^i}{i!}\right)D_R + D_R\left(\sum_{j=M}^\infty \frac{R^j}{j!}\right) = 2 D_R \sum_{n=M}^\infty \frac{R^n}{n!}.
$$
Given $\varepsilon > 0$, choose $M = N_{\mathrm{arch}}\!\bigl(R, \frac{\varepsilon}{3\max(1, D_R)}\bigr)$. Then $\|E_{2M-1}(x+y) - E_M(x)E_M(y)\| < 2\varepsilon/3$ while $\|E_{2M-1}(x+y) - \exp(x+y)\| \le \sum_{n\ge 2M-1} R^n/n! < \varepsilon/3$, so $\|\exp(x+y) - E_M(x)E_M(y)\| < \varepsilon$. Since multiplication in $A$ is continuous, $E_M(x)E_M(y) \to \exp(x)\exp(y)$ as $M \to \infty$, proving $\exp(x+y) = \exp(x)\exp(y)$. Setting $y = -x$ gives $\exp(x)\exp(-x) = \exp(-x)\exp(x) = \exp(0) = 1_A$, and if $x^* = -x$ then $(\exp x)^* = \exp(x^*) = \exp(-x) = (\exp x)^{-1}$.

In the downstream spectral chain (retained here by citation), `spectrum.exp_mem_exp` (`Analysis/Normed/Algebra/Spectrum.lean:374–400`) invokes Proposition 3(2)–(3) and (1) at arbitrary norm: `algebraMap_exp_comm z` and `exp_add_of_commute` factor $\exp(a) = \exp(a - z 1_A)e^z 1_A$ (`:378`), while `expSeries_summable'` peels off the unit term $\exp(a - z 1_A) = 1_A + (a - z 1_A)Q(a - z 1_A)$ (`:394`). That forward spectral inclusion, paired with `exp_mem_unitary_of_mem_skewAdjoint`, feeds `IsSelfAdjoint.mem_spectrum_eq_re` (`Analysis/CStarAlgebra/Spectrum.lean:173–185`) and the archive's spectral-reality call on $c = S^* S$ at `LConv.lean:154`. Separately, the archive calls `expSeries_radius_eq_top` directly in `NFRadRedR.lean:114–123` to place every $x \in A$ in the analyticity ball for $C^\infty$ smoothness of `NormedSpace.exp`, calls `norm_expSeries_summable'` on `Matrix.frobeniusNormedRing` in `SphericalL1StatementOfProjectors.lean:376` to prove $\|\exp X\|_F \le \sqrt{n}\,e^{\|X\|_F}$ without `NormOneClass`, and calls `expSeries_summable'` in `JacConstBHLie.lean:32` to commute matrix-vector evaluation with the infinite sum. $\square$ [Pinned global exponential wrappers](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Algebra/Exponential.lean#L468-L583) · [Pinned spectral-inclusion consumer](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Algebra/Spectrum.lean#L374-L400) · [Pinned self-adjoint reality consumer](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/CStarAlgebra/Spectrum.lean#L173-L195)

**Remarks and hypothesis-deletion boundary controls (why nonvanishing and vanishing ratios play distinct roles).**
1. *Deleting eventual nonvanishing $c_n \ne 0$: totalized division by zero versus finite or zero actual radius.* In Lean's real division, $y / 0 = 0$ by convention (`div_zero`), as noted explicitly in the docstring of `ofScalars_radius_eq_top_of_tendsto` (`OfScalars.lean:244–245`). Take the lacunary sequence $c_{2k} = 1$, $c_{2k+1} = 0$ on $M_2(\mathbb C)$ or $\mathcal B(\ell^2(\mathbb N_0))$. At even $n = 2k$, $|c_{2k+1}|/|c_{2k}| = 0/1 = 0$; at odd $n = 2k+1$, the totalized quotient is $|c_{2k+2}|/|c_{2k+1}| = 1/0 = 0$. Hence the formal sequence $n \mapsto \|c_{n+1}\|/\|c_n\|$ is identically $0$ and converges to $0$! Yet $\sum_{n\ge 0} c_n x^n = \sum_{k\ge 0} x^{2k}$ has $\|p_{2k}\| = 1$, so $\|p_n\| r^n$ is bounded if and only if $r \le 1$: the actual radius is $1 < \infty$ (diverging at $x = I$). Worse still, for $c_{2k} = k!$ and $c_{2k+1} = 0$, every totalized consecutive ratio is again $0$, whereas $k! r^{2k} \to +\infty$ for every $r > 0$ (for instance at $r = 1/10$, $275!\,(1/10)^{550} > 1$), giving actual radius $0$. Thus eventual nonvanishing is genuinely required to rule out zero denominators. (In `ofScalars_radius_eq_inv_of_tendsto_ENNReal` at `:290–309`, working in $\mathbb R_{\ge 0\infty}$ sets $x/0 = \infty$ for $x > 0$, which forces any sequence whose $\mathbb R_{\ge 0\infty}$-ratios tend to $0$ while taking infinitely many zeros to vanish identically from some index onward.)
2. *Deleting $\|c_{n+1}\|/\|c_n\| \to 0$ when the sufficient criterion fails, yet the actual radius is still $\infty$.* The ratio condition in Lemma 1(2) is **sufficient, not necessary**, for $\operatorname{radius}(p) = \infty$. Define strictly positive coefficients ($c_n > 0$ for every $n \ge 0$) by pairing adjacent even factorials:
$$
 c_{2k} = \frac{1}{(2k)!},\qquad c_{2k+1} = \frac{1}{(2k)!}\qquad (k \ge 0).
$$
Then $c_{2k+1}/c_{2k} = 1$ at every even index $n = 2k$, while $c_{2k+2}/c_{2k+1} = \frac{1}{(2k+1)(2k+2)} \to 0$ at odd indices $n = 2k+1$. Thus $\limsup_{n\to\infty} c_{n+1}/c_n = 1 \ne 0$: the limit does not exist, Lemma 1(2) fails to apply, and for every $r \ge 1$ the rescaled ratio $r\,c_{2k+1}/c_{2k} = r \ge 1$ never drops below $1$. Nevertheless, for **every** $r \ge 0$, grouping pairs gives
$$
 \sum_{n=0}^\infty c_n r^n = \sum_{k=0}^\infty \frac{r^{2k} + r^{2k+1}}{(2k)!} = (1 + r)\cosh(r) < \infty,
$$
so $\|p_n\| r^n \le c_n r^n$ ($n \ge 1$) is summable for all $r \ge 0$ and the actual radius is still $\operatorname{radius}(p) = \infty$! As Rudin emphasizes via Theorem 3.37 and Examples 3.35, oscillating consecutive ratios defeat the ratio test while the Cauchy–Hadamard root test $(c_n)^{1/n} \to 0$ still detects the infinite radius.
3. *Deleting $\|c_{n+1}\|/\|c_n\| \to 0$ when the actual radius becomes finite (Archimedean geometric series and $p$-adic exponentials).* Conversely, when consecutive ratios stay bounded away from zero along all indices—or when the Archimedean scalar continuity hypothesis `[ContinuousSMul ℚ 𝕂]` in Lemma 2(1) is dropped—the actual convergence radius becomes genuinely finite:
   - Over $\mathbb C$ on any normed algebra $A$ with $\|1_A\| = 1$, take $c_n = \rho^n$ with $\rho > 0$ (say $\rho = 2$). All $c_n > 0$, $|c_{n+1}|/|c_n| = 2 \ne 0$, $\|p_n\| = 2^n$, and $\|p_n\| r^n = (2r)^n$ is bounded if and only if $r \le 1/2$, so $\operatorname{radius}(p) = 1/2 < \infty$ (summing to $(1 - 2x)^{-1}$ at $\|x\| = 1/3$, while diverging at $x = \frac{1}{2}1_A$ where the general term has norm $1$).
   - Over the $p$-adic field $\mathbb K = \mathbb Q_p$ ($p$ prime), `[NontriviallyNormedField ℚ_p]` and `[CharZero ℚ_p]` both hold, so $c_n = (n!)^{-1} \ne 0$ for every $n \ge 0$; what fails in Lemma 2(1) is `[ContinuousSMul ℚ ℚ_p]`, because $(n+1)^{-1} \to 0$ in Archimedean $\mathbb Q$ does not imply $|(n+1)^{-1}|_p \to 0$. Indeed, along $n = p^k - 1$, $|c_{p^k}/c_{p^k-1}|_p = |p^{-k}|_p = p^k \to +\infty$, and Legendre's valuation formula $v_p(n!) = (n - s_p(n))/(p-1)$ (where $s_p(n)$ is the base-$p$ digit sum) gives $|(n!)^{-1}|_p^{1/n} = p^{(n - s_p(n))/((p-1)n)} \to p^{1/(p-1)} > 1$, so the $p$-adic exponential series has **finite** convergence radius $p^{-1/(p-1)} < 1$. [Expository]

**Scope and sources.** D'Alembert's 1768 *Mémoire XXXV* (§I, pp. 171–183, especially Art. 31, pp. 181–182) introduced geometric-ratio tail comparison and noted the eventual decay of factorial terms at arbitrary real arguments. Walter Rudin's *Principles of Mathematical Analysis* (3rd ed., 1976, Theorems 3.33–3.34, Examples 3.35, Theorem 3.37, Theorem 3.39, Example 3.40(b), pp. 65–70, and Chapter 8, eq. (25), p. 178) gives the modern ratio and root tests, oscillating failure examples, and the entire scalar exponential series; Ovidiu Costin's *Functional Analysis 7212* notes (2020, §1.0–§1.1, pp. 2–6) present the Banach-algebra exponential and commuting addition formula. In pinned Mathlib (`0df444a360eaa60ab8c11dca51a86af692955474`), `OfScalars.lean` is due to Edward Watine, `Exponential.lean` to Anatole Dedecker, Eric Wieser, and Yuyang Zhao, and the upstream multilinear-norm, convergence-radius, and ratio-test files to Sébastien Gouëzel, Yury Kudryashov, Sophie Morel, Patrick Massot, Johannes Hölzl, Dylan MacKenzie, and Heather Macbeth. Our non-circular threshold $N_{\mathrm{arch}}(R,\varepsilon)$, the coherent-block proof of the exact $\ell^2(\mathbb N_0)$ shift tail, the non-normal matrix comparison across operator and Frobenius norms, and the boundary classification are textbook exposition, with no claim of research priority on the classical theorems. Reverse exponential spectral inclusion, general holomorphic functional calculus, and the `[Open]` positive-width strip $I = [-\alpha,\alpha]$ nuclearity and $\alpha$-independence questions in Masullo's Chapters 10–12 remain completely untouched by this local reading. [Rudin 1976, pp. 65–70, 178](https://www.lehman.edu/faculty/rbettiol/lehman_teaching/2020mat320/baby_Rudin.pdf) · [Costin 2020, §§1.0–1.1, pp. 2–6](https://math.osu.edu/~costin.9/7212-2020/FA1.pdf) · [Source ledger](../sources/SOURCES.md#chapter-14-factorial-ratios-and-the-banach-exponential)

#### Differentiating the Banach exponential

The entire series gives $\exp A$ at every point of a Banach algebra. Differentiation requires a linear approximation that controls increments in all directions. In $(A+H)^3$ the terms linear in $H$ are $HA^2$, $AHA$ and $A^2H$. Each records a different position of the perturbation. Along $t\mapsto\exp(tA)$ the base point and increment are scalar multiples of $A$, so these placements give the same product.

**First calculation.** In $M_2(\mathbb C)$ with the Euclidean operator norm, let $N=E_{12}$, $H=E_{21}$ and $I=E_{11}+E_{22}$. Then $N^2=H^2=0$, $NH=E_{11}$, $HN=E_{22}$ and $NHN=N$. In particular $NN^\ast=E_{11}\ne E_{22}=N^\ast N$, so $N$ is non-normal. Put $M(t)=N+tH$. Because $M(t)^2=tI$, grouping even and odd degrees gives
$$
\exp M(t)=
\left(\sum_{k\ge0}\frac{t^k}{(2k)!}\right)I+
\left(\sum_{k\ge0}\frac{t^k}{(2k+1)!}\right)(N+tH).
$$
For $|t|\le1$, each scalar tail from $k=2$ has modulus at most $|t|^2$ times its factorial sum at $1$. The constant and linear coefficients give $\exp N=I+N$ and
$$
D\exp_N(H)=H+\frac I2+\frac N6,\qquad
(\exp N)H=H+E_{11},\qquad
D\exp_N(H)-(\exp N)H=\frac{E_{22}-E_{11}}2+\frac N6.
$$
The $(1,1)$ entry of the difference is $-1/2$. The surviving insertion sums are $H$, $NH+HN$ and $NHN$ in degrees $1,2,3$. In every higher degree, each insertion has at least two adjacent factors $N$ on one side of $H$ and vanishes.

**Second calculation.** In $\mathcal B(\ell^2(\mathbb N_0))$ with the operator norm, take the unilateral shift $Se_j=e_{j+1}$ and the projection $Pe_0=e_0$, $Pe_j=0$ for $j\ge1$. Both have norm one. The right factor acts first, so $PS=0$, while $SPe_0=e_1$. Thus $S^jPS^k=0$ for $k\ge1$, and $S^jP$ sends $e_0$ to $e_j$ and vanishes on its orthogonal complement. The insertion series below gives, for every $v=(v_j)_{j\ge0}$,
$$
D\exp_S(P)v=v_0\sum_{j\ge0}\frac{e_j}{(j+1)!},\qquad
(\exp S)Pv=v_0\sum_{j\ge0}\frac{e_j}{j!}.
$$
The error has first nonzero coordinate $-v_0/2$ at $e_1$. Its exact operator norm is $\bigl(\sum_{j\ge1}(j/(j+1)!)^2\bigr)^{1/2}\ge1/2$. The error maps $v$ to $v_0$ times a fixed vector, and its norm is attained at $e_0$. Every insertion degree contributes. [Expository]

**Definition.** Let $\mathcal A$ be an associative unital Banach algebra over $\mathbb K=\mathbb R$ or $\mathbb C$ with submultiplicative norm and the usual scalar norm. A Fréchet derivative of $f$ at $A$ is a continuous $\mathbb K$-linear map $L$ with $\|f(A+H)-f(A)-L(H)\|=o(\|H\|)$ as $H\to0$. The strict derivative asks for $f(B)-f(C)-L(B-C)=o(\|B-C\|)$ as $(B,C)\to(A,A)$. Write $X^n/n!$ for multiplication by the scalar reciprocal of $n!$. The norm of the unit may differ from one.

**Lemma (from a power series on a ball to a derivative).** Let $E,F$ be normed spaces over a nontrivially normed field and $p_n:E^n\to F$ continuous multilinear maps. Suppose $0<r\le\operatorname{radius}(p)$ and diagonal evaluations of $p$ sum to $f(x+h)$ for all $\|h\|<r$. This is `HasFPowerSeriesOnBall f p x r`. At the centre the strict derivative is the linear map $p_1$. If $F$ is complete and $\|a\|<r$, the derivative at $x+a$ is the first coefficient of the series recentered by $a$. [Lean, read]

*Proof.* Choose finite $0<b<s<r$. The strict-radius estimate supplies $\sum_n\|p_n\|s^n<\infty$. For $u,v$ of norm at most $b$, replace one slot at a time in $p_n(u,\ldots,u)-p_n(v,\ldots,v)$. Multilinearity gives $n$ terms with one slot $u-v$ and the others of norm at most $m=\max(\|u\|,\|v\|)$. Degrees zero and one in the difference of the value series give $0$ and $p_1(u-v)$. The rest has norm at most
$$
m\|u-v\|\sum_{n\ge2}n\|p_n\|b^{n-2}.
$$
The constant is finite since $n(b/s)^{n-2}$ is bounded. This proves strict differentiability at $x$ and ordinary differentiability by setting $v=0$. Both value sums are given in the premise, so completeness is unnecessary at the centre. The pinned proof uses a degree-weighted geometric series and passes from a two-point big-$O$ bound to little-$o$ at $(x,x)$. [Analytic/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Basic.lean#L775-L886) · [FDeriv/Analytic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean#L83-L111)

To change centre, reserve $k$ slots for the increment and fill the remaining $l=n-k$ slots with $a$, keeping their original order. Sum over the subsets of fixed slots, then over $l\ge0$. For $d>0$ with $\|a\|+d<r$, a partially applied $k$-linear map has norm at most $\|p_{k+l}\|\|a\|^l$. Weighting by $d^k$ and counting subsets gives
$$
\sum_{n\ge0}\|p_n\|\sum_{l=0}^n {n\choose l}\|a\|^l d^{n-l}
=\sum_{n\ge0}\|p_n\|(\|a\|+d)^n<\infty.
$$
For fixed $k$, divide by $d^k>0$ to obtain summable norms for its coefficient. Completeness of $F$ gives completeness of the map space and hence the coefficient sum. This majorant bounds the weighted coefficient norms at every such $d$, giving radius at least $r-\|a\|$. For $\|h\|<r-\|a\|$, choose such a $d>\|h\|$. Absolute summability allows grouping evaluations by $k$ or by original degree $n$ and subset of fixed slots. Grouped by $n$ the inner sum is $p_n(a+h,\ldots,a+h)$ by multilinearity. Grouped by $k$ it gives the new series. Apply the centre result at $x+a$. Lean uses `changeOriginIndexEquiv`, `changeOriginSeries_summable_aux₁`, `changeOrigin_eval` and `HasFPowerSeriesOnBall.changeOrigin`. The derivative theorem curries the single remaining slot into a continuous linear map. [ChangeOrigin.lean, lines 118–226](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/ChangeOrigin.lean#L118-L226) · [ChangeOrigin.lean, lines 248–341](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/ChangeOrigin.lean#L248-L341) · [FDeriv/Analytic.lean, lines 193–208](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean#L193-L208)

**Proposition (ordered derivative and effective bounds).** For every $A,H\in\mathcal A$,
$$
D\exp_A(H)=\sum_{n\ge1}\frac1{n!}\sum_{j=0}^{n-1}A^jHA^{n-1-j}.
$$
Let $L_A^{(N)}$ be the sum through degree $N\ge1$ and $T_N(R)=\sum_{m\ge N}R^m/m!$. For all $R,\delta\ge0$, $\|A\|\le R$ and $\|H\|\le\delta$,
$$
\begin{aligned}
\|D\exp_A\|_{\mathrm{op}}&\le e^R,\\
\|D\exp_A-L_A^{(N)}\|_{\mathrm{op}}&\le T_N(R),\\
\|\exp(A+H)-\exp A-D\exp_A(H)\|&\le\tfrac12 e^{R+\delta}\|H\|^2,\\
\|\exp(A+H)-\exp A-L_A^{(N)}(H)\|&\le
\tfrac12 e^{R+\delta}\|H\|^2+T_N(R)\|H\|.
\end{aligned}
$$
For $N+1>R$, the preceding factorial estimate gives $T_N(R)\le(R^N/N!)(N+1)/(N+1-R)$. The dyadic bound there gives a cutoff for any positive tolerance. To bound $e^{R+\delta}$ above by a rational, choose rational $b\ge R+\delta$ and integer $J\ge1$ with $J+1>b$. Use the finite sum through degree $J-1$ at $b$ plus its rational tail bound. [Al-Mohy and Higham, 2009, Theorems 3.1–3.2, pp. 1642–1643](https://eprints.maths.manchester.ac.uk/1218/1/covered/MIMS_ep2008_26.pdf) · [Factorial tail](#factorial-ratios-and-the-infinite-radius-of-the-banach-exponential)

*Proof.* `NormedSpace.expSeries` uses the ordered product map with coefficient $1/n!$. `NormedSpace.exp_hasFPowerSeriesOnBall` packages the sum on the full extended ball about zero using the infinite radius. Set $k=1$ in the change of centre. The complement of the fixed slots is a singleton, say slot $j$, giving the word $A^jHA^{n-1-j}$. The ball derivative theorem identifies its summed first coefficient with $D\exp_A(H)$. [Ordered coefficient](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Algebra/Exponential.lean#L101-L112) · [Global ball](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Algebra/Exponential.lean#L478-L499) · [Ball derivative](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean#L193-L208)

Each insertion is a product of $n$ actual factors with norm at most $\|A\|^{n-1}\|H\|$. An exponent zero contributes no factors, so it incurs no factor $\|1\|$. Including degree one, the degree-$n$ linear operator has norm at most $\|A\|^{n-1}/(n-1)!$. Use $0^0=1$ in scalar majorants. Completeness gives absolute convergence in operator norm. Summing and truncating this bound give the first two estimates.

In $(A+H)^n$ the word with no $H$ cancels against $A^n$, and words with one $H$ give the insertion sum. A word with $k\ge2$ copies of $H$ has norm at most $\|H\|^k\|A\|^{n-k}$, and there are $\binom{n}{k}$ of them. Writing $l=n-k$ in the nonnegative majorant gives
$$
\sum_{n\ge2}\sum_{k=2}^n\frac{\binom{n}{k}}{n!}\|A\|^{n-k}\|H\|^k
=e^{\|A\|}\sum_{k\ge2}\frac{\|H\|^k}{k!}
\le\tfrac12\|H\|^2 e^{\|A\|+\|H\|}.
$$
Here $k!\ge2(k-2)!$. Subtract finite prefixes and take norm limits to obtain the remainder, including at $H=0$. Dividing by $\|H\|$ for $H\ne0$ also proves the Fréchet limit directly. Adding the derivative tail gives the last inequality. [Expository]

**Commuting directions and exponential paths.** If $AH=HA$, all $n$ insertions in degree $n$ are $A^{n-1}H$. Since $n/n!=1/(n-1)!$, continuity of multiplication gives
$$
D\exp_A(H)=(\exp A)H=H(\exp A).
$$
The two calculations show that deleting commutation invalidates the general simplification. Equality at a single pair can occur even when $AH\ne HA$. Choose $y\in(2\pi,5\pi/2)$ with $y\cot y=1+\log(y/\sin y)$. The difference of the two sides tends to $+\infty$ on the left and is negative on the right, so such a $y$ exists. Put $z=\log(y/\sin y)+iy$, which gives $e^z=1+z$. At $A=\operatorname{diag}(0,z)$ and $H=E_{12}$, only $j=0$ contributes to each degree. Thus $D\exp_A(H)=((e^z-1)/z)H=H=(\exp A)H$, although $AH=0$ and $HA=zH\ne0$.

The derivative of $t\mapsto tA$ in scalar direction $u$ is $uA$. Since $(tA)A=A(tA)$, the scalar derivative of $t\mapsto\exp(tA)$ is $(\exp(tA))A=A\exp(tA)$ for every $t\in\mathbb K$. The real statement applies to a complex algebra by restriction of scalars. The pinned `hasFDerivAt_exp_smul_const_of_mem_ball` composes the identity derivative at zero with the scalar line, then translates using $\exp((t+h)A)=\exp(tA)\exp(hA)$ for small $h$. Its strict version identifies that derivative by uniqueness with the strict derivative of the analytic composite. `hasDerivAt_exp_smul_const` and its primed version use the infinite radius and place the generator on the right and left, respectively. The separate theorem `hasFDerivAt_exp` assumes a commutative algebra. [Zero and commutative proofs](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Exponential.lean#L65-L118) · [Path proof](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Exponential.lean#L248-L335) · [Global path declarations](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Exponential.lean#L370-L389)

**Integral form.** Higham gives the matrix formula with the exponential factors on opposite sides of the direction. In a Banach algebra the continuous integrand on the compact real interval has a norm-valued integral. The ordered product series for $\exp((1-s)A)H\exp(sA)$ converges uniformly there, since each $(j,k)$ term has norm at most $\|A\|^{j+k}\|H\|/(j!k!)$, including when either power is zero. Integration by parts yields $\int_0^1(1-s)^js^k\,ds=j!k!/(j+k+1)!$. At $j=0$ the integral is $1/(k+1)$, and for $j>0$ it is $j/(k+1)$ times the integral with indices $(j-1,k+1)$. Integrate term by term and group by $j+k+1$ to get
$$
D\exp_A(H)=\int_0^1\exp((1-s)A)H\exp(sA)\,ds.
$$
The integral is a textbook corollary. The pinned production chain uses the recentered coefficient. Its exponential-specific file discusses an integral approach in a comment. [Higham, *What Is a Fréchet Derivative?*, 23 June 2020](https://nhigham.com/2020/06/23/what-is-a-frechet-derivative/) · [Pinned comment](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Exponential.lean#L219-L235)

**Hypotheses and the chapter's interfaces.** To test the strict ball inequality, take $1/(1-x)$ for $|x|<1$ and assign value zero elsewhere. Its geometric series represents it on the open unit ball, and the function is discontinuous at $1$. To test completeness, equip $\mathbb R[X]$ with the sup norm on $[0,1]$. The exponential series at $X$ has summable norms and its uniform limit is $e^x$. No polynomial equals that function, by repeated differentiation on $(0,1)$. Characteristic zero keeps scalar factorials nonzero. Beyond $\mathbb R,\mathbb C$, the pinned entire-radius supplier also assumes continuous rational scalar multiplication. The inherited ratio test requires eventual nonvanishing because field division is totalized. For coefficients $1,0,1,0,\ldots$, every consecutive quotient is zero under that convention, while the scalar radius is one. [Scalar ratio premise](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/OfScalars.lean#L243-L260) · [Exponential radius hypotheses](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Algebra/Exponential.lean#L443-L499)

For self-adjoint $a$ in a unital complex $C^\ast$-algebra, the path computation gives $U'(t)=U(t)\,ia$ for $U(t)=\exp(ita)$ and real $t$. The real-spectrum argument uses unitarity, forward spectral inclusion and the unit-circle norm constraint. For each spectral $\lambda$ these give $|e^{it\lambda}|=1$, so $t=1$ suffices to deduce $\operatorname{Im}\lambda=0$. A2's `LConv.lean:154` invokes spectral reality on $S^\ast S$. There are direct differentiation consumers elsewhere. `OneParam.lean:118–142` uses the path derivative to make $F(t)\exp(-tA)$ constant. `JacBaseA.lean:20–43,245–265` uses existence of the ambient Fréchet derivative and its value at zero in a matrix coordinate argument. The expanded ordered formula and the quantitative estimates serve as textbook background, with zero direct A2 calls identified for those expressions. Masullo's positive-width strip trace questions remain [Open]. [Pinned forward inclusion](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Algebra/Spectrum.lean#L374-L400) · [Pinned spectral reality](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/CStarAlgebra/Spectrum.lean#L173-L195) · [Source ledger](../sources/SOURCES.md#chapter-14-differentiating-the-banach-exponential)

#### The logarithm of a near-identity unitary matrix

Given a matrix $g$ that preserves a Hermitian form, can we write $g=\exp X$ with $X$ in the Lie algebra of that form? When $g$ is close to the identity, the series for $\log(1+y)$ with $y=g-I$ gives such an $X$. The proof needs only the closed algebra generated by this one increment. A second matrix generally generates a different algebra. The [exponential derivative above](#differentiating-the-banach-exponential) gives the product derivative inside this commutative algebra. The real-spectrum result discussed there is background.

**First calculation.** Use the Frobenius norm on $M_2(\mathbb C)$. Take $D=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$, $\theta=2\arctan(1/20)$, and put
$$
c=\cos\theta=\frac{399}{401},\qquad s=\sin\theta=\frac{40}{401},\qquad
U=cI+isD.
$$
Then $D^2=I$ and $U^\ast U=(c^2+s^2)I=I$. For $z=c+is$ the squared distance to $1$ is $|z-1|^2=2(1-c)=4/401$. Consequently $\|U-I\|_F^2=8/401<1/16$. The degree-$n$ term of the logarithm is $(-1)^{n-1}\operatorname{diag}((z-1)^n,(\bar z-1)^n)/n$. To sum it, put $\ell(z)=\sum_{n\ge1}(-1)^{n-1}(z-1)^n/n$ on $|z-1|<1$. Termwise differentiation there gives $\ell'(z)=1/z$ by the geometric series. The arc $e^{it}$ for $-\theta\le t\le\theta$ lies in this disk, since $|e^{it}-1|=2|\sin(t/2)|\le 2/20$. Along it, $(d/dt)\ell(e^{it})=i$ and $\ell(1)=0$. Thus the two diagonal entries sum to $i\theta$ and $-i\theta$. In particular $X=i\theta D$ satisfies $X^\ast=-X$, $\exp X=U$ by the even and odd exponential series, and $\|X\|_F=\sqrt{2}\theta<\sqrt 2/10$. With $r=\sqrt{8/401}$ the bound after degree $N$ is $r^{N+1}/((N+1)(1-r))$, as proved below.

**Second calculation.** Keep $U$ and put $S=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $K=DS=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, and $V=cI+isS$. Now $S^2=I$, $SD=-K$, and $K^2=-I$. The projections $(I+S)/2$ and $(I-S)/2$ give $V=(c+is)(I+S)/2+(c-is)(I-S)/2$. Their product is zero, so every power of $V-I$ splits into the two scalar powers. Therefore $\log V=i\theta S$, and $\|V-I\|_F^2=8/401$. Multiplying in both orders gives
$$
UV=c^2 I+ics(D+S)-s^2K,\qquad
VU=c^2 I+ics(D+S)+s^2K .
$$
The product $UV$ is unitary and has trace $2c^2$. Expanding $\operatorname{tr}((UV-I)^\ast(UV-I))$ gives $\|UV-I\|_F^2=4(1-c^2)=4s^2<1/16$. Thus all three series are in the archive's ball.

For the product series put $W=ics(D+S)-s^2K$. The identities $(D+S)^2=2I$ and $(D+S)K+K(D+S)=0$ give $W^2=-(2c^2s^2+s^4)I=-(1-c^4)I$. Also $W^\ast=-W$. Take $\alpha=\arccos(c^2)\in(0,\pi/2)$ and $B=W/\sin\alpha$. Then $B^2=-I$, and $(I\mp iB)/2$ are complementary projections with $B$ acting by $\pm i$. On them $UV=c^2 I+\sin\alpha\,B$ acts by $e^{\pm i\alpha}$. For $|t|\le\alpha$ we have $|e^{it}-1|\le \sqrt{2(1-c^2)}=\sqrt{2}\,s<1$, so the same scalar arc sum applies to both projections. The degree-$n$ matrix terms split as in the first calculation and sum to
$$
\log(UV)=\alpha B=\frac{\alpha}{\sin\alpha}\bigl(ics(D+S)-s^2K\bigr).
$$
In $\log U+\log V=i\theta(D+S)$ the off-diagonal entries are equal. In $\log(UV)$ their difference is $-2\alpha s^2/\sin\alpha\ne 0$. Each logarithm is computed inside the algebra of its own generator. The two generators fail to commute, with $UV-VU=-2s^2K$. [Expository]

**Definition.** Let $A$ be a unital complex Banach algebra with submultiplicative norm. The unit can have norm different from one. For $y\in A$, set $r=\|y\|$. On $r<1$ define
$$
L(y)=\operatorname{logS}y=\sum_{k\ge0}\frac{(-1)^k}{k+1}\,y^{k+1},\qquad
L_N(y)=\sum_{n=1}^N\frac{(-1)^{n-1}}{n}\,y^n .
$$
Here $N$ is any nonnegative integer and $L_0=0$. We write $\log g=L(g-1)$ on $\|g-1\|<1$. For the archive take $A=M_m(\mathbb C)$ with $\|a\|_F=(\sum_{i,j}|a_{ij}|^2)^{1/2}$, the norm called $\operatorname{hsn}$, and $J=J_m(\varepsilon)$, the diagonal matrix of signs specified by $\varepsilon:\operatorname{Fin}(m)\to\{\mathrm{true},\mathrm{false}\}$. Matrix star is conjugate transpose. A $J$-unitary $g$ satisfies $g^\ast Jg=J$ and a $J$-skew-adjoint $X$ satisfies $X^\ast J+JX=0$. The Frobenius norm is submultiplicative by Cauchy–Schwarz in each entry of a product followed by summation over the row and column indices. This matrix algebra is complete by finite dimensionality. In particular $\|I\|_F=\sqrt m$.

**Lemma (absolute convergence and finite truncation).** For all $r<1$ the series for $L(y)$ converges absolutely. Its norm and the tail after degree $N$ satisfy
$$
\|L(y)\|\le \frac r{1-r},\qquad
\|L(y)-L_N(y)\|\le \frac{r^{N+1}}{(N+1)(1-r)}.
$$
For $r\le1/4$, the two bounds are at most $4r/3$ and $4r^{N+1}/(3(N+1))$. In particular the uniform tail on that ball is at most $1/(3(N+1)4^N)$.

*Proof.* The degree-$n$ term has norm at most $r^n/n$ by submultiplicativity for $n\ge1$. Compare the full sum with $\sum_{n\ge1}r^n$ and the tail with $(N+1)^{-1}\sum_{n\ge N+1}r^n$. Completeness provides the limits. The constant term is absent, so the comparison uses no norm bound on the unit. The archive uses the first of these estimates in `norm_logS_le` and `norm_logS_le'`. The tail estimate is a textbook consequence of the same comparison.

**Lemma (local inverse in the generated algebra).** For $\|y\|\le1/4$ one has $\exp L(y)=1+y$. If also $\|(1+y)^{-1}-1\|\le1/4$, then $\log((1+y)^{-1})=-L(y)$. For $\|X\|\le1/3$ and $\|\exp X-1\|\le1/4$, one has $L(\exp X-1)=X$.

*Proof.* Write $A_y=\overline{\mathbb C[y]}$, the norm closure of all polynomials in $y$ including constants. Polynomials commute. The continuity of multiplication makes the closure a commutative algebra with the inherited norm, and closedness makes it complete. The unital inclusion is an isometric algebra homomorphism. Finite sums of powers map to the same sums in $A$. Continuity therefore transports both the local logarithm and the entire exponential. This is the role of `Algebra.elemental`, `map_logS` and `map_exp_of_mem_ball` in the archive.

Work inside $A_y$. On the complex disk $|t|<2$, define
$$
F(t)=\sum_{k\ge0} g_k(t),\qquad g_k(t)=\frac{(-1)^kt^{k+1}}{k+1}\,y^{k+1}.
$$
Then $g_k'(t)=(-t)^k y^{k+1}$ and $\|g_k'(t)\|\le r(2r)^k\le (1/4)2^{-k}$. All terms vanish at zero. The summable derivative majorant gives uniform convergence of the derivatives. To see the passage to the limit, integrate the finite derivative sums along the line from $0$ to $t$ to obtain the uniform Cauchy estimate for the values. Integrate again along the segment from $t$ to $t+h$ and pass to the limit in the finite sums. After division by $h$ the difference quotient is the mean of the limiting derivatives on that segment, which tends to their value at $t$ by continuity. This proves $F'(t)=\sum_k g_k'(t)$. The same argument on each smaller closed disk justifies the scalar differentiation in the first calculation.

Set $q=-ty$. Its norm is less than $1$ since $|t|<2$ and $r\le1/4$. For the geometric sum, both $(\sum_{k=0}^M q^k)(1-q)$ and $(1-q)(\sum_{k=0}^M q^k)$ are $1-q^{M+1}$. The terms with positive degree have summable norms and the degree-zero term is the unit. Take limits to get a two-sided inverse in $A_y$. Since $g_k'(t)=q^k y$, continuity of multiplication gives $F'(t)=(\sum_{k\ge0}q^k)y$. The factor $y$ commutes with $1+ty$, giving $F'(t)(1+ty)=y$. Define $G(t)=\exp(-F(t))(1+ty)$. The commutative exponential derivative and the product rule yield
$$
G'(t)=\exp(-F(t))\bigl[-F'(t)(1+ty)+y\bigr]=0 .
$$
Integrating on the segment from $0$ to $1$ gives $G(1)=G(0)=1$. Since $F(1)=L(y)$, multiplication by $\exp L(y)$ gives the claimed identity. The radius $2$ gives a single geometric majorant on an open disk containing both evaluation points. The archive’s $1/4$ gives both the derivative majorant here and the $1/3$ bound on each logarithm in the inverse calculation.

For the inverse and the reverse composition, first suppose $\|b\|\le2/3$ and $\exp b=1$. The exponential remainder estimate follows by discarding degrees zero and one. With $a=\|b\|$ we have
$$
a=\|\exp b-1-b\|\le e^a-1-a\le\sum_{n\ge2}\frac{a^n}{2^{n-1}}
=\frac{a^2}{2-a}\le a^2 .
$$
The factorial inequality $n!\ge 2^{n-1}$ holds for $n\ge2$. Since $a<1$, the bound forces $a=0$. This works even in a noncommutative algebra. The archive uses its exponential remainder lemma and a real exponential estimate to obtain the same vanishing. Thus if $P,Q$ commute, $\exp P=\exp Q$, and $\|P-Q\|\le2/3$, the commuting addition rule gives $\exp(P-Q)=1$, hence $P=Q$.

Put $w=(1+y)^{-1}=\sum_{k\ge0}(-y)^k\in A_y$. With both small-ball bounds, the exponentials of $L(y)$ and $L(w-1)$ multiply to $1$. These logarithms commute and their norms are at most $1/3$ each. Their sum has norm at most $2/3$ and therefore vanishes. For the reverse composition work in $A_X=\overline{\mathbb C[X]}$. Both $y=\exp X-1$ and $L(y)$ belong to it, and $\exp L(y)=\exp X$. The commuting uniqueness test applies since $\|L(y)-X\|\le2/3$. Both assertions pass to the original algebra by inclusion. [Lean, read for `exp_logS_comm`, `eq_zero_of_exp_eq_one` and `logS_inv`; the reverse composition is a textbook corollary]

The reverse composition applies on an actual neighborhood of zero. For $\|X\|\le1/5$, the positive-degree exponential terms give $\|\exp X-1\|\le e^{\|X\|}-1\le \|X\|/(1-\|X\|)\le1/4$. More precisely, $y\mapsto L(y)$ on $\|y\|\le1/4$ is bijective onto $\{X:\|X\|\le1/3,\ \|\exp X-1\|\le1/4\}$ with inverse $X\mapsto\exp X-1$. The maps are continuous there by uniform convergence of their series on the stated norm balls.

**Proposition (the archive's `LogNear`).** For every $m$, $\varepsilon$, and real $\delta\le1/4$, if $g^\ast Jg=J$ and $\|g-I\|_F\le\delta$, then $X=L(g-I)$ satisfies
$$
X^\ast J+JX=0,\qquad \|X\|_F\le\frac43\|g-I\|_F\le2\delta,\qquad \exp X=g .
$$
For $J=I$ this is the usual skew-adjoint logarithm of a unitary matrix.

*Proof.* Define $T(a)=Ja^\ast J$. The diagonal entries of $J$ are real signs, so $J^\ast=J$ and $J^2=I$. In the Frobenius norm, $T$ is an isometry because its entries are the conjugated and transposed entries of $a$ times signs. The operation is additive and conjugate-linear. For a word $a_1\cdots a_n$ its image is
$$
J a_n^\ast\cdots a_1^\ast J=(Ja_n^\ast J)\cdots(Ja_1^\ast J).
$$
The right-hand side contracts the adjacent pairs of $J$'s. For a repeated letter it gives $T(y^n)=T(y)^n$, and $T(I)=I$. Each logarithm coefficient is real, so $T(L_N(y))=L_N(T(y))$. Convergence on both sides and continuity of $T$ give $T(L(y))=L(T(y))$. The same word calculation transports the exponential series wherever it is used.

From $g^\ast Jg=J$ we get $T(g)g=I$. The geometric series already gives a two-sided inverse for $g=I+y$ in $A_y$, so $T(g)=g^{-1}$ by multiplication on the right by that inverse. In particular $T(y)=g^{-1}-I$ lies in this same generated algebra and has norm exactly $r$. Both arguments of the inverse formula lie in the required $1/4$ ball. Thus $T(X)=L(T(y))=-X$. Multiplying on the left by $J$ gives $X^\ast J=-JX$. The convergence bound and $0\le r\le\delta$ give the displayed norm estimate. The first inverse identity gives the exponential value in the ambient matrix algebra. [Lean, read]

**A mixed-sign witness.** With $J=\operatorname{diag}(1,-1)$ and the same $S$ as above, set $\beta=\log(21/19)$ and $g=(401I+40S)/399$. Since $JS=-SJ$ and $401^2-40^2=399^2$, $g^\ast Jg=J$. Its squared Frobenius distance is $3208/159201<1/16$. The projections $(I\pm S)/2$ split $g$ into the positive scalars $21/19$ and $19/21$. The line segments from $1$ to these scalars lie in the disk of the scalar series. Integrating $\ell'(z)=1/z$ on them evaluates the logarithms to $\beta,-\beta$. Therefore $L(g-I)=\beta S$ and $J(\beta S)^\ast J=-\beta S$. This example is Hermitian in the ordinary sense and verifies the mixed-sign assertion with a nonzero logarithm.

**Boundary tests.** If one drops the small-ball requirement entirely, $g=-I$ is unitary but the degree-$n$ term of $L(g-I)$ equals $-2^nI/n$, which fails the term test. There is a skew-adjoint logarithm $i\pi I$ of this matrix. The divergence concerns the series recipe. Also $\exp(2\pi i I)=I$ while $L(0)=0$, so an unrestricted reverse composition would fail on a series input at the identity. If one drops preservation of the form, $g=\operatorname{diag}(9/8,1)$ has distance $1/8$ and a logarithm $\operatorname{diag}(\log(9/8),0)$, obtained by integrating the scalar derivative from $1$ to $9/8$. Its first entry is positive. For $J=I$ this is a nonzero self-adjoint logarithm. The exponential–logarithm identities already hold for this input independently of the form condition.

**Actual use in A2.** The proof bodies are in `UnitaryNearIdentityEqExpLogBound.lean:12–294`. At lines 151 and 273 the commutative exponential–logarithm lemma is used for the inverse formula and the constructed elemental algebra, respectively. The statement wrapper at `UnitaryNearIdentityEqExpLogBoundStatement.lean:9–10` exports `GlobalTheory.T.unitary_near_identity_eq_exp_log_bound`. `BranchVol.lean:93–107` passes it as the `LogNear` argument of `formalDegree_le_of_neighbourhoodVolume`. In `FormalDegreeLeOfNeighbourhoodVolume.lean:100–139`, the local log is used at $\delta=1/(4c)$ with $c=(8mB)^2\ge1$. Its Lie algebra membership and bound let the lowest-$K$-type derivative estimate give $\|dR(\pi)(X)v_0\|\le c(2\delta)=1/2$. The orbit estimate then bounds the displacement, which bounds the matrix coefficient below in modulus by $1/2$ on the neighborhood. This is a formal-degree application. Masullo's positive-width strip nuclearity and trace independence have status [Open]. [Source ledger](../sources/SOURCES.md#chapter-14-the-logarithm-of-a-near-identity-unitary-matrix)

**Attribution.** The von Neumann series supplies the classical inverse construction. Costin records it and the Banach-algebra series identity $\exp(\log g)=g$ for $\|g-1\|<1$. Lawson gives local exponential–logarithm coordinates for matrix groups. Higham, D. S. Mackey, N. Mackey and Tisseur give the adjoint and inverse conventions for automorphism groups of sesquilinear forms. Higham and Lin give the matrix principal logarithm under the spectral condition of avoiding the closed negative real axis. Loring gives skew-Hermitian logarithms of ordinary unitary matrices for arbitrary unitary spectrum via an angular branch. The chapter follows the archive's local proof with its own Frobenius constants, gives an explicit series tail, and checks the examples directly. [Costin, Proposition 1.0.3 and Lemma 1.1.1](https://math.osu.edu/~costin.9/7212-2020/FA1.pdf) · [Higham and Lin, §3.1.6](https://eprints.maths.manchester.ac.uk/2067/) · [Loring, §1](https://arxiv.org/abs/1203.6151) · [Lawson, §§2.5 and 3.2](https://www.math.lsu.edu/~lawson/liecontrol.pdf) · [Higham–Mackey–Mackey–Tisseur, §2](https://eprints.maths.manchester.ac.uk/47/2/paper.pdf)

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
| Ch. 14 Complements, Appendices A–E & Bibliography | pp. 523–940 | Zero-multiplicity bounds & Mordell CM curves (`§14.1` pp. 524–533), **breakdown over $\mathbb F_q(X)$ (`§14.2` pp. 534–536)**, higher rank (`§14.3` p. 536), Appendices A–E (`pp. 537–932`, `App. B` explicit formulas `pp. 587–654`), and Bibliography (`pp. 933–940`). | Apps. A, C, D in Wave 1; App. B in Wave 2 (`§B.4` local normalizations under review) `[Community]` `[Open]` |

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
