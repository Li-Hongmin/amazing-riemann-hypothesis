# Chapter 1. The statement and its fidelity

> Sources as of 2026-11-21, 04:00–04:42 UTC. Archive sha256 `9631b4f0…9c7fc`;
> Mathlib at commit `0df444a` (tag v4.33.1). See `sources/SOURCES.md`.

Before asking whether a formal proof is correct, one has to ask what it proves. Kevin Buzzard
put the point this way in a blog post of 12 November 2026: "The first question which one has to ask
when judging a pdf which comes with some Lean code is: 'what is the statement of the theorem in
the Lean code, and does this correspond to the actual theorem statement in the pdf?'" [Community;
Xena blog, 2026-11-12]. Here there is no pdf, so the question becomes: do the five Lean
statements at the end of the archive say what mathematicians mean by the Riemann hypothesis and
by the generalized Riemann hypothesis for Dirichlet L-functions?

This chapter answers that question as completely as we can. Section 1.1 reads the top-level
file.
Sections 1.2 and 1.3 unpack the Mathlib definitions on which the statements rest and explain why
they are the classical objects. Section 1.4 shows that all five theorems reduce, inside the
archive and using only Mathlib, to a single half-plane statement. Section 1.5 explains what kind
of guarantee a Lean proof gives and what the archive does that a reader should know about.
Section 1.6 records the public verification status, and Section 1.7 says what a complete pass
would and would not establish. Section 1.8 sets Masullo's intended statement beside the Lean one.

## 1.1 The final file

The archive's top-level file, `src/Main.lean`, is twelve lines long [Lean, read]
(`src/Main.lean:1`):

```lean
import Statements
import Supplements.Kernels.MainTheoremsAll

theorem riemannHypothesis : RiemannHypothesis := rhOfAll

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

A Lean `theorem t : P := e` asserts that the term `e` has type `P`, that is, that `e` is a proof
of the proposition `P`; the kernel checks this when the declaration is added. The five types
to the right of the colons are the statements. Everything to the right of `:=` is proof, and
for the question of this chapter it does not matter how it was found.

Of the five statement constants, `RiemannHypothesis` is defined in Mathlib, the community library
on which the archive builds; the other four are defined in the archive's file `src/Statements.lean`,
which imports Mathlib and nothing else [Lean, read] (`src/Statements.lean:1`). So the meaning of
the five theorems depends only on Mathlib and on sixteen lines of `src/Statements.lean`. No other file
of the archive can change it: a Lean environment never contains two declarations with the same
name, so no file can supply a second, different `RiemannHypothesis` or `DirichletLZerosOnLine`,
and a declaration, once added, is immutable [Expository]. (Whether the compiled environment really contains
Mathlib's and `src/Statements.lean`'s definitions unchanged is what `lake comparator` checks
mechanically, by comparing the statement constants of the proof's export with those of a
separately built "challenge" file that imports only Mathlib; see Section 1.6.)

The proofs are four names defined in `Supplements/Kernels/MainTheorems.lean`, which
`src/Main.lean` imports through `MainTheoremsAll` and `MainTheoremsCritical` [Lean, read]
(`src/Supplements/Kernels/MainTheorems.lean:7`, `:9`, `:11`, `:15`):

```lean
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter

theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi

theorem critAll (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 :=
  Formalism.VW.critLine allChi N χ hχ s h0 h1 hz

theorem claimAll : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta :=
  ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩
```

All four rest on one statement, `UpperTheory.EveryCharacter`, proved as
`UpperTheory.FinalTheorems.everyCharacter`. We return to it in Section 1.4.

## 1.2 Mathlib's Riemann hypothesis

### 1.2.1 The definition

Mathlib states the Riemann hypothesis as follows [Lean, read]
(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`):

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

In words: for every complex number $s$, if $\zeta(s)=0$, and $s$ is not of the form $-2(n+1)$
with $n\in\mathbb N=\{0,1,2,\dots\}$, and $s\ne1$, then $\Re s=1/2$. The docstring above the
definition calls it "a formal statement of the **Riemann hypothesis**" and adds that
"constructing a term of this type is worth a million dollars"
(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:182`).

Three things must be true for this to be the Riemann hypothesis: `riemannZeta` must be the
Riemann zeta function, the excluded points must be exactly the ones that ought to be excluded,
and `1 / 2` must mean one half. We check each.

### 1.2.2 `riemannZeta` is the Riemann zeta function

Mathlib does not define $\zeta$ by the Dirichlet series, which converges only for $\Re s>1$. It
defines `riemannZeta := hurwitzZetaEven 0` [Lean]
(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:121`), where `hurwitzZetaEven`
(`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:583`) is constructed, in the words of the
module documentation, "as Mellin transforms of various versions of the Jacobi theta function"
(`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:31`) — a construction that produces the
analytic continuation directly [Lean]. Two theorems pin the result down:

- For $\Re s>1$, $\zeta(s)=\sum_{n\ge0}(n+1)^{-s}$ [Lean]
  (`zeta_eq_tsum_one_div_nat_add_one_cpow`, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:214`).
- `riemannZeta` is complex-differentiable at every $s\ne1$ [Lean]
  (`differentiableAt_riemannZeta`, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:139`).

Since $\mathbb C\setminus\{1\}$ is connected and open, a holomorphic function on it is determined
by its values on the half-plane $\Re s>1$ (identity theorem). Hence `riemannZeta` agrees on
$\mathbb C\setminus\{1\}$ with the classical meromorphic continuation of the Dirichlet series
[Expository]. At the single remaining point $s=1$, where the classical function has a pole,
Mathlib's total function must return *some* value; it returns
$\zeta(1)=(\gamma-\log 4\pi)/2$ [Lean] (`riemannZeta_one`,
`Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:418`). This "junk value" is the reason for the
hypothesis $s\ne1$. Section 1.2.2.2 derives this value from the Gamma-normalized subtraction. The assigned value is nonzero, and
Mathlib proves $\zeta(s)\ne0$ on the whole closed half-plane $\Re s\ge1$, including $s=1$
[Lean] (`riemannZeta_ne_zero_of_one_le_re`,
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean:411`).

#### 1.2.2.1 How the theta integral produces the even Hurwitz pole

The even Hurwitz series converges on $\Re s>1$. Its theta integral has two endpoints, and each asks for a different subtraction. The large-$t$ limit depends on the shift, while the leading term at zero has the same coefficient for every shift. The latter is the source of the common pole used in Section 1.3.2.

**Two shifts.** At $a=1$, reindexing $n+1$ leaves each positive absolute distance twice after omitting distance zero. At $a=1/2$, the distances are $m+1/2$ for $m\ge0$, also with multiplicity two. Thus in the starting half-plane the even series give $E_1(s)=\zeta(s)$ and $E_{1/2}(s)=2^s\sum_{m\ge0}(2m+1)^{-s}=(2^s-1)\zeta(s)$. We will obtain their residues directly from the kernels.

**Definition.** For $a\in\mathbb R/\mathbb Z$, use any real representative in the sums

$$
 f_a(t)=\sum_{n\in\mathbb Z}e^{-\pi(n+a)^2t},\qquad
 g_a(t)=\sum_{n\in\mathbb Z}e^{2\pi i n a}e^{-\pi n^2t},\qquad t>0.
$$

Translation by an integer reindexes $f_a$ and leaves the phases of $g_a$ unchanged. Pairing opposite indices makes $g_a$ real. Gaussian comparison on $t\ge\eta>0$ gives locally uniform convergence. Let $\delta_a=1$ for the zero class and $0$ otherwise, and use $t^w=\exp(w\log t)$ with the real logarithm.

The input from **Gaussian Poisson summation** is $f_a(t)=t^{-1/2}g_a(1/t)$. In Mathlib, the kernel proof substitutes $z=ait$ and $\tau=it$ into the two-variable Jacobi theta transformation. Then $z/\tau=a$ and $-1/\tau=i/t$. The exponential multiplier cancels $e^{-\pi a^2t}$, leaving the reciprocal of the positive square root of $-i\tau=t$. The theta transformation invokes `Complex.tsum_exp_neg_quadratic`, retained here as an imported Poisson input [Lean]. [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:132–153](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L132-L153) · [Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:465–490](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean#L465-L490) · [Mathlib/Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean:87](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean#L87)

**Lemma (the modified Mellin integral).** The function

$$
 A_a(s)=\frac12\int_1^\infty t^{s/2-1}(f_a(t)-\delta_a)\,dt
       +\frac12\int_1^\infty t^{(1-s)/2-1}(g_a(t)-1)\,dt
$$

is entire. For $\Re s>1$ one has

$$
 \frac12\int_0^\infty t^{s/2-1}(f_a(t)-\delta_a)\,dt
   = A_a(s)-\frac{\delta_a}{s}+\frac1{s-1}.
$$

The right-hand side continues the completed even series meromorphically. It has a simple pole of residue $1$ at $s=1$ and has residue $-\delta_a$ at zero, where it is holomorphic if $\delta_a=0$.

**Proof.** Choose $0\le a<1$. Splitting the integer indices gives distances $m+a$ and $m+1-a$, $m\ge0$. For $b>0$, $(m+b)^2\ge b^2+m$, so the sum for distances $m+b$ is bounded by $e^{-\pi b^2t}/(1-e^{-\pi t})$. For $b=0$, delete $m=0$ and use the bound with $b=1$. The denominators are bounded below for $t\ge1$. The $n=0$ term of $g_a$ is $1$, and the other terms have total modulus at most $2e^{-\pi t}/(1-e^{-\pi t})$. Therefore $f_a(t)-\delta_a=O(e^{-ct})$ for some $c>0$ and $g_a(t)-1=O(e^{-\pi t})$.

At zero, inversion gives $f_a(t)-\delta_a=t^{-1/2}-\delta_a+O(t^{-1/2}e^{-\pi/t})$. Put $w=s/2$. At infinity the original Mellin integral converges absolutely for every $w$. At zero its integrand has modulus asymptotic to $t^{\Re w-3/2}$, so absolute convergence holds exactly for $\Re w>1/2$. The leading power also prevents conditional convergence. For $\Re w<1/2$, its truncated integral grows in modulus like a constant times $\epsilon^{\Re w-1/2}$, and the constant-kernel contribution is of smaller order, including its logarithmic growth when $w=0$. On $\Re w=1/2$ the leading integral has a logarithmic divergence at $w=1/2$ and an oscillating cutoff term at other points. The constant-kernel contribution converges there, and the exponential remainder is integrable for every $w$.

Define the modified kernel by $f_a(t)-t^{-1/2}$ on $(0,1)$, by $f_a(t)-\delta_a$ on $(1,\infty)$, and by zero at $1$. A singleton has measure zero. The lower piece is $t^{-1/2}(g_a(1/t)-1)$. With $u=1/t$ the product $t^{w-1}t^{-1/2}\,dt$ becomes $-u^{1/2-w-1}\,du$. Reversing the limits sends the lower piece to $\int_1^\infty u^{1/2-w-1}(g_a(u)-1)\,du$. This change can first be made on a truncated interval. The transformed integrand is integrable at infinity for every $w$, so the cutoff can be removed. This proves that $A_a(s)$ is half the modified Mellin transform.

On any bounded disk of $s$, both upper integrands are bounded by a constant times $t^M e^{-c't}$ for a suitable real $M$ and $c'>0$. Their derivatives in $s$ introduce $\pm(\log t)/2$. The resulting bound is integrable, and also bounds difference quotients along segments inside the disk by integration of the derivative along the segment. Dominated convergence therefore gives complex differentiability at every center.

The modified kernel minus the original kernel $f_a-\delta_a$ is $\delta_a-t^{-1/2}$ below $1$ and vanishes above it. For $\Re w>1/2$ the two correcting integrals converge separately. Their truncated power integrals are $(1-\epsilon^w)/w$ and $(1-\epsilon^{w-1/2})/(w-1/2)$. The constant correction requires $\Re w>0$ if its coefficient is nonzero. The $t^{-1/2}$ correction requires $\Re w>1/2$. In the latter half-plane the cutoff terms vanish. The transform of the difference is consequently $\delta_a/w-1/(w-1/2)$. Subtracting this from the modified transform, dividing by two and using $w=s/2$ gives $A_a(s)-\delta_a/s+1/(s-1)$.

For the series identification, let $\sigma=\Re s>1$. For $d=|n+a|>0$, substitution $u=\pi d^2t$ gives the integral of the absolute value of the weighted Gaussian as $\Gamma(\sigma/2)(\pi d^2)^{-\sigma/2}$. These bounds are summable since $d\ge |n|/2$ for large $|n|$. Thus the integral and sum can be exchanged. The same substitution with the complex exponent gives $\Gamma(s/2)(\pi d^2)^{-s/2}$, so the original half-integral is $G(s)E_a(s)$, where

$$
 G(s)=\pi^{-s/2}\Gamma(s/2),\qquad
 E_a(s)=\frac12\sum_{\substack{n\in\mathbb Z\\n+a\ne0}}|n+a|^{-s}
 \quad(\Re s>1).
$$

Write $C_a(s)$ for the continued completed expression. Its rational terms give the residues. Away from $0$ and $1$ define the continuation of $E_a$ by $C_a/G$. The reciprocal of $G$ is entire, and $G(1)=1$ by $\Gamma(1/2)=\sqrt\pi$. Since $\Gamma$ has residue $1$ at zero, $sG(s)$ extends holomorphically there with value $2$. The quotient of $sC_a(s)$ by this function gives $E_a(0)=-\delta_a/2$, with holomorphy at zero. At $1$, $E_a$ has residue $1$ and the precise subtraction used by Lean is

$$
 E_a(s)-\frac{1}{(s-1)G(s)}
   =\frac{A_a(s)-\delta_a/s}{G(s)}.
$$

The right side is holomorphic near $1$. Lean's total division sets the pole term to zero at $1$, so the same equality there follows from its defining expression. The meromorphic residue is read on the punctured neighborhood. $\square$

**Hand calculation.** At $a=1$, $f_1(t)=g_1(t)=1+2\sum_{m\ge1}e^{-\pi m^2t}$. The upper integral subtracts $1$, and the lower correction to the completed function is $-1/s+1/(s-1)$. The residues of $C_1$ at $0,1$ are $-1,1$, respectively. Division by the gamma factor gives $E_1(0)=-1/2$.

At $a=1/2$, $f_{1/2}(t)=2\sum_{m\ge0}e^{-\pi(m+1/2)^2t}$ has leading term $2e^{-\pi t/4}$ at infinity. Its partner is $g_{1/2}(t)=1+2\sum_{m\ge1}(-1)^m e^{-\pi m^2t}$, so near zero $f_{1/2}(t)=t^{-1/2}(1-2e^{-\pi/t}+O(e^{-4\pi/t}))$. The upper integral has no constant to subtract. The lower correction is $1/(s-1)$, so $C_{1/2}$ is holomorphic at zero, $E_{1/2}(0)=0$, and the residue at $1$ is still $1$. The values at zero agree with $\zeta(0,a)=1/2-a$ at these two shifts. The residue at $1$ also agrees with the factor $2^1-1=1$ in the half-integer example. [DLMF §25.11(i), (v)](https://dlmf.nist.gov/25.11) · [DLMF 25.11.13](https://dlmf.nist.gov/25.11.E13)

**Source note.** The archive SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Its manifest, at `lean/lake-manifest.json:6–13`, pins Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`. The following local proofs are [Lean, read].

- **Pole subtraction.** The theorem at line 630 removes the update at zero on a neighborhood of $1$. It uses the completed-function decomposition at line 305 and the entire modified transform at line 417. The FE pair supplies weight $1/2$, scalar $1$, and constants $(\delta_a,1)$. It obtains its exponential bounds by Gaussian comparison. [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:223–315](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L223-L315) · [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:417–419](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L417-L419) · [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:630–642](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L630-L642)
- **Production of the correction.** In the namespace `WeakFEPair`, `f_modif` makes the two subtractions, `f_modif_aux1` records the difference including the singleton, and `f_modif_aux2` evaluates its Mellin transform. The theorem `hasMellin` subtracts this transform from `Λ₀`. For entireness, `differentiable_Λ₀` uses the pair modified to have zero constants, with inversion giving rapid decay at zero from the partner's decay at infinity. [Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:149–182](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L149-L182) · [Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:212–232](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L212-L232) · [Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:247–418](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L247-L418)
- **Analytic suppliers.** The Mellin proof bounds the integrand by endpoint powers and its parameter derivative by nearby powers times a logarithm. The Dirichlet series proof uses summability of the integrals of the Gaussian norms. At zero, Lean uses the quotient limit and a removable-singularity theorem to justify the update. The local gamma normalization uses the entire reciprocal and the limit of $sG(s)$ at zero. Section 1.2.2.2 gives the local reading of the removable-singularity and reciprocal Gamma producers. The general parameter-integral and Poisson theorems remain [Lean]. [Mathlib/Analysis/MellinTransform.lean:228–283](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/MellinTransform.lean#L228-L283) · [Mathlib/Analysis/MellinTransform.lean:320–406](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/MellinTransform.lean#L320-L406) · [Mathlib/NumberTheory/LSeries/MellinEqDirichlet.lean:24–131](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/MellinEqDirichlet.lean#L24-L131) · [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:528–547](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L528-L547) · [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:554–619](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L554-L619) · [Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean:77–111](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L77-L111)

#### 1.2.2.2 Removing the Gamma factor at zero and at one

At an integer shift the completed even Hurwitz function has a pole at zero, but the ordinary even function has value $-1/2$ there. At a quarter shift de-completion instead creates a zero of the even part. At one the ordinary Hurwitz function has a simple pole, and the Mathlib function stores a finite value from a holomorphic remainder. Both assignments can be understood by identifying the holomorphic function whose value is being stored.

Write $E_a$ and $O_a$ for the ordinary even and odd parts, and $H_a=E_a+O_a$ for the full function. Let $P_a$ be the completed even function and $A_a$ its entire part. Write $G(s)=\pi^{-s/2}\Gamma(s/2)$, $q=1/G$, and $\delta_a=1$ for the zero class in $\mathbb R/\mathbb Z$ and $0$ otherwise. The even Mellin construction in §1.2.2.1 supplies
$$
 P_a(s)=A_a(s)-\frac{\delta_a}{s}+\frac1{s-1}.
$$
This formula also describes the total functions if division by zero returns zero. Write $[f]_{c\gets v}$ for $f$ with its value at $c$ replaced by $v$. We use the odd continuation and reflection in §1.3.2.1 and the series identifications in §§1.2.2.1 and 1.3.2.

**Lemma (holomorphy of an update).** Let $f$ be holomorphic on a punctured disk at $c$. If $(z-c)f(z)\to0$, then $f$ has a unique holomorphic extension. If $v$ is its punctured limit, the extension is exactly $[f]_{c\gets v}$.

**Proof.** Set $F(z)=(z-c)f(z)$ away from $c$ and $F(c)=0$. This is continuous and holomorphic off $c$. In applying Morera's theorem to $F$, cut a disk of radius $\epsilon$ out of any triangle meeting $c$. Cauchy's theorem applies to the remaining region. The new arcs have total length at most $2\pi\epsilon$ and the discarded straight segments have length tending to zero. Since $F$ is bounded near $c$, these integrals tend to zero. Thus $F$ is holomorphic. Its Taylor series has zero constant coefficient, so dividing by $z-c$ gives a holomorphic function with center value $F'(c)$ and the same punctured values as $f$. Continuity gives uniqueness and identifies $F'(c)$ with any previously calculated punctured limit. $\square$

In the Lean proof the hypothesis is $(f(z)-f(c))=o((z-c)^{-1})$, where $f(c)$ is an arbitrary stored value. Multiplication by $z-c$ gives the same zero limit, because $(z-c)f(c)\to0$. Lean proves the continuous-center case by applying a Cauchy power-series theorem on a closed ball with the singleton as the countable exceptional set. It applies that case to $F$ and then to the divided difference of $F$ at $c$. Off $c$ this difference is holomorphic by the quotient rule. At $c$ its assigned value is $F'(c)$, and continuity there is the definition of the derivative of $F$. Continuity also identifies the punctured limit with $F'(c)$, so updating with the punctured limit gives exactly the differentiable divided difference. [Lean, read] [Mathlib/Analysis/Complex/RemovableSingularity.lean:34–86](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/RemovableSingularity.lean#L34-L86)

**Lemma (the reciprocal Gamma zero).** The function $q$ is entire, with simple zeros at $-2n$ for $n\ge0$. Its expansion at zero is $q(s)=s/2+O(s^2)$, and $q(1)=1$.

**Proof.** Use the recurrence, holomorphy and nonvanishing of $\Gamma$ in the right half-plane, and the values $\Gamma(1)=1$ and $\Gamma(1/2)=\sqrt\pi$. Let $R(z)$ be the total reciprocal of $\Gamma(z)$, assigned zero at the nonpositive integers. The recurrence gives $R(z)=zR(z+1)$ everywhere, including at zero by the assigned values. For any center one can choose an integer $m\ge0$ with $\Re(z+m)>0$ on a neighborhood of the center. There
$$
 R(z)=\frac{z(z+1)\cdots(z+m-1)}{\Gamma(z+m)}
$$
with the empty product equal to $1$. This is holomorphic. At $z=-n$, with $m>n$, precisely one factor vanishes and it vanishes simply. Now $q(s)=\pi^{s/2}R(s/2)$. Near zero its recurrence expression is $\pi^{s/2}(s/2)/\Gamma(1+s/2)$, and the half-integer Gamma value gives $q(1)=1$. $\square$

Lean proves reciprocal entireness by induction on a shift into the right half-plane. The Deligne factor composes with division by two and multiplies by a nonzero entire power of $\pi$. Its residue proof uses $(s/2)\Gamma(s/2)\to1$ on the punctured filter and $2\pi^{-s/2}\to2$. [Lean, read] [Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:513–535](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L513-L535) · [Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean:73–115](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L73-L115)

**Proposition (Laurent orders and specified values).** Let $P$ be holomorphic off the center $c$ of a disk with at most a simple pole there, and let $q$ be holomorphic on the disk. Write $r$ for the residue of $P$ and $B=P-r/(s-c)$ for its holomorphic part. If $q$ has a simple zero at $c$, then $qP$ extends holomorphically with value $rq'(c)$. An update agrees with that extension precisely when its specified value equals $rq'(c)$. If $q(c)\ne0$, the product has residue $rq(c)$ and has a simple pole when $r\ne0$. Subtracting $rq(s)/(s-c)$ gives a holomorphic extension with center value $q(c)B(c)$. Subtracting $rq(c)/(s-c)$ instead gives center value $q(c)B(c)+rq'(c)$.

**Proof.** Write $w=s-c$ and $q(s)=q(c)+wU(s)$ with $U(c)=q'(c)$ and $U$ holomorphic. Multiplication gives
$$
 q(s)P(s)=\frac{rq(c)}{w}+rU(s)+q(s)B(s).
$$
This proves the extension identities and the necessity of the specified center value by continuity. For a nonzero meromorphic germ the order is its least Laurent exponent. Orders add because the leading coefficients multiply. A simple pole and simple zero therefore give order zero, while a holomorphic $P$ acquires one additional order of vanishing when $q$ has a simple zero. The at-most-simple-pole hypothesis itself follows if $wP$ has a finite limit: apply the update lemma to $wP$ and divide its Taylor series by $w$. $\square$

At zero take $r=-\delta_a$. The actual definition of $E_a$ updates $qP_a$ with $-\delta_a/2$, so it agrees on the whole disk with the holomorphic extension. The Lean producer uses the punctured identity $P_a/G=(sP_a)/(sG)$ to get this limit. Away from zero and one, the product is differentiable and the update agrees on a neighborhood. At zero, the raw total quotient is zero, and convergence of the punctured quotient makes it bounded and hence $o(1/s)$. The update lemma gives differentiability of the specified update. [Lean, read] [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:554–619](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L554-L619)

Near one set $B_a(s)=A_a(s)-\delta_a/s$. In the total-function convention the following identity holds on the full neighborhood, including one:
$$
 E_a(s)-\frac{q(s)}{s-1}=q(s)B_a(s).
$$
Indeed the rational pole term of $P_a$ evaluates to zero at one, and the only update in $E_a$ is at zero. The stored values are $E_a(1)=B_a(1)$ and $H_a(1)=B_a(1)+O_a(1)$. The odd part is entire and the meromorphic germs of $E_a$ and $H_a$ have residue $1$. Their ordinary Laurent constants differ from the stored values by $q'(1)$. Subtraction of two shifts also cancels the identical function $q(s)/(s-1)$ at every point of the neighborhood. This is the holomorphic identity consumed by the finite sum with weights of total sum zero. [Lean, read] [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:621–661](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L621-L661) · [Mathlib/NumberTheory/LSeries/HurwitzZeta.lean:82–107](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L82-L107) · [Mathlib/NumberTheory/LSeries/ZMod.lean:122–129](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L122-L129)

**Integer shift.** Take $a=1$, the zero class. Delete the zero distance and pair each positive distance with its negative. The even half-sum is $\zeta(s)$ and the odd half-sum cancels, giving $O_1\equiv0$ by entireness and uniqueness. At zero $P_1(s)=-1/s+O(1)$, so $q(s)P_1(s)=-1/2+O(s)$. The residue $-1$ and the simple inverse Gamma zero give the order-zero value $H_1(0)=E_1(0)=-1/2$.

Put $w=s-1$. Use the Laurent constant $\gamma$ of $\zeta$ at one, produced in §1.2.2.3, and $\psi(1/2)=-\gamma-2\log 2$ for the logarithmic derivative of $\Gamma$, produced in §1.2.2.4. Then
$$
 G'(1)=\frac{\psi(1/2)-\log\pi}{2}
       =-\frac{\gamma+\log(4\pi)}2,\qquad q'(1)=-G'(1).
$$
Multiplying $\zeta(1+w)=1/w+\gamma+O(w)$ by $G(1+w)=1+wG'(1)+O(w^2)$ gives $P_1(1+w)=1/w+\gamma+G'(1)+O(w)$. The stored value at one is therefore
$$
 H_1(1)=E_1(1)=\gamma+G'(1)=\frac{\gamma-\log(4\pi)}2.
$$
The ordinary Laurent constant is $\gamma$ and its residue is $1$. At zero the series terms are ones, and at one the series is harmonic. Both diverge. [DLMF 5.4.13](https://dlmf.nist.gov/5.4#E13) · [DLMF 25.2.4–5](https://dlmf.nist.gov/25.2#E4)

**Quarter shift.** For $a=1/4$ the negative shift is represented by $3/4$. On $\Re s>1$ their one-sided series use the progressions $1$ and $3$ modulo four, each with scale $4^s$. Before scaling, the sum of the two progressions is $(1-2^{-s})\zeta(s)$, and their difference is $\beta(s)=\sum_{n\ge0}(-1)^n(2n+1)^{-s}$. Consequently, for $s\ne1$,
$$
 E_{1/4}(s)=m(s)\zeta(s),\qquad m(s)=\frac{2^s(2^s-1)}2,\qquad
 O_{1/4}(s)=\frac{4^s}{2}\beta(s).
$$
The sine series at $1/4$ identifies $\beta$ with the entire sine zeta function. The identities extend by uniqueness to $\mathbb C\setminus\{1\}$; at $s=1$ the first one fails for the total functions, since the stored values differ by $3\log 2$ (computed below). The alternating-series remainder for real $s\ge1$ is bounded by the reciprocal of the first omitted odd integer. Hence the limit at one equals the alternating sum. Integrate the finite geometric sum in $-x^2$ on $[0,1]$. The integral of the remainder is at most $\int_0^1x^{2M+2}\,dx$ after indices $0,\ldots,M$, giving $\beta(1)=\int_0^1(1+x^2)^{-1}\,dx=\pi/4$.

The odd completion uses $G(s+1)$, with values $1$ and $1/\pi$ at zero and one. The completed odd reflection identifies the odd completion at zero with the sine completion at one. Thus $O_{1/4}(0)=\beta(1)/\pi=1/4$ and $O_{1/4}(1)=2\beta(1)=\pi/2$. For the even part, $m(0)=0$ and $m'(0)=(\log 2)/2$. Since $\zeta(0)=-1/2$, the even function has a simple zero, and multiplication by $G(s)=2/s+O(1)$ gives $P_{1/4}(0)=-(\log 2)/2$. The completed residue is zero and the inverse Gamma zero survives in $E_{1/4}$, whose update is $0$. Hence $H_{1/4}(0)=1/4$.

At one $m(1)=1$ and $m'(1)=3\log 2$. The even expansion starts with $1/w+\gamma+3\log 2$, and the full expansion with $1/w+\gamma+3\log 2+\pi/2$. Subtracting $q(s)/(s-1)$ gives the actual stored values
$$
 \begin{aligned}
 E_{1/4}(1)&=\frac{\gamma-\log(4\pi)}2+3\log 2,\\
 H_{1/4}(1)&=\frac{\gamma-\log(4\pi)}2+3\log 2+\frac{\pi}{2}.
 \end{aligned}
$$
In particular $H_{1/4}-H_1$ extends at one with value $3\log 2+\pi/2$, because the residues cancel. At one the full and even series diverge by harmonic comparison. The odd series converges there, but its absolute tail diverges. At zero the full series terms are ones, and the alternating beta terms have modulus one. Grouping the latter in pairs at zero produces zero partial sums along only one subsequence and cannot justify substitution into the original series. [DLMF 25.11.1, 25.11.13](https://dlmf.nist.gov/25.11)

**Source note.** The zero-value proof for $\zeta$ unfolds the update. The one-value proof identifies the limit of the Gamma-normalized subtraction with the limit obtained from continuity at the actual stored value. The quarter-shift evaluations are deductions from these interfaces and the series and reflection identities. The [proof map](../notes/proof-map.md#p1-chapter-1-removable-values) records the pinned paths and the imported inputs. [Mathlib/NumberTheory/LSeries/RiemannZeta.lean:119–156](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L119-L156) · [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:386–422](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L386-L422)

#### 1.2.2.3 The Laurent constant at one: harmonic sums, the integral error and the stored value

Section 1.2.2.2 took the Laurent constant $\gamma$ of $\zeta$ at one as a classical input and derived the stored value $\zeta(1)=(\gamma-\log 4\pi)/2$ from it. This subsection closes that supply. It follows the Mathlib proof that produces $\gamma$ as a limit of harmonic sums, converts the limit along the real axis to a limit in the complex plane, and identifies the stored value. Three numbers attached to the point $s=1$ have to be kept apart throughout:

| Name | Formula | Where it comes from |
|---|---|---|
| Laurent constant | $\gamma=\lim_{s\to1}\bigl(\zeta(s)-\tfrac1{s-1}\bigr)$ | the harmonic sums below |
| normalized derivative | $G'(1)=-\tfrac{\gamma+\log 4\pi}2$, where $G(s)=\pi^{-s/2}\Gamma(s/2)$ | the Gamma factor, §1.2.2.2 |
| stored value | $\zeta(1)=\gamma+G'(1)=\tfrac{\gamma-\log 4\pi}2$ | the two together |

Only the first is a property of the Riemann zeta function. The second is a property of the normalization chosen in the Mellin construction, and the third is what the total function `riemannZeta` returns at the pole.

**Example (the ordinary harmonic sum).** Write $H_N=\sum_{k=1}^N 1/k$. Compare $H_N$ with $\log N$ through the integral of $1/x$. On $[k,k+1]$ the function $1/x$ lies between $1/(k+1)$ and $1/k$, so $1/(k+1)<\log(k+1)-\log k<1/k$. Summing from $k=1$ to $N$ gives $H_{N+1}-1<\log(N+1)<H_N$. The two sequences $a_N=H_N-\log(N+1)$ and $b_N=H_N-\log N$ therefore satisfy $0<a_N$ and $b_N\le 1$, and they differ by $\log(1+1/N)\to0$. The common limit is Euler's constant. Taking $N=6$ gives $H_6=49/20$, $a_6=49/20-\log7$ and $b_6=49/20-\log 6$, which is how Mathlib proves $1/2<\gamma<2/3$. The sequence $H_N-\log N$ does not converge fast: the error is about $1/(2N)$. The point of the construction below is that a suitably weighted version of the same error has a finite sum, and that this sum controls $\zeta$ near one.

**Definition (the integral error).** For an integer $n\ge1$ and real $s>0$ put
$$
 t_n(s)=\int_n^{n+1}\frac{x-n}{x^{s+1}}\,dx ,\qquad T(s)=\sum_{n\ge1}t_n(s).
$$
Each $t_n(s)$ is nonnegative. In Mathlib the index is shifted: `term (n + 1) s` is our $t_{n+1}(s)$, and `termTSum s` is $T(s)$. [Lean, read] [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:61–85](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L61-L85)

The integrand is the Euler summation kernel. Integrating $x^{-s-1}$ against the sawtooth $x-n$ on each unit interval records the error made when the sum $\sum n^{-s}$ is replaced by the integral $\int x^{-s}\,dx$. The next two lemmas evaluate $t_n$ in closed form at $s=1$ and for $s>1$.

**Lemma (Euler's constant as a limit).** The sequence $a_N=H_N-\log(N+1)$ is strictly increasing and the sequence $b_N=H_N-\log N$, $N\ge1$, is strictly decreasing. Both converge to the same real number $\gamma$, and $a_N<\gamma<b_N$ for every $N\ge1$.

**Proof.** The inequality $\log y<y-1$ for $y>0$, $y\ne1$, gives everything. For $a$, $a_{N+1}-a_N=\frac1{N+1}-\log\frac{N+2}{N+1}$, and with $y=\frac{N+2}{N+1}$ the logarithm is less than $y-1=\frac1{N+1}$, so the difference is positive. For $b$, $b_{N+1}-b_N=\frac1{N+1}-\log\frac{N+1}{N}$, and with $y=\frac{N}{N+1}$ we get $\log\frac{N+1}{N}=-\log y>1-y=\frac1{N+1}$, so the difference is negative. Since $b_N-a_N=\log(1+1/N)>0$, every $a_M$ is below every $b_N$ (compare both with the index $\max(M,N)$). The increasing sequence $a$ is bounded above by $b_1=1$, so it converges to its supremum; call it $\gamma$. The difference $\log(1+1/N)$ tends to zero, so $b_N\to\gamma$ as well. Strict monotonicity gives the strict bounds. $\square$

Mathlib defines `Real.eulerMascheroniConstant` as the limit of the increasing sequence and proves the two monotonicity statements from `log_lt_sub_one_of_pos` exactly as above. The junk value $2$ assigned to $b_0$ keeps the decreasing sequence total. The statement $H_N-\log N\to\gamma$ is `Real.tendsto_harmonic_sub_log`. [Lean, read] [Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean:48–154](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean#L48-L154)

**Lemma (the integral error at one).** For $n\ge1$,
$$
 t_n(1)=\log(n+1)-\log n-\frac1{n+1},\qquad
 \sum_{n=1}^{N}t_n(1)=\log(N+1)-H_{N+1}+1,\qquad T(1)=1-\gamma .
$$

**Proof.** Write $(x-n)/x^2=1/x-n/x^2$. The first part integrates to $\log(n+1)-\log n$. The second integrates to $n\bigl(1/n-1/(n+1)\bigr)=1/(n+1)$. For the partial sum, induct on $N$. The case $N=0$ reads $0=\log1-H_1+1$. For the step, add $t_{N+1}(1)=\log(N+2)-\log(N+1)-1/(N+2)$ to $\log(N+1)-H_{N+1}+1$ and use $H_{N+2}=H_{N+1}+1/(N+2)$. Finally $\log(N+1)-H_{N+1}+1=1-b_{N+1}\to1-\gamma$. Because the terms are nonnegative, convergence of partial sums is the same as summability, so $T(1)=1-\gamma$. $\square$

In Lean the partial-sum identity is `termSum_one`, proved by induction with `harmonic_succ`, and the sum is `term_tsum_one`, which composes the decreasing-sequence limit with the shift $N\mapsto N+1$. [Lean, read] [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:93–156](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L93-L156) · [Mathlib/NumberTheory/Harmonic/Defs.lean:23–31](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/Defs.lean#L23-L31)

**Lemma (the integral error for $s>1$).** For $n\ge1$ and real $s>1$,
$$
 t_n(s)=\frac1{s-1}\Bigl(\frac1{n^{s-1}}-\frac1{(n+1)^{s-1}}\Bigr)-\frac ns\Bigl(\frac1{n^{s}}-\frac1{(n+1)^{s}}\Bigr),
$$
$$
 \sum_{n=1}^{N}t_n(s)=\frac1{s-1}\Bigl(1-\frac1{(N+1)^{s-1}}\Bigr)-\frac1s\Bigl(\sum_{m=1}^{N}\frac1{m^s}-\frac{N}{(N+1)^s}\Bigr),
$$
and consequently
$$
 T(s)=\frac1{s-1}-\frac{\zeta(s)}s,\qquad \zeta(s)-\frac1{s-1}=1-s\,T(s).
$$

**Proof.** Split the integrand as $x^{-s}-n\,x^{-s-1}$ and integrate each power. The first sum telescopes to the displayed expression. For the second, write $\sum_{n=1}^N n\bigl(n^{-s}-(n+1)^{-s}\bigr)=\sum_{n=1}^N n^{1-s}-\sum_{m=2}^{N+1}(m-1)m^{-s}$. Expanding $(m-1)m^{-s}=m^{1-s}-m^{-s}$ cancels all but the first term of the first sum and the last of the second, leaving $1-(N+1)^{1-s}+\sum_{m=2}^{N+1}m^{-s}=\sum_{m=1}^{N}m^{-s}+(N+1)^{-s}-(N+1)^{1-s}$, which is $\sum_{m=1}^N m^{-s}-N(N+1)^{-s}$. Now let $N\to\infty$. Since $s>1$, $(N+1)^{1-s}\to0$, the partial sums of $m^{-s}$ tend to $\zeta(s)$, and $0\le N(N+1)^{-s}\le(N+1)^{1-s}\to0$. Hence $T(s)=1/(s-1)-\zeta(s)/s$. Multiply by $s$ and rearrange: $\zeta(s)-1/(s-1)=1-sT(s)$, using $s/(s-1)-1/(s-1)=1$. $\square$

Lean's `termSum_of_lt` carries exactly this telescoping, by two inductions on $N$, and `termTSum_of_lt` passes to the limit using the summability of $m^{-s}$ for $s>1$ and the comparison $N(N+1)^{-s}\le(N+1)^{1-s}$. The rearrangement is `zeta_limit_aux1`. [Lean, read] [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:166–262](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L166-L262)

**Lemma (continuity of the error sum).** $T$ is continuous on $[1,\infty)$.

**Proof.** Two dominated-convergence arguments. For fixed $n$ the integrand $(x-n)x^{-s-1}$ is continuous in $s$ and, for $s\ge1$ and $x\ge n\ge1$, bounded by $(x-n)x^{-2}$, which is integrable on $[n,n+1]$. So each $t_n$ is continuous on $[1,\infty)$. For the sum, the same monotonicity in $s$ gives $0\le t_n(s)\le t_n(1)$ for $s\ge1$, and $\sum t_n(1)=1-\gamma$ converges. A series of continuous functions dominated by a convergent constant series is continuous. $\square$

The Lean proof is `continuousOn_term` followed by `continuousOn_termTSum`, with the pointwise bound `term n s ≤ term n 1` supplied by monotonicity of the integrand. [Lean, read] [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:272–311](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L272-L311)

**Theorem (the Laurent constant along the real axis).** As $s\to1^+$ through real values, $\zeta(s)-\dfrac1{s-1}\to\gamma$.

**Proof.** For real $s>1$ the previous lemma gives $\zeta(s)-1/(s-1)=1-sT(s)$. The right side is continuous on $[1,\infty)$ and takes the value $1-T(1)=1-(1-\gamma)=\gamma$ at $s=1$. $\square$

This is `tendsto_riemannZeta_sub_one_div_nhds_right`. The proof first replaces `riemannZeta s` for real $s>1$ by the series $\sum_{n\ge0}(n+1)^{-s}$, using the identification of §1.2.2 and the compatibility of real and complex powers, then applies `zeta_limit_aux1` and the continuity of $T$ at the left endpoint of $[1,\infty)$. [Lean, read] [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:316–339](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L316-L339) · [Mathlib/NumberTheory/LSeries/RiemannZeta.lean:214–219](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L214-L219)

**Theorem (the Laurent constant in the plane).** The function $f(s)=\zeta(s)-\dfrac1{s-1}$ extends holomorphically to $s=1$ with value $\gamma$. Equivalently $f(s)\to\gamma$ as $s\to1$ through complex $s\ne1$, and $\zeta(s)=\dfrac1{s-1}+\gamma+O(s-1)$ near one.

**Proof.** The function $f$ is holomorphic on a punctured neighborhood of one, because $\zeta$ is differentiable away from one and the pole term is differentiable there. By the residue statement of §§1.2.2.1–1.2.2.2, $(s-1)\zeta(s)\to1$, so $(s-1)f(s)=(s-1)\zeta(s)-1\to0$. The holomorphy-of-an-update lemma of §1.2.2.2 applies: $f$ has a holomorphic extension, hence some punctured limit $C$. Restricting to real $s>1$, which approach one inside the punctured neighborhood, gives $C=\gamma$ by the previous theorem and uniqueness of limits. $\square$

Lean carries out the proof in the order stated. It applies `Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO` to get an unnamed limit, where the little-o hypothesis $f(s)-f(1)=o(1/(s-1))$ is checked from `riemannZeta_residue_one`, and then composes with the real embedding to identify the limit with $\gamma$. The entire function `riemannZeta₀`, equal to $\zeta(s)-(s-1)^{-1}$ off one and to $\gamma$ at one, is the resulting extension. [Lean, read] [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:342–373](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L342-L373) · [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:532–558](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L532-L558) · [Mathlib/NumberTheory/LSeries/RiemannZeta.lean:242–243](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L242-L243)

**Theorem (identification of the stored value).** Let $G(s)=\pi^{-s/2}\Gamma(s/2)$ and $q=1/G$ as in §1.2.2.2. Then
$$
 \lim_{s\to1}\Bigl(\frac1{s-1}-\frac{q(s)}{s-1}\Bigr)=G'(1)=-\frac{\gamma+\log 4\pi}2,
 \qquad
 \lim_{s\to1}\Bigl(\zeta(s)-\frac{q(s)}{s-1}\Bigr)=\gamma+G'(1)=\frac{\gamma-\log 4\pi}2,
$$
and the second limit is the stored value $\zeta(1)$ of the total function. The completed function has the same stored value, $\Lambda(1)=\zeta(1)$, and the entire function $\Lambda_0$ of §1.2.2.1 has $\Lambda_0(1)=\zeta(1)+1$.

**Proof.** Since $G(1)=1$ and $G$ is holomorphic and nonvanishing near one,
$$
 \frac1{s-1}-\frac1{G(s)(s-1)}=\frac{G(s)-1}{s-1}\cdot\frac1{G(s)}\longrightarrow G'(1)\cdot\frac1{G(1)}=G'(1).
$$
The value of $G'(1)$ is the logarithmic derivative at one: $G'(1)/G(1)=-\tfrac12\log\pi+\tfrac12\psi(1/2)$ with $\psi(1/2)=-\gamma-2\log2$ (produced in §1.2.2.4), which gives $-(\gamma+\log 4\pi)/2$. Adding this limit to the Laurent-constant limit gives the second display. By §1.2.2.2 the function $\zeta(s)-q(s)/(s-1)$ is differentiable at one with the stored value $\zeta(1)$ as its value there, so it is continuous there and its punctured limit is $\zeta(1)$. Uniqueness of limits gives $\zeta(1)=(\gamma-\log4\pi)/2$. For the completed function, $\Lambda(1)=G(1)\zeta(1)=\zeta(1)$ because $\zeta(s)=\Lambda(s)/G(s)$ for $s\ne0$ as total functions. For $\Lambda_0$, the identity $\Lambda(s)=\Lambda_0(s)-1/s-1/(1-s)$ holds for all $s$ in the total-function convention; at $s=1$ the last term is $1/0=0$, so $\Lambda_0(1)=\Lambda(1)+1$. $\square$

In Lean, `tendsto_Gamma_term_aux` writes the difference as a slope of `Gammaℝ` at one divided by `Gammaℝ s`, and reads off the slope limit from `hasDerivAt_Gammaℝ_one`. That derivative is computed by the product and chain rules from the derivative of $\Gamma$ at $1/2$ and of $\pi^{-s/2}$; §1.2.2.4 reads the production of the derivative at $1/2$. The final step `riemannZeta_one` compares the resulting limit of `riemannZeta s - 1 / Gammaℝ s / (s - 1)` with the continuity statement `tendsto_hurwitzZetaEven_sub_one_div_nhds_one 0` and uses `tendsto_nhds_unique`. The completed values follow by rewriting. [Lean, read] [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:386–438](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L386-L438) · [Mathlib/NumberTheory/Harmonic/GammaDeriv.lean:180–227](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/GammaDeriv.lean#L180-L227) · [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:647–650](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L647-L650)

**Example (the quarter shift).** Let $H_{1/4}$ be the full Hurwitz function at the quarter shift, as in §1.2.2.2, so that $H_{1/4}(s)=\sum_{n\ge0}(n+1/4)^{-s}$ for $\Re s>1$. Its Laurent constant at one can be computed twice.

First, from the identities of §1.2.2.2, valid for $s\ne1$: $H_{1/4}(s)=m(s)\zeta(s)+O_{1/4}(s)$ with $m(s)=2^s(2^s-1)/2$ and $O_{1/4}$ entire. Expanding at $s=1+w$ with $m(1)=1$, $m'(1)=3\log2$ and the theorem above,
$$
 H_{1/4}(1+w)=\frac1w+\gamma+3\log2+\frac\pi2+O(w).
$$
The Laurent constant is $\gamma+3\log2+\pi/2$. Here only the value of the Laurent constant of $\zeta$ has been used from this subsection; the rest is the de-completion of §1.2.2.2.

Second, directly from the series, as a check against the classical digamma function [Expository]. For real $0<a\le1$ and $1\le s\le2$ consider
$$
 \zeta(s,a)-\zeta(s)=\bigl(a^{-s}-1\bigr)+\sum_{n\ge1}\Bigl(\frac1{(n+a)^{s}}-\frac1{(n+1)^{s}}\Bigr).
$$
By the mean value theorem on $[n+a,n+1]$ the $n$-th term is bounded in absolute value by $s(1-a)n^{-s-1}\le 2n^{-2}$, uniformly in $s\in[1,2]$. The series is therefore uniformly convergent, and its sum is continuous on $[1,2]$. Letting $s\to1^+$ and using the theorem above for $\zeta$,
$$
 \lim_{s\to1^+}\Bigl(\zeta(s,a)-\frac1{s-1}\Bigr)=\gamma+\frac1a-1+\sum_{n\ge1}\Bigl(\frac1{n+a}-\frac1{n+1}\Bigr)=\gamma-\gamma-\psi(a)=-\psi(a),
$$
where the last equality is the series $\psi(a)=-\gamma+\sum_{k\ge0}\bigl(\frac1{k+1}-\frac1{k+a}\bigr)$. For $a=1/4$ use Gauss's formula for $\psi$ at rational arguments with $p/q=1/4$:
$$
 \psi\bigl(\tfrac14\bigr)=-\gamma-\log4-\frac\pi2\cot\frac\pi4+\frac12\sum_{k=1}^{3}\cos\frac{\pi k}{2}\,\log\Bigl(2-2\cos\frac{\pi k}2\Bigr).
$$
The $k=1$ and $k=3$ terms vanish because the cosine does, and the $k=2$ term is $\tfrac12(-1)\log4=-\log2$. Hence $\psi(1/4)=-\gamma-3\log2-\pi/2$ and $-\psi(1/4)=\gamma+3\log2+\pi/2$, in agreement with the first computation. The stored value is again the Laurent constant plus the normalized derivative,
$$
 H_{1/4}(1)=\gamma+3\log2+\frac\pi2+G'(1)=\frac{\gamma-\log 4\pi}2+3\log2+\frac\pi2,
$$
because the general statement `tendsto_hurwitzZeta_sub_one_div_nhds_one` identifies the stored value of every shift with the limit of the same $q$-normalized subtraction. Mathlib has no digamma evaluation at $1/4$; the two agreeing computations are our check of the de-completion identities, not a Lean theorem. [Lean, read] [Mathlib/NumberTheory/LSeries/HurwitzZeta.lean:82–101](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L82-L101) · [DLMF 5.7.6](https://dlmf.nist.gov/5.7#E6) · [DLMF 5.4.19](https://dlmf.nist.gov/5.4#E19)

**Remarks.**

1. *Three numbers.* For the integer shift the Laurent constant is $\gamma\approx0.5772$, the normalized derivative is $G'(1)\approx-1.554$, and the stored value is $\zeta(1)\approx-0.977$. For the quarter shift the Laurent constant is $\gamma+3\log2+\pi/2\approx4.227$ and the stored value is about $2.673$. The normalized derivative is the same for every shift, because it is a property of $q$ alone. Differences of two shifts therefore have the same value at one whether one uses Laurent constants or stored values, which is the cancellation used by the finite Dirichlet sums of §1.3.2.

2. *Why the real axis suffices.* The removable-singularity lemma only shows that some limit exists. The value is then determined by any single approach to the point, and the real approach from the right is where the Dirichlet series converges and the Euler summation kernel is positive. This is a different route from reading $\gamma$ off the completed decomposition of §1.2.2.1, which gives the residue but not the constant term.

3. *Consumers.* The constant is used in Mathlib for $\zeta'(0)=-\tfrac12\log 2\pi$ (`deriv_riemannZeta_zero`) and for the nonvanishing $\zeta(1)\ne0$, which follows from $\gamma<2/3<1<\log4\pi$. The latter is what removes the hypothesis $s\ne1$ discussed at the start of §1.2.2. We have read the nonvanishing proof and only the statement of the derivative computation. [Lean, read] [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:441–450](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L441-L450) · [Lean] [Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:492–517](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L492-L517)

4. *Classical form.* The constant $\gamma$ is the $n=0$ Stieltjes constant in the expansion $\zeta(s)=\frac1{s-1}+\sum_{n\ge0}\frac{(-1)^n}{n!}\gamma_n(s-1)^n$, with $\gamma_0=\lim_m\bigl(\sum_{k\le m}1/k-\log m\bigr)$. The Mathlib route proves exactly $\gamma_0=\gamma$ and nothing about the higher coefficients, which are not needed anywhere in the archive's main line. [DLMF 25.2.4–5](https://dlmf.nist.gov/25.2#E4)

**Source note.** The reading in this subsection is R3 for the harmonic-sum, integral-error, continuity and limit bodies in `ZetaAsymp.lean` and `EulerMascheroni.lean`, for the Deligne-factor derivative wrapper in `GammaDeriv.lean`, and for the stored-value consumers. Inputs retained at the boundary are the derivative of the real Gamma function at $1/2$ and at positive integers (now read in §1.2.2.4), the interval-integral library used to evaluate $t_n$, the dominated-convergence lemmas for parametric integrals and series, and the elementary logarithm and exponential bounds behind $1/2<\gamma<2/3$. The [proof map](../notes/proof-map.md#p1-chapter-1-laurent-constant-at-one) lists these with pinned paths.

#### 1.2.2.4 The derivative of Gamma at one half: duplication, log-convexity and the Deligne factor

Sections 1.2.2.2 and 1.2.2.3 used one fact about the Gamma function that neither of them proved: the logarithmic derivative $\psi(1/2)=-\gamma-2\log 2$, which fixes the normalized derivative $G'(1)=-(\gamma+\log 4\pi)/2$ of the Deligne factor $G(s)=\pi^{-s/2}\Gamma(s/2)$. Section 1.2.2.3 kept the two Mathlib producers, the derivative of the real Gamma function at $1/2$ and at the positive integers, as named inputs at its boundary. This subsection reads those producers. It is about a different number from the previous subsection. The Laurent constant $\gamma$ of $\zeta$ at one is a property of the zeta function and was produced there from harmonic sums; it is not recomputed here. The derivative of $\Gamma$ at $1/2$ is a property of the normalization chosen in the Mellin construction, and the only thing it borrows from §1.2.2.3 is the limit $H_n-\log n\to\gamma$.

Throughout, $\Gamma$ is the real Gamma function on $(0,\infty)$, $f=\log\Gamma$, $\psi=f'=\Gamma'/\Gamma$ its logarithmic derivative, and $H_n=\sum_{k=1}^n 1/k$.

**Example (the recurrence moves the derivative between integers).** Differentiating $\Gamma(x+1)=x\Gamma(x)$ gives $\Gamma'(x+1)=\Gamma(x)+x\Gamma'(x)$. Dividing by $\Gamma(x+1)=x\Gamma(x)$ gives the recurrence of the logarithmic derivative,
$$
 \psi(x+1)=\psi(x)+\frac1x .
$$
So once $\psi(1)$ is known, every $\psi(n+1)=\psi(1)+H_n$ follows, and once $\psi(1/2)$ is known, every $\psi(n+1/2)$ follows. The recurrence carries values along a lattice of spacing one but cannot connect the integer lattice with the half-integer lattice. Two separate pieces of information are therefore needed: a value at one point of each lattice. Mathlib gets the first from convexity and the second from the duplication formula.

**Definition (log-convexity).** A function $f$ on an interval is convex if $f(ax+by)\le af(x)+bf(y)$ for $x,y$ in the interval and $a,b\ge0$ with $a+b=1$. The Gamma function is log-convex on $(0,\infty)$: the function $f=\log\Gamma$ is convex there. Mathlib proves this from Hölder's inequality applied to the integral $\Gamma(ax+by)=\int_0^\infty t^{ax+by-1}e^{-t}\,dt$; we use only the statement here, and §1.2.2.5 reads the proof. [Lean] [Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean:111–119](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L111-L119)

**Lemma (chords and tangents).** Let $f$ be convex on an open interval and differentiable at the points named. For $x<y$ in the interval,
$$
 f'(x)\le\frac{f(y)-f(x)}{y-x}\le f'(y).
$$

**Proof.** For $x<u<y$ the three-chord inequality of a convex function gives $\frac{f(u)-f(x)}{u-x}\le\frac{f(y)-f(x)}{y-x}\le\frac{f(y)-f(u)}{y-u}$: the point $(u,f(u))$ lies on or below the chord from $x$ to $y$. Let $u\to x^+$ in the first inequality and $u\to y^-$ in the second. $\square$

Mathlib has both halves as `ConvexOn.deriv_le_slope` and `ConvexOn.slope_le_deriv`; the bodies are not read here. [Lean] [Mathlib/Analysis/Convex/Deriv.lean:601–671](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convex/Deriv.lean#L601-L671)

**Theorem (the derivative at positive integers).** For every integer $n\ge0$,
$$
 \psi(n+1)=H_n-\gamma,\qquad \Gamma'(n+1)=n!\,(H_n-\gamma).
$$
In particular $\Gamma'(1)=-\gamma$.

**Proof.** The function $f=\log\Gamma$ is differentiable on $(0,\infty)$, since $\Gamma$ is differentiable and positive there. From $\Gamma(x+1)=x\Gamma(x)$ we get $f(x+1)=f(x)+\log x$ for $x>0$, and differentiating, $f'(x+1)=f'(x)+1/x$. Induction on $n$ gives $f'(n+1)=f'(1)+H_n$: the case $n=0$ is trivial, and the step adds $1/(n+1)$ to both sides and uses $H_{n+1}=H_n+1/(n+1)$.

It remains to show $f'(1)=-\gamma$. Apply the chords-and-tangents lemma to $f$ on $[n,n+1]$ and on $[n+1,n+2]$, for $n\ge1$. The chord slopes are $f(n+1)-f(n)=\log n$ and $f(n+2)-f(n+1)=\log(n+1)$, so
$$
 \log n\le f'(n+1)\le\log(n+1).
$$
Substituting $f'(n+1)=f'(1)+H_n$ and rearranging,
$$
 H_n-\log(n+1)\le -f'(1)\le H_n-\log n .
$$
Both outer sequences converge to $\gamma$: this is the lemma on Euler's constant as a limit in §1.2.2.3, with $a_n=H_n-\log(n+1)$ and $b_n=H_n-\log n$. Hence $-f'(1)=\gamma$. Finally $\Gamma'(n+1)=\Gamma(n+1)f'(n+1)=n!\,(H_n-\gamma)$ by $\Gamma(n+1)=n!$. $\square$

This is `Real.deriv_Gamma_nat`, and the Lean proof follows the order above: it reduces to `log ∘ Gamma`, proves the derivative recurrence `hder_rec` from the functional equation by differentiating an eventual equality, proves `hder_nat` by induction with `harmonic_succ`, obtains the two slope bounds `derivLB` and `derivUB` from `convexOn_log_Gamma` through `slope_le_deriv` and `deriv_le_slope`, and closes with `le_antisymm` against the two limits `tendsto_harmonic_sub_log` and `tendsto_harmonic_sub_log_add_one`. The wrapped forms are `Real.hasDerivAt_Gamma_nat`, `Real.hasDerivAt_Gamma_one` and `eulerMascheroniConstant_eq_neg_deriv`, which states $\gamma=-\Gamma'(1)$. The differentiability of $\Gamma$ away from the nonpositive integers, `Real.differentiableAt_Gamma`, is used as a named input. [Lean, read] [Mathlib/NumberTheory/Harmonic/GammaDeriv.lean:32–98](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/GammaDeriv.lean#L32-L98) · [Lean] [Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean:149](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean#L149)

**Theorem (Legendre duplication; input).** For every real $s$, as total functions,
$$
 \Gamma(s)\,\Gamma\bigl(s+\tfrac12\bigr)=\Gamma(2s)\,2^{1-2s}\sqrt\pi ,
$$
and $\Gamma(1/2)=\sqrt\pi$.

Mathlib proves the duplication formula for $s>0$ from the Bohr–Mollerup characterization (the right side, suitably rescaled, satisfies the functional equation, is log-convex and equals one at $s=1$), extends it to all complex $s$ by the identity theorem applied to the entire reciprocals of both sides, and restricts back to the reals. The value $\Gamma(1/2)=\sqrt\pi$ is the Gaussian integral. We have read the structure of the complex extension and use the positive-real case and the Gaussian integral as named inputs here; §1.2.2.5 reads the positive-real proof and the extension. [Lean] [Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:559–601](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L559-L601) · [Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean:447–452](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L447-L452) · [Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:307](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean#L307) · [DLMF 5.5.5](https://dlmf.nist.gov/5.5#E5) · [DLMF 5.4.6](https://dlmf.nist.gov/5.4#E6)

**Theorem (the derivative at one half).**
$$
 \Gamma'\bigl(\tfrac12\bigr)=-\sqrt\pi\,(\gamma+2\log 2),\qquad \psi\bigl(\tfrac12\bigr)=-\gamma-2\log 2 .
$$

**Proof (hand calculation A).** Both sides of the duplication formula are differentiable at $s=1/2$: the left because $\Gamma$ is differentiable at $1/2$ and at $1$, the right because $\Gamma$ is differentiable at $2\cdot\frac12=1$ and $2^{1-2s}$ is a smooth function of $s$. Differentiate at $s=1/2$, where $\Gamma(1/2)=\sqrt\pi$, $\Gamma(1)=1$, $\Gamma'(1)=-\gamma$ and $2^{1-2s}=1$.

Left side, by the product rule:
$$
 \Gamma'\bigl(\tfrac12\bigr)\Gamma(1)+\Gamma\bigl(\tfrac12\bigr)\Gamma'(1)=\Gamma'\bigl(\tfrac12\bigr)-\sqrt\pi\,\gamma .
$$
Right side, by the product and chain rules, with $\frac{d}{ds}\Gamma(2s)=2\Gamma'(2s)$ and $\frac{d}{ds}2^{1-2s}=-2\log2\cdot2^{1-2s}$:
$$
 \sqrt\pi\Bigl(2\Gamma'(1)\cdot1+\Gamma(1)\cdot(-2\log 2)\Bigr)=\sqrt\pi\,(-2\gamma-2\log 2).
$$
Equating and solving, $\Gamma'(1/2)=\sqrt\pi(-2\gamma-2\log2)+\sqrt\pi\gamma=-\sqrt\pi(\gamma+2\log 2)$. Dividing by $\Gamma(1/2)=\sqrt\pi$ gives $\psi(1/2)$. Numerically $\gamma+2\log2\approx1.96351$ and $\Gamma'(1/2)\approx-3.48023$. $\square$

The Lean proof `Real.hasDerivAt_Gamma_one_half` is a six-step `calc` computing `deriv Gamma (1/2)`. It first adds and subtracts $\sqrt\pi\gamma$ to rewrite the target as the derivative of $s\mapsto\Gamma(s)\Gamma(s+1/2)$ at $1/2$ (using `deriv_fun_mul`, `Gamma_one_half_eq`, `Gamma_one` and `eulerMascheroniConstant_eq_neg_deriv`), replaces the product by the right side of `Gamma_mul_Gamma_add_half`, pulls out the constant $\sqrt\pi$, splits the remaining product, evaluates the derivative of $\Gamma(2s)$ by the chain rule and `hasDerivAt_Gamma_one`, and the derivative of $2^{1-2s}$ by `HasDerivAt.rpow`, and finishes with `ring`. Every differentiability side condition is discharged by `differentiableAt_Gamma` at a positive point. [Lean, read] [Mathlib/NumberTheory/Harmonic/GammaDeriv.lean:100–146](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/GammaDeriv.lean#L100-L146) · [DLMF 5.4.13](https://dlmf.nist.gov/5.4#E13)

**Corollary (three halves and the half-integer lattice).**
$$
 \Gamma'\bigl(\tfrac32\bigr)=\frac{\sqrt\pi}2\,(2-\gamma-2\log 2),\qquad
 \psi\bigl(n+\tfrac12\bigr)=-\gamma-2\log2+2\sum_{k=1}^{n}\frac1{2k-1}\quad(n\ge0).
$$

**Proof (hand calculation B).** Apply the recurrence of the first example at $x=1/2$: $\Gamma'(3/2)=\Gamma(1/2)+\tfrac12\Gamma'(1/2)=\sqrt\pi-\tfrac12\sqrt\pi(\gamma+2\log2)=\tfrac{\sqrt\pi}2(2-\gamma-2\log 2)$. Equivalently $\psi(3/2)=\psi(1/2)+2=2-\gamma-2\log 2\approx0.03649$, and with $\Gamma(3/2)=\sqrt\pi/2\approx0.88623$ we get $\Gamma'(3/2)\approx0.03234$. For general $n$, induct: $\psi(n+\tfrac32)=\psi(n+\tfrac12)+\frac1{n+1/2}=\psi(n+\tfrac12)+\frac{2}{2n+1}$, which adds the next odd reciprocal. $\square$

The half-integer formula is DLMF 5.4.15; Mathlib states only the case $n=0$. [Expository] from [Lean] inputs · [DLMF 5.4.15](https://dlmf.nist.gov/5.4#E15) · [DLMF 5.5.2](https://dlmf.nist.gov/5.5#E2)

**Proposition (transport to the complex function).** Let $F:\mathbb C\to\mathbb C$ be complex-differentiable at a real point $x$, let $g:\mathbb R\to\mathbb R$ have derivative $g'(x)$ at $x$, and suppose $F(t)=g(t)$ for all real $t$. Then $F'(x)=g'(x)$. In particular the complex Gamma function has derivative $-\gamma$ at $1$, $-\sqrt\pi(\gamma+2\log2)$ at $1/2$ and $n!(H_n-\gamma)$ at $n+1$.

**Proof.** The restriction $t\mapsto F(t)$ of $F$ to the real line is the composition of $F$ with the inclusion $\mathbb R\to\mathbb C$, so by the chain rule it has derivative $F'(x)\cdot1$ at $x$ as a map $\mathbb R\to\mathbb C$. By hypothesis this restriction equals $t\mapsto g(t)$ viewed in $\mathbb C$, whose derivative is $g'(x)$. Derivatives are unique, so $F'(x)=g'(x)$. For $\Gamma$ the hypotheses hold at $1$, $1/2$ and $n+1$: the complex function is differentiable away from the nonpositive integers and agrees with the real function on the real line. $\square$

In Lean this is the private lemma `HasDerivAt.complex_of_real`, proved by `comp_ofReal` and `ofReal_comp` and the uniqueness of `deriv`, applied with `Gamma_ofReal`. The three complex statements are `Complex.hasDerivAt_Gamma_nat`, `Complex.hasDerivAt_Gamma_one` and `Complex.hasDerivAt_Gamma_one_half`. [Lean, read] [Mathlib/NumberTheory/Harmonic/GammaDeriv.lean:154–191](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/GammaDeriv.lean#L154-L191)

**Theorem (normalized derivatives of the two Gamma factors).** Let $G(s)=\pi^{-s/2}\Gamma(s/2)$ be the Deligne factor of §1.2.2.2 and $\Gamma_{\mathbb C}(s)=2(2\pi)^{-s}\Gamma(s)$ its complex companion. Then
$$
 G'(1)=-\frac{\gamma+\log 4\pi}2,\qquad \Gamma_{\mathbb C}'(1)=-\frac{\gamma+\log 2\pi}{\pi}.
$$

**Proof.** For $G$, the product rule at $s=1$ with $\frac{d}{ds}\pi^{-s/2}=-\tfrac12\log\pi\cdot\pi^{-s/2}$ and $\frac{d}{ds}\Gamma(s/2)=\tfrac12\Gamma'(s/2)$ gives
$$
 G'(1)=\pi^{-1/2}\Bigl(-\tfrac12\log\pi\cdot\Gamma(\tfrac12)+\tfrac12\Gamma'(\tfrac12)\Bigr)
      =-\tfrac12\log\pi+\tfrac12\psi(\tfrac12)
      =-\tfrac12\bigl(\log\pi+\gamma+2\log 2\bigr)=-\frac{\gamma+\log4\pi}2 .
$$
For $\Gamma_{\mathbb C}$, with $\frac{d}{ds}(2\pi)^{-s}=-\log(2\pi)(2\pi)^{-s}$, $\Gamma(1)=1$ and $\Gamma'(1)=-\gamma$,
$$
 \Gamma_{\mathbb C}'(1)=2\bigl((2\pi)^{-1}(-\log 2\pi)+(2\pi)^{-1}(-\gamma)\bigr)=-\frac{\gamma+\log 2\pi}{\pi}. \qquad\square
$$

These are `hasDerivAt_Gammaℝ_one` and `hasDerivAt_Gammaℂ_one`, both proved by `HasDerivAt.mul` of a `const_cpow` derivative and the complex Gamma derivative at $1/2$ (composed with $s\mapsto s/2$) or at $1$, followed by a rewrite of the resulting expression into the stated real logarithm. Numerically $G'(1)\approx-1.55412$ and $\Gamma_{\mathbb C}'(1)\approx-0.76875$. [Lean, read] [Mathlib/NumberTheory/Harmonic/GammaDeriv.lean:193–228](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/GammaDeriv.lean#L193-L228) · [Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean:43–45](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L43-L45)

**Where each derivative is spent in this chapter.**

| Derivative | Value | Paid to |
|---|---|---|
| $\Gamma'(1)=-\gamma$ | from log-convexity | the half-point calculation above; in Mathlib also $\zeta'(0)=-\tfrac12\log2\pi$ (§1.2.2.3, Remark 3) |
| $\Gamma'(1/2)$, i.e. $\psi(1/2)$ | from duplication | $G'(1)$ in the integer-shift calculation of §1.2.2.2 and in the identification of the stored value $\zeta(1)$ in §1.2.2.3 |
| $\Gamma'(3/2)$, $\Gamma'(n+1)$ for $n\ge1$ | from the recurrence | nothing in this chapter; they illustrate the recurrence the Lean induction runs on |

**Remarks.**

1. *Two lattices, two inputs.* The recurrence connects $\psi$ at points differing by integers. Log-convexity fixes the integer lattice through the squeeze $\log n\le\psi(n+1)\le\log(n+1)$, and the duplication formula connects the half-integer lattice to the integer one at the single point $s=1/2$, where $2s=1$. The only use of the duplication formula in Chapter 1 is this one derivative.

2. *What is borrowed from §1.2.2.3.* Only the limit $H_n-\log n\to\gamma$, in both its forms $a_n\to\gamma$ and $b_n\to\gamma$. The Euler-summation integral error, the continuity of $T$ and the removable-singularity transfer play no role here. Conversely §1.2.2.3 borrowed from this subsection only $G'(1)$. The two productions are independent and meet in the stored value $\zeta(1)=\gamma+G'(1)$.

3. *The classical routes not taken.* The textbook derivations of $\psi(1)=-\gamma$ go through the Weierstrass product or the series $\psi(z)=-\gamma+\sum_{k\ge0}\bigl(\frac1{k+1}-\frac1{k+z}\bigr)$ used in the quarter-shift check of §1.2.2.3. Mathlib has neither at the pinned commit; the convexity route needs only the Bohr–Mollerup development already present for the duplication formula. The value $\psi(1/2)$ is likewise usually read off the series or the reflection formula; here it comes from one differentiation.

4. *Real versus complex.* All derivatives are computed for the real Gamma function and transported. The transport proposition is the only place where complex differentiability of $\Gamma$ at the point is needed, and it is supplied by `differentiableAt_Gamma` away from the nonpositive integers.

**Source note.** The reading in this subsection is R3 for `Real.deriv_Gamma_nat`, `Real.hasDerivAt_Gamma_one_half`, the transport lemma and the three complex derivative statements, and for the two normalized derivatives `hasDerivAt_Gammaℝ_one` and `hasDerivAt_Gammaℂ_one`. Inputs retained at the boundary are the log-convexity of $\Gamma$ (Hölder), the positive-real duplication formula (Bohr–Mollerup uniqueness; both read in §1.2.2.5), the Gaussian integral $\Gamma(1/2)=\sqrt\pi$, the convex slope lemmas, the differentiability of $\Gamma$ away from the nonpositive integers, and the real and complex power rules `HasDerivAt.rpow` and `HasDerivAt.const_cpow`. The [proof map](../notes/proof-map.md#p1-chapter-1-derivative-of-gamma-at-one-half) lists these with pinned paths. The hand calculations A and B and the half-integer formula are ours, checked against DLMF 5.4.12–15 and 5.5.2, 5.5.5.

#### 1.2.2.5 Log-convexity, the Bohr–Mollerup theorem and the duplication formula

Section 1.2.2.4 spent two facts about the real Gamma function without proving them: the convexity of $\log\Gamma$ on $(0,\infty)$, which fixed the derivative on the integer lattice, and Legendre's duplication formula for $s>0$, which carried it to the half-integer lattice. This subsection reads their Mathlib producers in `BohrMollerup.lean`. The two facts are not independent. Log-convexity, together with the recurrence and $\Gamma(1)=1$, characterizes $\Gamma$ (the Bohr–Mollerup theorem), and the duplication formula follows by checking these three properties for a rescaled product of two half-argument Gamma values. The proofs use Euler's integral, Hölder's inequality and the value $\Gamma(1/2)=\sqrt\pi$; they use nothing from Euler's constant (§1.2.2.3) or from the Beta integral (Chapter 2). Throughout, $\Gamma$ is the real Gamma function on $(0,\infty)$, where it is positive, and $\log$ is the natural logarithm of a positive number.

**Example (the recurrence and the normalization do not determine $\Gamma$).** Let $p$ be a positive function of period $1$ with $p(1)=1$, and put $f=\Gamma p$. Then $f>0$, $f(x+1)=x\Gamma(x)p(x)=xf(x)$ and $f(1)=1$. For $p(x)=1+\sin^2(\pi x)$ the function $f$ is real-analytic and agrees with $\Gamma$ at every positive integer, $f(n)=(n-1)!$, but $f(n+\tfrac12)=2\,\Gamma(n+\tfrac12)$; for instance $f(1/2)=2\sqrt\pi$. The recurrence only moves values along $x+\mathbb Z$, and any choice of $f$ on $(0,1]$ extends to a solution, as Artin observes ([*The Gamma Function*, p. 13](https://archive.org/details/gammafunction0000arti)). A further condition is needed, and the one that works is a condition on shape: for this $f$ the midpoint inequality of the next definition already fails on $[1,2]$, since $f(3/2)^2=\bigl(2\Gamma(\tfrac32)\bigr)^2=\pi>1=f(1)f(2)$.

**Definition (log-convexity; the Gauss quotients).** A positive function $f$ on $(0,\infty)$ is *log-convex* if $\log f$ is convex there, that is,
$$
 f(as+bt)\le f(s)^a f(t)^b\qquad(s,t>0,\ a,b\ge0,\ a+b=1).
$$
For $x>0$ and $n\ge1$ put
$$
 L_n(x)=x\log n+\log n!-\sum_{m=0}^{n}\log(x+m),\qquad e^{L_n(x)}=Q_n(x)=\frac{n^x\,n!}{x(x+1)\cdots(x+n)} .
$$
$Q_n$ is the Gauss quotient written $G_n$ in Chapter 2, §2.3.2.1 (we avoid that letter here because $G$ denotes the Deligne factor in this chapter), and $Q_n(x)\to\Gamma(x)$ is Gauss's product formula, DLMF 5.8.1. In Lean, $L_n(x)$ is `Real.BohrMollerup.logGammaSeq x n`. [Lean, read] [BohrMollerup.lean:138–141](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L138-L141) · [DLMF 5.8.1](https://dlmf.nist.gov/5.8#E1)

**Theorem 1 (log-convexity of $\Gamma$).** For $s,t>0$ and $a,b>0$ with $a+b=1$,
$$
 \Gamma(as+bt)\le\Gamma(s)^a\,\Gamma(t)^b .
$$
Consequently $\log\Gamma$ is convex on $(0,\infty)$.

The proof uses Hölder's inequality for integrals, which we take as an input: if $p,q>1$ with $1/p+1/q=1$, and $g,h\ge0$ are measurable on $(0,\infty)$ with $g^p$ and $h^q$ integrable, then
$$
 \int_0^\infty gh\,dx\le\Bigl(\int_0^\infty g^p\,dx\Bigr)^{1/p}\Bigl(\int_0^\infty h^q\,dx\Bigr)^{1/q}.
$$
In Mathlib this is `integral_mul_le_Lp_mul_Lq_of_nonneg`, which reduces to the same inequality for $\lVert g\rVert\,\lVert h\rVert$ and then to the Lebesgue-integral version `ENNReal.lintegral_mul_le_Lp_mul_Lq`, whose proof we do not read. [Lean] [Bochner/Basic.lean:1144–1209](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L1144-L1209) · [MeanInequalities.lean:150](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/MeanInequalities.lean#L150) · [DLMF 1.7.5](https://dlmf.nist.gov/1.7#E5)

**Proof.** For $c>0$ and $u>0$ put $\varphi_{c,u}(x)=e^{-cx}x^{c(u-1)}$ on $(0,\infty)$. It is nonnegative and continuous, and $\varphi_{c,u}(x)^{1/c}=e^{-x}x^{u-1}$ is Euler's integrand, which is integrable because $u>0$. So $\varphi_{c,u}\in L^{1/c}(0,\infty)$ and $\int_0^\infty\varphi_{c,u}^{1/c}\,dx=\Gamma(u)$. Take $(c,u)=(a,s)$ and $(c,u)=(b,t)$. Because $a+b=1$,
$$
 \varphi_{a,s}(x)\,\varphi_{b,t}(x)=e^{-(a+b)x}x^{a(s-1)+b(t-1)}=e^{-x}x^{as+bt-1},
$$
whose integral is $\Gamma(as+bt)$, as $as+bt>0$. The exponents $p=1/a$ and $q=1/b$ are conjugate, $1/p+1/q=a+b=1$, and Hölder's inequality gives
$$
 \Gamma(as+bt)\le\Bigl(\int_0^\infty\varphi_{a,s}^{1/a}\,dx\Bigr)^{a}\Bigl(\int_0^\infty\varphi_{b,t}^{1/b}\,dx\Bigr)^{b}=\Gamma(s)^a\,\Gamma(t)^b .
$$
All three Gamma values are positive, so taking logarithms gives $\log\Gamma(as+bt)\le a\log\Gamma(s)+b\log\Gamma(t)$ for $a,b>0$; for $a=0$ or $b=0$ the convexity inequality is an equality. $\square$

The Lean proof `Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma` is this argument. Its local function `f c u x` is $\varphi_{c,u}(x)$; `fpow` is the identity $\varphi_{c,u}^{1/c}=e^{-x}x^{u-1}$; `f_mem_Lp` proves membership in $L^{1/c}$ through `memLp_norm_rpow_iff`, `GammaIntegral_convergent` and continuity on $(0,\infty)$; the conjugate exponents come from `Real.holderConjugate_one_div`; after the three Gamma values are rewritten by `Gamma_eq_integral`, Hölder is applied and the integrands are matched by the exponential identity `A` and the power identity `B`. `convexOn_log_Gamma` then uses `convexOn_iff_forall_pos`, which reduces convexity to strictly positive weights, together with `log_rpow`, `log_mul` and the monotonicity of $\log$. [Lean, read] [BohrMollerup.lean:58–120](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L58-L120)

**Lemma 2 (integers and shifts).** Let $F:(0,\infty)\to\mathbb R$ satisfy $F(y+1)=F(y)+\log y$ for all $y>0$. Then, for $n\ge1$ and $x>0$,
$$
 F(n)=F(1)+\log(n-1)!,\qquad F(x+n)=F(x)+\sum_{m=0}^{n-1}\log(x+m).
$$

**Proof.** Induction on $n$: the first identity uses $\log(n-1)!+\log n=\log n!$, the second adds $\log(x+n)$ at each step. $\square$

These are `f_nat_eq` and `f_add_nat_eq`. [Lean, read] [BohrMollerup.lean:145–165](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L145-L165)

**Lemma 3 (two chords).** Let $F$ be as in Lemma 2 and convex on $(0,\infty)$.

1. For $n\ge1$ and $0<x\le1$: $F(n+x)\le F(n)+x\log n$.
2. For $n\ge2$ and $x>0$: $F(n)+x\log(n-1)\le F(n+x)$.

**Proof.** (1) Write $n+x=(1-x)n+x(n+1)$. Convexity and $F(n+1)=F(n)+\log n$ give $F(n+x)\le(1-x)F(n)+xF(n+1)=F(n)+x\log n$. (2) For the three points $n-1<n<n+x$ the slopes of a convex function increase, so $F(n)-F(n-1)\le\bigl(F(n+x)-F(n)\bigr)/x$. The left side is $\log(n-1)$ by the recurrence at $n-1>0$; multiply by $x>0$. $\square$

In Lean, (1) is `f_add_nat_le`, proved from the definition of convexity with weights $1-x$ and $x$, and (2) is `f_add_nat_ge`, proved from `convexOn_iff_slope_mono_adjacent`. These two inequalities are the only places where convexity enters the uniqueness proof. [Lean, read] [BohrMollerup.lean:167–188](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L167-L188)

**Lemma 4 (the squeeze and the limit).** Let $F$ be as in Lemma 3. For $n\ge1$,
$$
 F(x)-F(1)-x\bigl(\log(n+1)-\log n\bigr)\le L_n(x)\le F(x)-F(1),
$$
where the upper bound holds for every $x>0$ and the lower bound for $0<x\le1$. Moreover $L_n(x)\to F(x)-F(1)$ as $n\to\infty$, for every $x>0$.

**Proof.** By Lemma 2, $F(x)+\sum_{m=0}^{n}\log(x+m)=F(n+1+x)$ and $F(1)+\log n!=F(n+1)$, so
$$
 F(x)-F(1)-L_n(x)=F(n+1+x)-F(n+1)-x\log n .
$$
Lemma 3(2) at the integer $n+1\ge2$ says that the right side is $\ge0$, which is the upper bound. Lemma 3(1) at $n+1$ says, for $0<x\le1$, that it is $\le x\log(n+1)-x\log n$, which is the lower bound. Since $\log(n+1)-\log n\to0$, the two bounds squeeze $L_n(x)$ to $F(x)-F(1)$ when $0<x\le1$.

For larger $x$ argue by induction on the integer $m$ with $m<x\le m+1$. Expanding the definition gives, for $y>0$ and $n\ge1$,
$$
 L_n(y+1)=L_{n+1}(y)+\log y-(y+1)\bigl(\log(n+1)-\log n\bigr).
$$
With $y=x-1$, which lies in $(m-1,m]$, this reads $L_n(x)=L_{n+1}(x-1)+\log(x-1)-x\bigl(\log(n+1)-\log n\bigr)$. By the induction hypothesis $L_{n+1}(x-1)\to F(x-1)-F(1)$, and the last term tends to $0$. Hence $L_n(x)\to F(x-1)+\log(x-1)-F(1)=F(x)-F(1)$. $\square$

The Lean proof is split the same way: `logGammaSeq_add_one` is the displayed shift identity; `le_logGammaSeq` and `ge_logGammaSeq` are the two bounds, obtained from `f_add_nat_le` and `f_add_nat_ge` at $n+1$; `tendsto_logGammaSeq_of_le_one` is the squeeze with `tendsto_log_nat_add_one_sub_log`; and `tendsto_logGammaSeq` inducts on $m=\lceil x-1\rceil$ with the reindexing $n\mapsto n+1$. [Lean, read] [BohrMollerup.lean:190–291](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L190-L291)

**Theorem 5 (Bohr–Mollerup).** Let $f:(0,\infty)\to\mathbb R$ satisfy

1. $f(y)>0$ for $y>0$;
2. $f(y+1)=y\,f(y)$ for $y>0$;
3. $f(1)=1$;
4. $\log f$ is convex on $(0,\infty)$.

Then $f=\Gamma$ on $(0,\infty)$. Moreover $L_n(x)\to\log\Gamma(x)$, that is $Q_n(x)\to\Gamma(x)$, for every $x>0$.

**Proof.** By (1) and (2), $F=\log f$ satisfies $F(y+1)=F(y)+\log y$; by (4) it is convex; by (3), $F(1)=0$. Lemma 4 gives $L_n(x)\to\log f(x)$. The Gamma function itself satisfies (1)–(4): positivity and $\Gamma(1)=1$ come from Euler's integral, the recurrence from integration by parts, and (4) is Theorem 1. So Lemma 4 applied to $\log\Gamma$ gives $L_n(x)\to\log\Gamma(x)$. The sequence $L_n(x)$ does not involve $f$, so the two limits coincide, $\log f(x)=\log\Gamma(x)$, and $f(x)=\Gamma(x)$ because both are positive. $\square$

In Lean the limit for $\Gamma$ is `Real.BohrMollerup.tendsto_log_gamma`, and the theorem is `Real.eq_Gamma_of_log_convex`, which concludes `EqOn f Gamma (Ioi 0)` by `tendsto_nhds_unique` and `log_injOn_pos`. Conditions (1)–(4) are its whole hypothesis; no continuity or differentiability of $f$ is assumed. The argument is the one of Artin's Theorem 2.1, written additively; Artin credits the method to Bohr and Mollerup (1922). [Lean, read] [BohrMollerup.lean:293–318](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L293-L318) · [DLMF §5.5(iv)](https://dlmf.nist.gov/5.5.iv) · [Artin, *The Gamma Function*, pp. vi, 14–15](https://archive.org/details/gammafunction0000arti)

**Hand calculation A (the integer values pin down $\Gamma(1/2)$).** For $F=\log\Gamma$ the bounds of Lemma 4 use only $\Gamma(n)=(n-1)!$ and convexity. At $x=\tfrac12$ they bracket $\Gamma(\tfrac12)$ without any integral:
$$
 Q_n(\tfrac12)\le\Gamma(\tfrac12)\le Q_n(\tfrac12)\sqrt{\tfrac{n+1}{n}},\qquad Q_n(\tfrac12)=\frac{\sqrt n\;n!}{\tfrac12\cdot\tfrac32\cdots(n+\tfrac12)} .
$$
For $n=1$ the two chords of Lemma 3 at the integer $2$ read $F(2)+\tfrac12\log1\le F(\tfrac52)\le F(2)+\tfrac12\log2$, that is $1\le\Gamma(\tfrac52)\le\sqrt2$. The recurrence gives $\Gamma(\tfrac52)=\tfrac32\cdot\tfrac12\,\Gamma(\tfrac12)$, hence $\tfrac43\le\Gamma(\tfrac12)\le\tfrac43\sqrt2$. For $n=2$ the chords at $3$ give $2\sqrt2\le\Gamma(\tfrac72)\le2\sqrt3$, and $\Gamma(\tfrac72)=\tfrac{15}8\Gamma(\tfrac12)$. For $n=3$ the chords at $4$ give $6\sqrt3\le\Gamma(\tfrac92)\le12$, and $\Gamma(\tfrac92)=\tfrac{105}{16}\Gamma(\tfrac12)$. So:

| $n$ | lower bound $Q_n(\tfrac12)$ | upper bound $Q_n(\tfrac12)\sqrt{(n+1)/n}$ |
|---|---|---|
| $1$ | $4/3\approx1.33333$ | $4\sqrt2/3\approx1.88562$ |
| $2$ | $16\sqrt2/15\approx1.50849$ | $16\sqrt3/15\approx1.84752$ |
| $3$ | $32\sqrt3/35\approx1.58359$ | $64/35\approx1.82857$ |
| $1000$ | $\approx1.77179$ | $\approx1.77268$ |

The brackets close on $\sqrt\pi\approx1.77245$, the Gaussian value, which enters this development only through Theorem 6 below. The upper bound equals $\sqrt{n+1}\;n!\;2^{n+1}/\bigl(1\cdot3\cdots(2n+1)\bigr)$; squaring the limit and using $2\cdot4\cdots(2n)=2^n n!$ turns $\Gamma(\tfrac12)^2=\pi$ into Wallis's product $\prod_{k\ge1}\frac{4k^2}{4k^2-1}=\frac\pi2$. [Expository]

**Theorem 6 (duplication for positive arguments).** For $s>0$,
$$
 \Gamma(s)\,\Gamma\bigl(s+\tfrac12\bigr)=\Gamma(2s)\,2^{1-2s}\sqrt\pi .
$$

**Proof.** Define on $(0,\infty)$
$$
 D(s)=\frac{2^{s-1}}{\sqrt\pi}\,\Gamma\bigl(\tfrac s2\bigr)\,\Gamma\bigl(\tfrac s2+\tfrac12\bigr)
$$
and check the four conditions of Theorem 5.

1. $D(s)>0$, as a product of positive factors.
2. $D(s+1)=\frac{2^{s}}{\sqrt\pi}\,\Gamma(\tfrac s2+\tfrac12)\,\Gamma(\tfrac s2+1)$, and $\Gamma(\tfrac s2+1)=\tfrac s2\,\Gamma(\tfrac s2)$. Since $2^s=2\cdot2^{s-1}$, $D(s+1)=s\,D(s)$.
3. $D(1)=\Gamma(\tfrac12)\Gamma(1)/\sqrt\pi=1$, by $\Gamma(1/2)=\sqrt\pi$.
4. $\log D(s)=\log\Gamma(\tfrac s2)+\log\Gamma(\tfrac s2+\tfrac12)+s\log2-\log(2\sqrt\pi)$. The first two terms are $\log\Gamma$ composed with the affine maps $s\mapsto s/2$ and $s\mapsto s/2+1/2$, which send $(0,\infty)$ into $(0,\infty)$, so they are convex by Theorem 1; the third term is linear and the fourth constant. So $\log D$ is convex on $(0,\infty)$.

Theorem 5 gives $D=\Gamma$ on $(0,\infty)$. At the point $2s>0$ this says $\Gamma(2s)=\frac{2^{2s-1}}{\sqrt\pi}\Gamma(s)\Gamma(s+\tfrac12)$, which rearranges to the claim. $\square$

In Lean, $D$ is `doublingGamma`, written $\Gamma(s/2)\Gamma(s/2+1/2)2^{s-1}/\sqrt\pi$. The checks are `doublingGamma_add_one` (stated for $s\ne0$), `doublingGamma_one` (the only call of `Gamma_one_half_eq` in this development), `log_doublingGamma_eq` and `doublingGamma_log_convex_Ioi`. In the last, the first summand is `convexOn_log_Gamma.comp_affineMap` for $s\mapsto s/2$, whose preimage of $(0,\infty)$ is exactly $(0,\infty)$; the second is the same composition for $s\mapsto s/2+1/2$, whose natural domain $(-1,\infty)$ is cut down to $(0,\infty)$ by `ConvexOn.subset`; the linear term is `convexOn_id` scaled by $\log2\ge0$. `doublingGamma_eq_Gamma` applies `eq_Gamma_of_log_convex`, and `Gamma_mul_Gamma_add_half_of_pos` evaluates it at $2s$ and clears $2^{2s-1}$ and $\sqrt\pi$ with `field`. [Lean, read] [BohrMollerup.lean:375–452](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L375-L452) · [DLMF 5.5.5](https://dlmf.nist.gov/5.5#E5)

**Hand calculation B (the doubling function on and off the integers).** The recurrence step (2) is the heart of the proof. Under $s\mapsto s+1$ the two factors trade places, $\Gamma(\tfrac s2)\Gamma(\tfrac s2+\tfrac12)\mapsto\Gamma(\tfrac s2+\tfrac12)\Gamma(\tfrac s2+1)$; the recurrence for the second factor produces $\tfrac s2$, and the base $2$ of $2^{s-1}$ supplies the missing factor $2$. On the integers, (2) and (3) already force $D(n)=(n-1)!$. Indeed, with $\Gamma(\tfrac32)=\tfrac{\sqrt\pi}2$ and $\Gamma(\tfrac52)=\tfrac{3\sqrt\pi}4$,
$$
 D(2)=\tfrac{2}{\sqrt\pi}\,\Gamma(1)\Gamma(\tfrac32)=1,\qquad D(3)=\tfrac{4}{\sqrt\pi}\,\Gamma(\tfrac32)\Gamma(2)=2,\qquad D(4)=\tfrac{8}{\sqrt\pi}\,\Gamma(2)\Gamma(\tfrac52)=6 .
$$
These values say nothing beyond (2) and (3); the content of Theorem 6 lies off the integers. At $s=\tfrac12$ we have $D(\tfrac12)=2^{-1/2}\pi^{-1/2}\,\Gamma(\tfrac14)\Gamma(\tfrac34)$. The reflection formula $\Gamma(z)\Gamma(1-z)=\pi/\sin\pi z$ ([Chapter 2, §2.3.2.1](02-functional-equations-and-primitive-characters.md#2321-why-gamma-has-no-zeros-in-the-right-half-plane)) at $z=\tfrac14$ gives $\Gamma(\tfrac14)\Gamma(\tfrac34)=\pi\sqrt2$, hence $D(\tfrac12)=\sqrt\pi=\Gamma(\tfrac12)$, as Theorem 5 predicts. In the duplication formula this is the case $s=\tfrac14$. In the Deligne-factor notation of §1.2.2.2 the same computation reads
$$
 G(\tfrac12)\,G(\tfrac32)=\pi^{-1}\,\Gamma(\tfrac14)\Gamma(\tfrac34)=\sqrt2=2(2\pi)^{-1/2}\,\Gamma(\tfrac12)=\Gamma_{\mathbb C}(\tfrac12),
$$
which is the form of the duplication formula spent in the functional equation (see the table below).

**Proposition 7 (all arguments).** For every complex $s$, as an identity of total functions,
$$
 \Gamma(s)\,\Gamma\bigl(s+\tfrac12\bigr)=\Gamma(2s)\,2^{1-2s}\sqrt\pi ;
$$
in particular the identity holds for every real $s$.

**Proof.** The functions $z\mapsto\Gamma(z)^{-1}\Gamma(z+\tfrac12)^{-1}$ and $z\mapsto\Gamma(2z)^{-1}2^{2z-1}/\sqrt\pi$ are entire, because $1/\Gamma$ is entire (§1.2.2.2) and $2^{2z-1}=e^{(2z-1)\log2}$. By Theorem 6 they agree at every real $t>0$, in particular on a punctured real neighbourhood of $1$, which accumulates at $1$. By the identity theorem the two entire functions are equal. Inverting both sides gives the formula at every $s$: in Mathlib $0^{-1}=0$, so inversion is an involution of $\mathbb C$, and at the poles both sides equal $0$. Restricting to real arguments gives the real identity. $\square$

This is `Complex.Gamma_mul_Gamma_add_half`. The entire reciprocals come from `differentiable_one_div_Gamma` (read in §1.2.2.2). The frequent agreement in the punctured neighbourhood `𝓝[≠] 1` is obtained from `eventually_gt_nhds zero_lt_one`, that is from real $t>0$ near $1$, pushed forward along the inclusion $\mathbb R\to\mathbb C$, and then `AnalyticOnNhd.eq_of_frequently_eq` is applied. The single call of the positive-real theorem is at line 586. `Real.Gamma_mul_Gamma_add_half` restricts by `ofReal_inj`. [Lean, read] [Beta.lean:559–601](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L559-L601) · [IsolatedZeros.lean:261](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/IsolatedZeros.lean#L261)

**Where the two inputs are spent.** Outside `BohrMollerup.lean`, a search of the whole pinned Mathlib tree finds exactly the following direct calls of these statements; the last row follows one path further, to the functional equation used in this chapter.

| Statement | Direct consumer at the pinned commit | Use in this book |
|---|---|---|
| Theorem 1, `convexOn_log_Gamma` | `Real.deriv_Gamma_nat`, [GammaDeriv.lean:44](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/GammaDeriv.lean#L44), slope bounds at lines 65–74 | §1.2.2.4, the derivative at the positive integers through $\log n\le\psi(n+1)\le\log(n+1)$ |
| Theorem 6, `Gamma_mul_Gamma_add_half_of_pos` | `Complex.Gamma_mul_Gamma_add_half`, [Beta.lean:586](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L586) (its only call) | Proposition 7 |
| Proposition 7, real form | `Real.hasDerivAt_Gamma_one_half`, [GammaDeriv.lean:117](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/GammaDeriv.lean#L117) (`funext Gamma_mul_Gamma_add_half`) | §1.2.2.4, hand calculation A: $\Gamma'(1/2)=-\sqrt\pi(\gamma+2\log2)$, hence $G'(1)$ |
| Proposition 7, complex form | `Gammaℝ_mul_Gammaℝ_add_one`, $G(s)G(s+1)=\Gamma_{\mathbb C}(s)$, [Deligne.lean:122–135](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L122-L135); then `Gammaℝ_div_Gammaℝ_one_sub` (155–166), `inv_Gammaℝ_one_sub` (170–181), `hurwitzZetaEven_one_sub` ([HurwitzZetaEven.lean:760–769](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L760-L769)) and `riemannZeta_one_sub` ([RiemannZeta.lean:178–180](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L178-L180)) | §1.2.3 and §1.4.2: the cosine form of the functional equation, called by the archive's `Formalism.VW.rh_of_right` at `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:28` |

In the last row the duplication formula supplies the numerator and the reflection formula of Chapter 2 the denominator of
$$
 \frac{G(s)}{G(1-s)}=\frac{G(s)\,G(s+1)}{G(1-s)\,G(1+s)}=\frac{\Gamma_{\mathbb C}(s)}{1/\cos(\pi s/2)}=\Gamma_{\mathbb C}(s)\cos\frac{\pi s}2\qquad(s\ne-1,-3,-5,\dots),
$$
the excluded points being those where $G(s+1)=0$. This is how the symmetric equation $\Lambda(1-s)=\Lambda(s)$ becomes $\zeta(1-s)=2(2\pi)^{-s}\Gamma(s)\cos(\pi s/2)\zeta(s)$. The archive also calls the Bohr–Mollerup development directly. `GlobalTheory.CompanionTheory.DigammaLimit.euler_seq_le_Gamma` (`src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean:8–29`) applies `Real.BohrMollerup.ge_logGammaSeq` with `Real.convexOn_log_Gamma` to obtain the lower bound $Q_n(x)\le\Gamma(x)$ of Lemma 4, and uses it to dominate the complex Gauss quotients on a circle in the proof of a digamma limit. Whether that file lies in the dependency closure of the main theorems is not determined here.

**The counterexample revisited.** For $f=\Gamma\cdot(1+\sin^2\pi x)$, conditions (1)–(3) of Theorem 5 hold and (4) fails, and the failure sits exactly where the proof uses (4). Lemma 3(1) at $n=1$, $x=\tfrac12$ would give $\log f(\tfrac32)\le\log f(1)=0$, but $f(\tfrac32)=2\Gamma(\tfrac32)=\sqrt\pi>1$. The sequence $L_n(x)$ is the same for every candidate $f$, and it converges to $\log\Gamma(x)$, whereas $\log f(x)-\log f(1)=\log\Gamma(x)+\log(1+\sin^2\pi x)$; at $x=\tfrac12$ these numbers are $\log\sqrt\pi\approx0.57236$ and $\log(2\sqrt\pi)\approx1.26551$. In general, if $p>0$ has period $1$ and $p(1)=1$, Theorem 5 applied to $\Gamma p$ shows that $\log(\Gamma p)$ is convex only when $p\equiv1$. The proof of Lemma 4 uses Lemma 3 only for large $n$, so convexity of $\log f$ on a half-line $(a,\infty)$, together with (1)–(3), would already force $f=\Gamma$ [Expository]. Accordingly, for small amplitudes the defect shows up only far out: for $f=\Gamma\cdot(1+\tfrac1{100}\sin^2\pi x)$ the midpoint inequality on $[n,n+1]$ holds for $n\le12$ and fails for every $n\ge13$ that we tested (floating-point check up to $n=10^5$).

**Remarks.**

1. *Hölder versus Riemann sums.* Artin proves the log-convexity of $\int\varphi(t)\,t^{x-1}\,dt$ from the facts that sums and limits of log-convex functions are log-convex, approximating the integral by Riemann sums (Theorem 1.9, pp. 9–10). Mathlib applies Hölder's inequality to the improper integral directly. The Hölder of Mathlib's docstring is the integral inequality; it is unrelated to Hölder's theorem on the differential transcendence of $\Gamma$, which Artin's preface lists among the topics not treated.

2. *The constant.* Artin proves Gauss's multiplication formula $p^x\,\Gamma(\tfrac xp)\Gamma(\tfrac{x+1}p)\cdots\Gamma(\tfrac{x+p-1}p)=a_p\Gamma(x)$ by the same uniqueness argument, with an unknown constant $a_p$. He computes $a_p$ from the Gauss product and Stirling's formula, fixing the last constant by $a_2=2\Gamma(\tfrac12)=2\sqrt\pi$, and attributes the case $p=2$ to Legendre (pp. 22–24). Mathlib treats only $p=2$ and fixes the constant directly at $s=1$, where $D(1)=\Gamma(\tfrac12)/\sqrt\pi$. This is the only point at which the Gaussian integral enters the duplication formula; the general multiplication formula is recorded as a TODO in the file header (lines 36–38).

3. *No regularity is assumed.* Theorem 5 assumes neither continuity nor differentiability, and the real-analytic counterexample shows that regularity would not replace convexity. Positivity (1) is what makes $\log f$ the honest logarithm: Mathlib's `Real.log` is total, with $\log0=0$ and $\log(-x)=\log x$.

4. *Local versus global.* The derivative at $\tfrac12$ in §1.2.2.4 depends only on the duplication formula near $s=\tfrac12$, which Theorem 6 already supplies on $(0,\infty)$. The Lean proof nevertheless uses the global real identity, because it rewrites the function under `deriv` with `funext`. The complex extension of Proposition 7 is genuinely needed by the second consumer, which uses $G(s)G(s+1)=\Gamma_{\mathbb C}(s)$ at complex $s$.

5. *Two productions of the Gauss limit.* Theorem 5 yields $Q_n(x)\to\Gamma(x)$ for real $x>0$; the file header calls this a weak form of the Euler limit formula. Chapter 2, §2.3.2.1 reads the complex limit `Complex.GammaSeq_tendsto_Gamma` (`Beta.lean:335`), which Mathlib proves separately from the integral.

**Source note.** The reading is R3 for `BohrMollerup.lean:58–120` (Theorem 1), `138–318` (Lemmas 2–4 and Theorem 5) and `375–452` (Theorem 6); for `Beta.lean:559–601` (Proposition 7, whose structure only was read in §1.2.2.4); for the consumer bodies `Deligne.lean:122–181`, `HurwitzZetaEven.lean:760–769` and `RiemannZeta.lean:178–180`; for the Hölder wrappers `Bochner/Basic.lean:1144–1209`; and for the archive consumers `RhOfRight.lean:28` and `DigammaTendstoLogSubHarmonic.lean:8–29`. Inputs retained by name (statements read, bodies not read) are the Hölder core `ENNReal.lintegral_mul_le_Lp_mul_Lq`; the Gaussian value `Real.Gamma_one_half_eq`; `Complex.Gamma_one`, the evaluation of Euler's integral at $s=1$ behind the real normalization; the convexity library (`convexOn_iff_forall_pos`, `convexOn_iff_slope_mono_adjacent`, `ConvexOn.comp_affineMap`, `ConvexOn.subset`, `ConvexOn.add`, `ConvexOn.smul`, `convexOn_id`); `Real.holderConjugate_one_div`, `memLp_norm_rpow_iff`, `memLp_one_iff_integrable`, `tendsto_log_nat_add_one_sub_log` and `log_injOn_pos`; the identity theorem `AnalyticOnNhd.eq_of_frequently_eq`; and `completedHurwitzZetaEven_one_sub` (read in §1.2.2.6). Inherited from earlier sections are Euler's integral (`GammaIntegral_convergent`, `Real.Gamma_eq_integral`), the recurrence and `Real.Gamma_pos_of_pos` ([Chapter 2, §2.3.2.3](02-functional-equations-and-primitive-characters.md#2323-eulers-integral-for-gamma-convergence-at-both-ends-and-what-gamma_eq_integral-actually-proves)), the reflection formula (Chapter 2, §2.3.2.1) and `differentiable_one_div_Gamma` (§1.2.2.2); the real transfers `Real.Gamma_add_one` and `Real.Gamma_one` were read here. The [proof map](../notes/proof-map.md#p1-chapter-1-log-convexity-bohrmollerup-and-duplication) gives pinned paths and lines. Artin's monograph was read in the 1964 English translation; the 1922 text of Bohr and Mollerup was not read. The hand calculations A and B, the counterexample and the consumer table are ours; the numbers were cross-checked in floating point, which is a consistency check, not a certificate. This reading does not certify the dependency cone, and no Lean compilation was run.

#### 1.2.2.6 From the theta transformation to the completed Hurwitz functional equation

**Motivation.** Section 1.2.2.1 used the theta transformation $f_a(t)=t^{-1/2}g_a(1/t)$ in one direction only: to read the small-$t$ asymptotic of $f_a$ off the large-$t$ limit of $g_a$, subtract the singular powers below $t=1$, and continue the completed even Hurwitz function meromorphically to $\mathbb C$ with its simple pole at $s=1$. Section 1.2.2.5 then supplied the archimedean Gamma ratio $G(s)/G(1-s)=\Gamma_{\mathbb C}(s)\cos(\pi s/2)$ from the duplication and reflection formulas, leaving a single named input between the Jacobi theta kernel and the functional equation `riemannZeta_one_sub` consumed by the archive's `rh_of_right`: the completed reflection `completedHurwitzZetaEven_one_sub`.

Two analytical obstacles stand between the pointwise theta law $f_a(1/x)=x^{1/2}g_a(x)$ and a global functional equation on $\mathbb C$. First, the unmodified Mellin integrals of $f_a$ and $g_a$ diverge on half-planes (and for $f_a$ with $a=0$, at every complex $s$), so changing variables $t\mapsto 1/t$ directly in $\int_0^\infty t^{w-1}f_a(t)\,dt$ manipulates an integral whose domain of convergence is empty. Second, for a nonzero shift $a\in\mathbb R/\mathbb Z\setminus\{0\}$, the pair $(f_a,g_a)$ is not self-dual: $f_a(t)\to 0$ as $t\to\infty$ whereas $g_a(t)\to 1$, so reflection across $s\mapsto 1-s$ does not send the even Hurwitz zeta function back to itself, but exchanges it with a dual *cosine zeta* partner while swapping the pole locations $s=0$ and $s=1$. Mathlib packages both phenomena into the conditional interface `WeakFEPair`, builds an entire partner pair by piecewise subtraction with a deliberate zero at the seam $t=1$, proves Mellin inversion on the entire modified pair, and cancels the two rational pole terms algebraically before specializing to $a\in\mathbb R/\mathbb Z$ and $a=0$.

**Example (two traps: Bochner degeneracy on unmodified kernels and the seam defect at $x=1$).** Before stating the general interface, test the naive Mellin inversion on two concrete kernels from §1.2.2.1.

1. *Empty convergence strip and Bochner totalization.* At $a=0$, $f_0(t)=g_0(t)=1+2\sum_{n\ge1}e^{-\pi n^2 t}$ tends to $1$ as $t\to\infty$ and behaves like $t^{-1/2}$ as $t\to0^+$. For every $w\in\mathbb C$, $t^{w-1}f_0(t)$ fails to be integrable on $(0,\infty)$: at $\infty$ convergence would require $\Re w<0$, whereas at $0$ it requires $\Re w>1/2$. In Mathlib, `mellin f w` is defined as a Bochner integral, which returns $0$ whenever the integrand is not integrable. Substituting $t\mapsto 1/t$ in `mellin f_0 (1/2 - w) = mellin g_0 w` is therefore *formally true* in Lean — both sides evaluate to $0=0$ for every $w\in\mathbb C$ — and proves nothing about $\zeta(s)$! Even if one subtracts the constant at $\infty$ beforehand, $(f_0(t)-1)=O(e^{-\pi t})$ at $\infty$ and $\sim t^{-1/2}$ at $0$, so $\int_0^\infty t^{w-1}(f_0(t)-1)\,dt$ converges on $\Re w>1/2$, while the reflected argument $1/2-w$ requires $\Re(1/2-w)>1/2$, i.e. $\Re w<0$, giving two *disjoint* half-planes. One must pass to kernels modified on $(0,1)$ and $(1,\infty)$ separately so that both sides converge on all of $\mathbb C$ simultaneously.

2. *The seam mismatch at $x=1$ when $f_\infty\ne\varepsilon g_\infty$.* Take $a=1/3$. Here $f_{1/3}(t)=\sum_{n\in\mathbb Z}e^{-\pi(n+1/3)^2 t}\to 0$ as $t\to\infty$ ($f_\infty=0$), whereas $g_{1/3}(t)=1+2\sum_{n\ge1}\cos(2\pi n/3)e^{-\pi n^2 t}\to 1$ ($g_\infty=1$), with weight $k=1/2$ and root number $\varepsilon=1$. At the inversion fixed point $x=1$, the theta identity $f_{1/3}(1/x)=x^{1/2}g_{1/3}(x)$ gives $f_{1/3}(1)=g_{1/3}(1)$ ($\approx 0.95678$). Suppose one defined the upper-tail subtraction on the *closed* ray $[1,\infty)$ and the lower-tail subtraction on $(0,1)$. Then at $x=1$ the modified $f$-kernel would take the value $f_{1/3}(1)-0=f_{1/3}(1)$, whereas the modified $g$-kernel would take the value $g_{1/3}(1)-1=f_{1/3}(1)-1$. Their difference at $x=1$ is $+1\ne0$, breaking the pointwise functional equation $f_{\mathrm{modif}}(1/x)=\varepsilon x^k g_{\mathrm{modif}}(x)$ at $x=1$. Replacing $[1,\infty)$ by the open ray $(1,\infty)$ sets both modified kernels to $0$ at $x=1$, restoring exact pointwise symmetry without altering any Lebesgue integral because $\{1\}$ has measure zero.

**Definition (`WeakFEPair`, dual pair, piecewise modification, and $\Lambda_0,\Lambda$).** Let $E$ be a normed $\mathbb C$-vector space (in all our applications $E=\mathbb C$). A *weak functional-equation pair* $P$ (`WeakFEPair E`) consists of data $(f,g,k,\varepsilon,f_0,g_0)$ with $f,g:(0,\infty)\to E$ (extended arbitrarily to $\mathbb R$), real weight $k\in\mathbb R$, scalar $\varepsilon\in\mathbb C$, and asymptotic constants $f_0,g_0\in E$, subject to the seven hypotheses:

1. $f$ and $g$ are locally integrable on $(0,\infty)$ (`hf_int`, `hg_int`);
2. $k>0$ and $\varepsilon\ne0$ (`hk`, `hε`);
3. for every $x>0$, $f(1/x)=\varepsilon x^k g(x)$ (`h_feq`);
4. for every $r\in\mathbb R$, $f(x)-f_0=O(x^r)$ and $g(x)-g_0=O(x^r)$ as $x\to\infty$ (`hf_top`, `hg_top`).

We say that $P$ is a *strong functional-equation pair* (`IsStrongFEPair P`) if $f_0=0$ and $g_0=0$. Given any weak pair $P$, define:

- the *dual (symmetric) data* $P^{\mathrm{symm}}=(g,f,k,\varepsilon^{-1},g_0,f_0)$ (`WeakFEPair.symm`);
- the *piecewise modified kernels* (`WeakFEPair.f_modif`, `WeakFEPair.g_modif`) for $x\in\mathbb R$:
$$
 f_{\mathrm{modif}}(x)=\mathbf 1_{(1,\infty)}(x)\bigl(f(x)-f_0\bigr)+\mathbf 1_{(0,1)}(x)\bigl(f(x)-\varepsilon x^{-k}g_0\bigr),
$$
$$
 g_{\mathrm{modif}}(x)=\mathbf 1_{(1,\infty)}(x)\bigl(g(x)-g_0\bigr)+\mathbf 1_{(0,1)}(x)\bigl(g(x)-\varepsilon^{-1}x^{-k}f_0\bigr);
$$
- the *pole-removed* and *meromorphic Mellin transforms* (`WeakFEPair.Λ₀`, `WeakFEPair.Λ`), for $E$ complete and $s\in\mathbb C$:
$$
 \Lambda_0(P,s)=\mathcal M(f_{\mathrm{modif}})(s)=\int_0^\infty t^{s-1}f_{\mathrm{modif}}(t)\,dt,\qquad
 \Lambda(P,s)=\Lambda_0(P,s)-\frac{1}{s}f_0-\frac{\varepsilon}{k-s}g_0,
$$
where in Lean's total arithmetic on $\mathbb C$ division by zero evaluates to $0$ ($z/0=0$). [Lean, read] [AbstractFuncEq.lean:80–138](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L80-L138) · [AbstractFuncEq.lean:247–255](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L247-L255) · [AbstractFuncEq.lean:376–388](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L376-L388)

Notice that $g_{\mathrm{modif}}$ is obtained from $f_{\mathrm{modif}}$ simply by replacing $(f,g,\varepsilon,f_0,g_0)$ with $(g,f,\varepsilon^{-1},g_0,f_0)$. Once Lemma 1 verifies that $P^{\mathrm{symm}}$ is itself a valid `WeakFEPair`, $(P^{\mathrm{symm}}).f_{\mathrm{modif}}$ is definitionally equal to $g_{\mathrm{modif}}$.

**Lemma 1 (dual kernel law and strong-pair modification).** Let $P=(f,g,k,\varepsilon,f_0,g_0)$ be a `WeakFEPair`.

1. For every $x>0$, $g(1/x)=\varepsilon^{-1}x^k f(x)$, and $P^{\mathrm{symm}}$ satisfies all seven `WeakFEPair` axioms.
2. For every $x>0$, $f_{\mathrm{modif}}(1/x)=\varepsilon x^k g_{\mathrm{modif}}(x)$, and $P_{\mathrm{strong}}=(f_{\mathrm{modif}},g_{\mathrm{modif}},k,\varepsilon,0,0)$ is a strong `WeakFEPair` (`toStrongFEPair`, `isStrongFEPair_toStrongFEPair`). Consequently, for every $r\in\mathbb R$, both $f_{\mathrm{modif}}(x)$ and $g_{\mathrm{modif}}(x)$ are $O(x^r)$ as $x\to\infty$ and as $x\to0^+$, so their Mellin integrals converge absolutely and define entire functions of $s\in\mathbb C$.

**Proof.** (1) Let $x>0$, so $1/x>0$ and $x^k>0$. Applying hypothesis (3) at $1/x$ gives $f(x)=f\bigl(1/(1/x)\bigr)=\varepsilon(1/x)^k g(1/x)=\varepsilon x^{-k}g(1/x)$. Because $\varepsilon\ne0$ and $x^k\ne0$, multiplying both sides by $\varepsilon^{-1}x^k$ cancels $\varepsilon x^{-k}$ and yields $g(1/x)=\varepsilon^{-1}x^k f(x)$. Since $\varepsilon^{-1}\ne0$, $k>0$, and the local-integrability and $\infty$-decay hypotheses of $P^{\mathrm{symm}}$ are literally those of $P$ in reverse order, $P^{\mathrm{symm}}$ is a `WeakFEPair`.

(2) Fix $x>0$ and split by trichotomy at $1$.

- *Case $x>1$.* Then $0<1/x<1$, so $f_{\mathrm{modif}}(1/x)=f(1/x)-\varepsilon(1/x)^{-k}g_0$ from the $(0,1)$ branch and $g_{\mathrm{modif}}(x)=g(x)-g_0$ from the $(1,\infty)$ branch. Using $(1/x)^{-k}=x^k$ and $f(1/x)=\varepsilon x^k g(x)$, we obtain
$$
 f_{\mathrm{modif}}(1/x)=\varepsilon x^k g(x)-\varepsilon x^k g_0=\varepsilon x^k\bigl(g(x)-g_0\bigr)=\varepsilon x^k g_{\mathrm{modif}}(x).
$$
- *Case $x=1$.* Since $1\notin(1,\infty)$ and $1\notin(0,1)$, both $f_{\mathrm{modif}}(1)$ and $g_{\mathrm{modif}}(1)$ equal $0$, and $0=\varepsilon\cdot 1^k\cdot 0$.
- *Case $0<x<1$.* Then $1/x>1$, so $f_{\mathrm{modif}}(1/x)=f(1/x)-f_0$ and $g_{\mathrm{modif}}(x)=g(x)-\varepsilon^{-1}x^{-k}f_0$. Using $f(1/x)=\varepsilon x^k g(x)$ together with $\varepsilon x^k\cdot\varepsilon^{-1}x^{-k}=1$ ($\varepsilon\ne0$, $x^k\ne0$), we have
$$
 \varepsilon x^k g_{\mathrm{modif}}(x)=\varepsilon x^k g(x)-\bigl(\varepsilon x^k\varepsilon^{-1}x^{-k}\bigr)f_0=f(1/x)-f_0=f_{\mathrm{modif}}(1/x).
$$

On $(0,\infty)$, the power $x\mapsto\varepsilon x^{-k}g_0$ is continuous, hence locally integrable; subtracting constants or continuous functions and multiplying by the measurable indicators of $(1,\infty)$ and $(0,1)$ preserves local integrability on $(0,\infty)$. For $x>1$, $f_{\mathrm{modif}}(x)=f(x)-f_0=O(x^r)$ for every $r\in\mathbb R$ by hypothesis (4); the same argument applied to $P^{\mathrm{symm}}$ gives local integrability and rapid decay at $\infty$ for $g_{\mathrm{modif}}$. Thus $P_{\mathrm{strong}}$ is a `WeakFEPair` with $(f_0,g_0)=(0,0)$. Rapid decay as $x\to0^+$ follows by substituting $1/x\to\infty$ into $f_{\mathrm{modif}}(x)=\varepsilon x^{-k}g_{\mathrm{modif}}(1/x)$ with exponent $-(r+k)$, and global Mellin convergence and complex differentiability follow from the endpoint-power criteria established in §1.2.2.1. $\square$

In Lean, part (1) is `WeakFEPair.h_feq'` and `WeakFEPair.symm` (`field [P.hε, (rpow_pos_of_pos hx _).ne']` clears the scalar). Part (2) is `hf_modif_int`, `hf_modif_FE` (`rcases lt_trichotomy 1 x with hx' | rfl | hx'`), `hf_modif_top`, `toStrongFEPair` (whose `g` field is `P.symm.f_modif`, definitionally `P.g_modif`), and `isStrongFEPair_toStrongFEPair`. Global convergence and holomorphy of a strong pair are `IsStrongFEPair.mellinConvergent` and `IsStrongFEPair.differentiable_mellin` (inherited from §1.2.2.1 via `mellinConvergent_of_isBigO_rpow` and `mellin_differentiableAt_of_isBigO_rpow`). [Lean, read] [AbstractFuncEq.lean:107–138](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L107-L138) · [AbstractFuncEq.lean:213–316](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L213-L316)

**Lemma 2 (Mellin inversion on $(0,\infty)$ and `WeakFEPair.functional_equation₀`).** Let $E$ be a complete normed $\mathbb C$-vector space and let $P=(f,g,k,\varepsilon,f_0,g_0)$ be a `WeakFEPair`.

1. For every $s\in\mathbb C$, as an equality of Bochner integrals on $(0,\infty)$,
$$
 \mathcal M(f)(k-s)=\varepsilon\,\mathcal M(g)(s).
$$
2. Applying (1) to the strong pair $P_{\mathrm{strong}}$ gives, for every $s\in\mathbb C$, the convergent entire identity
$$
 \Lambda_0(P,k-s)=\varepsilon\,\Lambda_0(P^{\mathrm{symm}},s),
$$
and both sides equal the two-tail integral on $(1,\infty)$:
$$
 \Lambda_0(P,k-s)=\int_1^\infty t^{k-s-1}\bigl(f(t)-f_0\bigr)\,dt+\varepsilon\int_1^\infty t^{s-1}\bigl(g(t)-g_0\bigr)\,dt.
$$

**Proof.** (1) The diffeomorphism $\varphi:(0,\infty)\to(0,\infty)$, $\varphi(t)=t^{-1}$, is injective and maps $(0,\infty)$ onto $(0,\infty)$, with $\lvert\varphi'(t)\rvert=\lvert-t^{-2}\rvert=t^{-2}$. By the change-of-variables formula on $(0,\infty)$ applied to $y\mapsto y^{-s-1}g(y)$ at exponent $p=-1$,
$$
 \mathcal M(g)(-s)=\int_0^\infty y^{-s-1}g(y)\,dy=\int_0^\infty t^{-2}\,(t^{-1})^{-s-1}g(1/t)\,dt=\int_0^\infty t^{s-1}g(1/t)\,dt=\mathcal M\bigl(t\mapsto g(1/t)\bigr)(s),
$$
and replacing $-s$ by $s$ gives $\mathcal M(g)(s)=\mathcal M(t\mapsto g(1/t))(-s)$. Next, for every $t>0$, $t^{(k-s)-1}\cdot t^{-k}=t^{-s-1}$ because $t>0$ has real logarithm and $(k-s-1)+(-k)=-s-1$; hence shifting the Mellin weight by $-k$ gives
$$
 \mathcal M\bigl(t\mapsto t^{-k}g(1/t)\bigr)(k-s)=\mathcal M\bigl(t\mapsto g(1/t)\bigr)(-s)=\mathcal M(g)(s).
$$
Pulling the constant scalar $\varepsilon\in\mathbb C$ through the Bochner integral yields
$$
 \varepsilon\,\mathcal M(g)(s)=\mathcal M\bigl(t\mapsto\varepsilon t^{-k}g(1/t)\bigr)(k-s)=\int_0^\infty t^{k-s-1}\varepsilon t^{-k}g(1/t)\,dt.
$$
Now use Lemma 1(1): for every $t>0$, $g(1/t)=\varepsilon^{-1}t^k f(t)$, and since $\varepsilon\ne0$ and $t^k>0$, $\varepsilon t^{-k}(\varepsilon^{-1}t^k f(t))=f(t)$ pointwise on $(0,\infty)$. Therefore the right-hand integral is literally $\int_0^\infty t^{k-s-1}f(t)\,dt=\mathcal M(f)(k-s)$. Every step (bijective change of variables, pointwise rewriting on $(0,\infty)$, and scalar multiplication by $\varepsilon\ne0$) preserves non-integrability as well as integrability, so the Bochner identity holds for all $s\in\mathbb C$.

(2) By Lemma 1(2), $P_{\mathrm{strong}}$ is a `WeakFEPair` whose Mellin transforms converge at every complex argument, with $(P_{\mathrm{strong}})^{\mathrm{symm}}$ having first kernel $g_{\mathrm{modif}}=(P^{\mathrm{symm}}).f_{\mathrm{modif}}$. Applying (1) to $P_{\mathrm{strong}}$ gives
$$
 \Lambda_0(P,k-s)=\mathcal M(f_{\mathrm{modif}})(k-s)=\varepsilon\,\mathcal M(g_{\mathrm{modif}})(s)=\varepsilon\,\Lambda_0(P^{\mathrm{symm}},s).
$$
Finally, split $\Lambda_0(P,k-s)=\int_0^\infty t^{k-s-1}f_{\mathrm{modif}}(t)\,dt$ across $(0,1)$, $\{1\}$, and $(1,\infty)$. The singleton $\{1\}$ has measure zero; on $(1,\infty)$, $f_{\mathrm{modif}}(t)=f(t)-f_0$; on $(0,1)$, $f_{\mathrm{modif}}(t)=\varepsilon t^{-k}g_{\mathrm{modif}}(1/t)=\varepsilon t^{-k}(g(1/t)-g_0)$, and substituting $u=1/t$ sends $\int_0^1 t^{k-s-1}\varepsilon t^{-k}(g(1/t)-g_0)\,dt$ to $\varepsilon\int_1^\infty u^{s-1}(g(u)-g_0)\,du$. $\square$

In Lean, part (1) is `private theorem WeakFEPair.functional_equation_aux` (located in `namespace WeakFEPair`, not `IsStrongFEPair`). It chains `step1 := mellin_comp_rpow P.g (-s) (-1)`, `step2 := mellin_cpow_smul (fun t ↦ P.g (1 / t)) (P.k - s) (-P.k)`, and `step3 := mellin_const_smul … (P.k - s) P.ε`, then rewrites the integrand on `Ioi 0` via `setIntegral_congr_fun` and `P.h_feq' t ht`, finishing with `field_simp [P.hε]` and `(t : ℂ) ^ (P.k : ℂ) ≠ 0`. In `MellinTransform.lean`, the header comments on lines 99 and 118 explicitly note that `mellin_cpow_smul`, `mellin_const_smul`, and `mellin_comp_rpow` require no convergence hypothesis (reducing to `0 = 0` otherwise); `mellin_comp_rpow` calls `integral_comp_rpow_Ioi` (`IntegralEqImproper.lean:1131–1143`), which proves $(0,\infty)^p=(0,\infty)$ for $p\ne0$ via $x\mapsto x^{1/p}$ and invokes the general Jacobian theorem `integral_image_eq_integral_abs_deriv_smul` (retained here as a named measure-theory input; compare [Chapter 2, §§2.3.2.3–2.3.2.4](02-functional-equations-and-primitive-characters.md#2324-nonnegative-derivatives-and-improper-integrals-the-integrability-criteria-behind-both-ends-of-eulers-integral) for improper-integral conventions in `IntegralEqImproper.lean`). Part (2) is the one-line theorem `WeakFEPair.functional_equation₀`: `P.toStrongFEPair.functional_equation_aux s`. [Lean, read] [AbstractFuncEq.lean:184–203](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L184-L203) · [AbstractFuncEq.lean:420–423](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L420-L423) · [MellinTransform.lean:99–132](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/MellinTransform.lean#L99-L132) · [IntegralEqImproper.lean:1131–1143](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L1131-L1143)

**Lemma 3 (pole-pair swap and `WeakFEPair.functional_equation`).** Let $E$ be a complete normed $\mathbb C$-vector space and let $P=(f,g,k,\varepsilon,f_0,g_0)$ be a `WeakFEPair`.

1. On the half-plane $\Re s>k$, the Mellin integral of $f(x)-f_0$ converges and equals $\Lambda(P,s)$ (`hasMellin`, inherited from §1.2.2.1); $\Lambda(P,s)$ is complex-differentiable at every $s$ satisfying $(s\ne0\text{ or }f_0=0)$ and $(s\ne k\text{ or }g_0=0)$.
2. For *every* $s\in\mathbb C$ (including $s=0$ and $s=k$ under Lean's total division $z/0=0$),
$$
 \Lambda(P,k-s)=\varepsilon\,\Lambda(P^{\mathrm{symm}},s).
$$

**Proof.** Part (1) was read in §1.2.2.1 (`f_modif_aux1`, `f_modif_aux2`, `hasMellin`, `differentiableAt_Λ`): on $\Re s>k>0$, subtracting $f(x)-f_0$ from $f_{\mathrm{modif}}(x)$ leaves $f_0-\varepsilon x^{-k}g_0$ on $(0,1)$ (plus a negligible singleton at $x=1$), whose Mellin integral is $\frac{1}{s}f_0+\frac{\varepsilon}{k-s}g_0$.

For part (2), fix any $s\in\mathbb C$. Unfolding $\Lambda(P,k-s)$ and using the algebraic identity $k-(k-s)=s$ gives
$$
 \Lambda(P,k-s)=\Lambda_0(P,k-s)-\frac{1}{k-s}f_0-\frac{\varepsilon}{s}g_0.
$$
Unfolding $\Lambda(P^{\mathrm{symm}},s)$ from the definition of $P^{\mathrm{symm}}=(g,f,k,\varepsilon^{-1},g_0,f_0)$ gives
$$
 \Lambda(P^{\mathrm{symm}},s)=\Lambda_0(P^{\mathrm{symm}},s)-\frac{1}{s}g_0-\frac{\varepsilon^{-1}}{k-s}f_0.
$$
Multiply the second equation by $\varepsilon$. Because $\varepsilon\ne0$, $\varepsilon\varepsilon^{-1}=1$, so in $\mathbb C$ (even when $k-s=0$, where $\frac{z}{0}=0$ gives $\varepsilon\cdot\frac{\varepsilon^{-1}}{0}=\varepsilon\cdot0=0=\frac{1}{0}$) we have $\varepsilon\cdot\frac{\varepsilon^{-1}}{k-s}=\frac{\varepsilon\varepsilon^{-1}}{k-s}=\frac{1}{k-s}$:
$$
 \varepsilon\,\Lambda(P^{\mathrm{symm}},s)=\varepsilon\,\Lambda_0(P^{\mathrm{symm}},s)-\frac{\varepsilon}{s}g_0-\frac{1}{k-s}f_0.
$$
By Lemma 2(2), $\Lambda_0(P,k-s)=\varepsilon\,\Lambda_0(P^{\mathrm{symm}},s)$, and the two pole-correction pairs $-\frac{1}{k-s}f_0-\frac{\varepsilon}{s}g_0$ and $-\frac{\varepsilon}{s}g_0-\frac{1}{k-s}f_0$ are identical in reverse order. Hence $\Lambda(P,k-s)=\varepsilon\,\Lambda(P^{\mathrm{symm}},s)$ for all $s\in\mathbb C$. $\square$

In Lean, `Λ₀_eq` writes `P.Λ₀ s = P.Λ s + (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g₀`, `symm_Λ₀_eq` expands the same identity for `P.symm`, and `WeakFEPair.functional_equation` combines four module equalities in a single `linear_combination (norm := module)` line:
`P.functional_equation₀ s - P.Λ₀_eq (P.k - s) + congr(P.ε • $(P.symm_Λ₀_eq s)) + congr(($(mul_inv_cancel₀ P.hε) / (P.k - s)) • P.f₀)`. [Lean, read] [AbstractFuncEq.lean:381–388](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L381-L388) · [AbstractFuncEq.lean:424–429](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L424-L429)

**Theorem 4 (completed even Hurwitz and cosine functional equations, series identification, and $a=0$ self-duality).** Assume the Gaussian Poisson summation input (`Complex.tsum_exp_neg_quadratic`), which supplies $f_a(1/x)=x^{1/2}g_a(x)$ for every $a\in\mathbb R/\mathbb Z$ and $x>0$ (§1.2.2.1). For each $a\in\mathbb R/\mathbb Z$, set $\delta_a=1$ if $a=0$ and $\delta_a=0$ if $a\ne0$.

1. *The even Hurwitz FE-pair.* The tuple $P_a=(f_a,g_a,1/2,1,\delta_a,1)$ is a `WeakFEPair` over $\mathbb C$ (`hurwitzEvenFEPair a`), with dual $P_a^{\mathrm{symm}}=(g_a,f_a,1/2,1,1,\delta_a)$ satisfying $P_{-a}=P_a$ and, at $a=0$, $P_0^{\mathrm{symm}}=P_0$.
2. *Rescaled completions and pole swap.* Define for $s\in\mathbb C$
$$
 \Lambda_{\mathrm{even},0}(a,s)=\tfrac12\Lambda_0(P_a,s/2),\qquad
 \Lambda_{\mathrm{even}}(a,s)=\tfrac12\Lambda(P_a,s/2),
$$
$$
 \Lambda_{\cos,0}(a,s)=\tfrac12\Lambda_0(P_a^{\mathrm{symm}},s/2),\qquad
 \Lambda_{\cos}(a,s)=\tfrac12\Lambda(P_a^{\mathrm{symm}},s/2).
$$
Then $\Lambda_{\mathrm{even},0}(a,\cdot)$ and $\Lambda_{\cos,0}(a,\cdot)$ are entire,
$$
 \Lambda_{\mathrm{even}}(a,s)=\Lambda_{\mathrm{even},0}(a,s)-\frac{\delta_a}{s}-\frac{1}{1-s},\qquad
 \Lambda_{\cos}(a,s)=\Lambda_{\cos,0}(a,s)-\frac{1}{s}-\frac{\delta_a}{1-s},
$$
and for *every* $a\in\mathbb R/\mathbb Z$ and *every* $s\in\mathbb C$,
$$
 \Lambda_{\mathrm{even},0}(a,1-s)=\Lambda_{\cos,0}(a,s),\qquad
 \Lambda_{\mathrm{even}}(a,1-s)=\Lambda_{\cos}(a,s).
$$
3. *Dirichlet series and un-completed functions.* Recall $G(s)=\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$ and define total functions on $\mathbb C$ by updating at $s=0$:
$$
 E_a(s)=\bigl[\Lambda_{\mathrm{even}}(a,\cdot)/G\bigr]_{0\gets-\delta_a/2},\qquad
 Z_{\cos}(a,s)=\bigl[\Lambda_{\cos}(a,\cdot)/G\bigr]_{0\gets-1/2}.
$$
Then $E_a$ is holomorphic on $\mathbb C\setminus\{1\}$, while $Z_{\cos}(a,\cdot)$ is holomorphic on $\mathbb C\setminus\{1\}$ when $a=0$ and **entire** when $a\ne0$. For every real representative $a\in\mathbb R$ and every $s\in\mathbb C$ with $\Re s>1$,
$$
 \Lambda_{\mathrm{even}}(a,s)=G(s)\,E_a(s),\qquad E_a(s)=\frac12\sum_{\substack{n\in\mathbb Z\\n+a\ne0}}\lvert n+a\rvert^{-s},
$$
$$
 \Lambda_{\cos}(a,s)=G(s)\,Z_{\cos}(a,s),\qquad Z_{\cos}(a,s)=\sum_{n=1}^\infty\frac{\cos(2\pi a n)}{n^s}.
$$
4. *Zero-shift self-duality.* At $a=0$, writing $\Lambda_0(s)=\Lambda_{\mathrm{even},0}(0,s)$, $\Lambda(s)=\Lambda_{\mathrm{even}}(0,s)$, and $\zeta(s)=E_0(s)$, we have $\Lambda_{\cos,0}(0,s)=\Lambda_0(s)$, $\Lambda_{\cos}(0,s)=\Lambda(s)$, $Z_{\cos}(0,s)=\zeta(s)$, and for every $s\in\mathbb C$,
$$
 \Lambda_0(1-s)=\Lambda_0(s),\qquad \Lambda(1-s)=\Lambda(s).
$$

**Proof.** (1) Continuity of $f_a$ and $g_a$ on $(0,\infty)$ (from locally uniform Gaussian comparison in §1.2.2.1) supplies local integrability. By §1.2.2.1, $f_a(x)-\delta_a=O(e^{-c x})$ for some $c>0$ and $g_a(x)-1=O(e^{-\pi x})$ as $x\to\infty$; since $e^{-c x}=o(x^r)$ as $x\to\infty$ for every real $r$, hypotheses `hf_top` and `hg_top` hold. The Poisson-derived Jacobi identity $f_a(1/x)=x^{1/2}g_a(x)$ gives `h_feq` with $k=1/2>0$ and $\varepsilon=1\ne0$. Reindexing $n\mapsto-n$ shows $f_{-a}=f_a$ and $g_{-a}=g_a$. At $a=0$, both kernels equal $\sum_{n\in\mathbb Z}e^{-\pi n^2 x}$ and $\delta_0=1=g_0$, so $P_0^{\mathrm{symm}}$ has the exact same six data fields as $P_0$; by proof irrelevance on the propositional fields, $P_0^{\mathrm{symm}}=P_0$.

(2) Substituting $w=s/2$ into $\Lambda(P_a,w)=\Lambda_0(P_a,w)-\frac{\delta_a}{w}-\frac{1}{1/2-w}$ and dividing by $2$ cancels the factor of $2$ in both denominators:
$$
 \frac{1}{2}\cdot\frac{\delta_a}{s/2}=\frac{\delta_a}{s},\qquad
 \frac{1}{2}\cdot\frac{1}{\frac12-\frac s2}=\frac{1}{1-s}
$$
(including at $s=0$ and $s=1$, where $0/2=0$ and $z/0=0$). The same cancellation in $\frac12\Lambda(P_a^{\mathrm{symm}},s/2)$ swaps $(\delta_a,1)$ to $(1,\delta_a)$, giving $-\frac{1}{s}-\frac{\delta_a}{1-s}$. Now rewrite $\frac{1-s}{2}=\frac12-\frac s2=k-\frac s2$ and apply Lemma 2(2) and Lemma 3(2) at argument $s/2$ with $\varepsilon=1$:
$$
 \Lambda_{\mathrm{even},0}(a,1-s)=\tfrac12\Lambda_0\bigl(P_a,\tfrac12-\tfrac s2\bigr)=\tfrac12\cdot 1\cdot\Lambda_0\bigl(P_a^{\mathrm{symm}},\tfrac s2\bigr)=\Lambda_{\cos,0}(a,s),
$$
$$
 \Lambda_{\mathrm{even}}(a,1-s)=\tfrac12\Lambda\bigl(P_a,\tfrac12-\tfrac s2\bigr)=\tfrac12\cdot 1\cdot\Lambda\bigl(P_a^{\mathrm{symm}},\tfrac s2\bigr)=\Lambda_{\cos}(a,s).
$$

(3) The series and holomorphy of $\Lambda_{\mathrm{even}}$ and $E_a$ were proved in §§1.2.2.1–1.2.2.2 (`P_a, A_a` there are our $\Lambda_{\mathrm{even}}(a,\cdot), \Lambda_{\mathrm{even},0}(a,\cdot)$). For the dual pair $P_a^{\mathrm{symm}}$, when $\Re s>1$ we have $\Re(s/2)>1/2=k$, so Lemma 3(1) applied to $P_a^{\mathrm{symm}}$ identifies $\Lambda_{\cos}(a,s)$ with $\frac12\mathcal M(g_a-1)(s/2)=\mathcal M\bigl((g_a-1)/2\bigr)(s/2)$. Now $(g_a(t)-1)/2=\sum_{n\in\mathbb Z\setminus\{0\}}\frac12 e^{2\pi i a n}e^{-\pi n^2 t}$. For $\sigma=\Re s>1$, the Gaussian Mellin integrals of the moduli equal $\frac12 G(\sigma)\lvert n\rvert^{-\sigma}$, which are summable over $n\in\mathbb Z\setminus\{0\}$; termwise integration via $u=\pi n^2 t$ yields
$$
 \Lambda_{\cos}(a,s)=\sum_{n\in\mathbb Z\setminus\{0\}}\frac{G(s)\,e^{2\pi i a n}}{2\lvert n\rvert^s}
 =G(s)\sum_{n=1}^\infty\frac{e^{2\pi i a n}+e^{-2\pi i a n}}{2\,n^s}
 =G(s)\sum_{n=1}^\infty\frac{\cos(2\pi a n)}{n^s}.
$$
Dividing by $G(s)\ne0$ on $\Re s>1$ identifies $Z_{\cos}(a,s)$ with the cosine Dirichlet series. Because $P_a^{\mathrm{symm}}$ has first constant $1$ for *every* $a$, $\Lambda_{\cos}(a,s)$ always has residue $-1$ at $s=0$, so dividing by $G(s)=2/s+O(1)$ gives punctured limit $(-1)/2=-1/2$ at $s=0$ for every $a$ (§1.2.2.2, `differentiableAt_update_of_residue`). At $s=1$, the term $-\delta_a/(1-s)$ vanishes identically when $a\ne0$, so $\Lambda_{\cos}(a,s)$ is holomorphic at $s=1$, making $Z_{\cos}(a,\cdot)$ entire whenever $a\ne0$.

(4) At $a=0$, $P_0^{\mathrm{symm}}=P_0$ from (1) gives $\Lambda_{\cos,0}(0,s)=\Lambda_0(s)$ and $\Lambda_{\cos}(0,s)=\Lambda(s)$, and both $E_0$ and $Z_{\cos}(0,\cdot)$ update $\Lambda/G$ by $-1/2$ at $0$, so $Z_{\cos}(0,\cdot)=\zeta$. Substituting these into (2) gives $\Lambda_0(1-s)=\Lambda_0(s)$ and $\Lambda(1-s)=\Lambda(s)$. $\square$

In Lean, `hurwitzEvenFEPair` (`HurwitzZetaEven.lean:254–277`) constructs $P_a$, `hurwitzEvenFEPair_zero_symm` (`:279–283`) proves `(hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0` from `evenKernel_eq_cosKernel_of_zero` (`:102–105`), and `completedHurwitzZetaEven_eq` / `completedCosZeta_eq` (`:305–339`) perform the factor-$2$ cancellation in the pole terms. The completed functional equations `completedHurwitzZetaEven_one_sub` (`:365–372`) and `completedHurwitzZetaEven₀_one_sub` (`:375–382`) rewrite $(1-s)/2=1/2-s/2$ via `sub_div` and invoke `(hurwitzEvenFEPair a).functional_equation (s / 2)` and `functional_equation₀ (s / 2)`; the symmetric forms `completedCosZeta_one_sub` and `completedCosZeta₀_one_sub` (`:385–392`) substitute $1-s$ using `sub_sub_cancel`. The cosine Dirichlet-series lemmas are `hasSum_int_completedCosZeta` and `hasSum_nat_completedCosZeta` (`:488–526`, calling `hasSum_mellin_pi_mul_sq` from `MellinEqDirichlet.lean:81`, R3 in §1.2.2.1, and pairing $\pm n$ with `HasSum.nat_add_neg`), followed by `cosZeta`, `differentiable_cosZeta_of_ne_zero`, and `hasSum_nat_cosZeta` (`:697–748`). In `RiemannZeta.lean`, lines 64–88 and 100–109 deduce `completedCosZeta_zero`, `completedRiemannZeta₀_one_sub`, and `completedRiemannZeta_one_sub` in three rewrites each, and lines 125–128 deduce `cosZeta_zero`. [Lean, read] [HurwitzZetaEven.lean:254–392](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L254-L392) · [HurwitzZetaEven.lean:488–526](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L488-L526) · [HurwitzZetaEven.lean:697–753](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L697-L753) · [RiemannZeta.lean:64–128](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L64-L128)

**Corollary 5 (de-completed functional equations and sharpness of the excluded sets).** Keep the Poisson assumption of Theorem 4 and the duplication and reflection formulas of §1.2.2.5 and [Chapter 2, §2.3.2.1](02-functional-equations-and-primitive-characters.md#2321-why-gamma-has-no-zeros-in-the-right-half-plane).

1. (`hurwitzZetaEven_one_sub`) For every $a\in\mathbb R/\mathbb Z$ and $s\in\mathbb C$, if $s\ne-n$ for all $n\in\mathbb N$ and $(a\ne0\text{ or }s\ne1)$, then
$$
 E_a(1-s)=2(2\pi)^{-s}\Gamma(s)\cos\Bigl(\frac{\pi s}{2}\Bigr)Z_{\cos}(a,s).
$$
2. (`cosZeta_one_sub`) For every $a\in\mathbb R/\mathbb Z$ and $s\in\mathbb C$, if $s\ne 1-n$ for all $n\in\mathbb N$, then
$$
 Z_{\cos}(a,1-s)=2(2\pi)^{-s}\Gamma(s)\cos\Bigl(\frac{\pi s}{2}\Bigr)E_a(s).
$$
3. (`riemannZeta_one_sub`) Specializing (1) to $a=0$: for every $s\in\mathbb C$, if $s\ne-n$ for all $n\in\mathbb N$ and $s\ne1$, then
$$
 \zeta(1-s)=2(2\pi)^{-s}\Gamma(s)\cos\Bigl(\frac{\pi s}{2}\Bigr)\zeta(s).
$$

**Proof.** We track where each exclusion is spent in Mathlib's total arithmetic.

For (1), first express $E_a(1-s)$ as $\Lambda_{\mathrm{even}}(a,1-s)\cdot G(1-s)^{-1}$. By definition, $E_a(w)$ equals $\Lambda_{\mathrm{even}}(a,w)/G(w)$ away from $w=0$; at $w=0$, $G(0)=\pi^0\Gamma(0)=0$, so $\Lambda_{\mathrm{even}}(a,0)/G(0)=0$, which still agrees with the updated value $E_a(0)=-\delta_a/2$ *if and only if* $a\ne0$ ($\delta_a=0$). Thus $E_a(1-s)=\Lambda_{\mathrm{even}}(a,1-s)G(1-s)^{-1}$ holds whenever $a\ne0$ or $1-s\ne0$, which is precisely the hypothesis $(a\ne0\text{ or }s\ne1)$ (`hurwitzZetaEven_def_of_ne_or_ne`). Next, Theorem 4(2) rewrites $\Lambda_{\mathrm{even}}(a,1-s)$ as $\Lambda_{\cos}(a,s)$. From §1.2.2.5 (`Deligne.inv_Gammaℝ_one_sub`, lines 170–181), the Gamma-ratio identity
$$
 G(1-s)^{-1}=\Gamma_{\mathbb C}(s)\cos\Bigl(\frac{\pi s}{2}\Bigr)G(s)^{-1}
$$
holds under the hypothesis $\forall n\in\mathbb N,\;s\ne-n$: in Lean's proof of `inv_Gammaℝ_one_sub`, $s\ne-n$ ensures $\Gamma(s)\ne0$ so $\Gamma_{\mathbb C}(s)\ne0$ can be cancelled in $G(s)G(s+1)=\Gamma_{\mathbb C}(s)$ and $G(1-s)G(1+s)=1/\cos(\pi s/2)$ (at negative even integers $s=-2m$ with $m\ge1$, $G(s)=0$ while $G(1-s)\ne0$, so $Z_{\cos}(a,-2m)=0$ and $\Gamma(-2m)=0$ make the right side $0$ while $E_a(1+2m)\ne0$; at negative odd integers $s=-(2m+1)$, $G(1-s)=G(2m+2)\ne0$ and $G(s)\ne0$, while $\Gamma(-(2m+1))=0$ in Lean's totalized $\Gamma$ instead of cancelling the zero of $\cos(\pi s/2)$!). Finally, at $n=0$ the same hypothesis gives $s\ne0$, which drops the `Function.update` at $0$ in $Z_{\cos}(a,s)=\Lambda_{\cos}(a,s)G(s)^{-1}$. Rearranging the commutative product gives (1).

For (2), $Z_{\cos}(a,w)$ updates at $w=0$ with $-1/2\ne0$ for *every* $a$, so writing $Z_{\cos}(a,1-s)=\Lambda_{\cos}(a,1-s)G(1-s)^{-1}$ requires $1-s\ne0$, i.e. $s\ne1$ (the case $n=0$ of $s\ne1-n$). Theorem 4(2) at $1-s$ gives $\Lambda_{\cos}(a,1-s)=\Lambda_{\mathrm{even}}(a,s)$; the cases $n=m+1$ of $s\ne1-n$ give $\forall m\in\mathbb N,\;s\ne-m$ for `inv_Gammaℝ_one_sub`; and $n=1$ gives $s\ne0$, which drops the update at $0$ in $E_a(s)=\Lambda_{\mathrm{even}}(a,s)G(s)^{-1}$.

For (3), set $a=0$ in (1): the disjunction $(0\ne0\text{ or }s\ne1)$ simplifies to $s\ne1$, and Theorem 4(4) rewrites $E_0=\zeta$ and $Z_{\cos}(0,\cdot)=\zeta$. $\square$

[Lean, read] [HurwitzZetaEven.lean:587–593](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L587-L593) · [HurwitzZetaEven.lean:760–783](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L760-L783) · [RiemannZeta.lean:178–180](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L178-L180) · [Deligne.lean:170–181](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L170-L181)

**Hand calculation A (zero shift $a=0$: self-dual kernel, pole swap, $\zeta(-1)=-1/12$, and total-function failure at $s=1$).** Set $a=0\in\mathbb R/\mathbb Z$, so $\delta_0=1$ and $\psi(x)=\sum_{n=1}^\infty e^{-\pi n^2 x}$.

1. *Kernels and modified kernels.* Both kernels coincide with Jacobi's theta series $f_0(x)=g_0(x)=1+2\psi(x)$, satisfying $1+2\psi(1/x)=x^{1/2}(1+2\psi(x))$. The weak pair $P_0=(f_0,f_0,1/2,1,1,1)$ is self-dual ($P_0^{\mathrm{symm}}=P_0$). Using $1+2\psi(x)-x^{-1/2}=2x^{-1/2}\psi(1/x)$ on $(0,1)$, the modified kernel is
$$
 f_{0,\mathrm{modif}}(x)=g_{0,\mathrm{modif}}(x)=\begin{cases}
 2\psi(x), & x>1,\\
 0, & x=1,\\
 2x^{-1/2}\psi(1/x), & 0<x<1.
 \end{cases}
$$
Note that at $x=1$ the unmodified tails $f_0(1)-1=2\psi(1)>0$ are nonzero, while the definition sets $f_{0,\mathrm{modif}}(1)=0$.

2. *Two-tail integral and pole swap.* Lemma 2(2) at $w=s/2$, divided by $2$, gives Riemann's manifestly symmetric formula
$$
 \Lambda_0(s)=\int_1^\infty\psi(x)\bigl(x^{s/2-1}+x^{(1-s)/2-1}\bigr)\,dx,\qquad
 \Lambda(s)=\Lambda_0(s)-\frac{1}{s}-\frac{1}{1-s}=\Lambda_0(s)+\frac{1}{s(s-1)}\quad(s\ne0,1).
$$
Under $s\mapsto 1-s$, the two exponents $s/2-1$ and $(1-s)/2-1$ exchange places in the integrand, while the simple pole $-\frac{1}{s}$ at $s=0$ (residue $-1$, coming from $f_0=1$ at $\infty$) and the simple pole $-\frac{1}{1-s}$ at $s=1$ (residue $+1$, coming from $g_0=1$ at $0^+$) swap places: $-\frac{1}{1-s}-\frac{1}{1-(1-s)}=-\frac{1}{1-s}-\frac{1}{s}$.

3. *Evaluating $s=2\mapsto 1-s=-1$.* At $s=2$, both hypotheses of `riemannZeta_one_sub` hold ($2\notin-\mathbb N$ and $2\ne1$). Using $\zeta(2)=\pi^2/6$ and $G(2)=\pi^{-1}\Gamma(1)=1/\pi$, we get $\Lambda(2)=G(2)\zeta(2)=\pi/6$. Since $-\frac{1}{2}-\frac{1}{1-2}=-\frac12+1=\frac12$, the entire integral at $s=2$ (and at $s=-1$) equals
$$
 \Lambda_0(2)=\Lambda_0(-1)=\frac{\pi}{6}-\frac{1}{2}=\frac{\pi-3}{6}\approx 0.0235988>0,
$$
strictly positive as required by $\psi(x)>0$ on $(1,\infty)$. Corollary 5(3) at $s=2$ gives
$$
 \zeta(-1)=2(2\pi)^{-2}\Gamma(2)\cos(\pi)\,\zeta(2)=\frac{2}{4\pi^2}\cdot 1\cdot(-1)\cdot\frac{\pi^2}{6}=-\frac{1}{12};
$$
equivalently, since $\Gamma(1/2)=\sqrt\pi$ and $\frac12\Gamma(-1/2)=\Gamma(1/2)$ give $\Gamma(-1/2)=-2\sqrt\pi$, we have $G(-1)=\pi^{1/2}\Gamma(-1/2)=-2\pi$ and $\zeta(-1)=\Lambda(-1)/G(-1)=(\pi/6)/(-2\pi)=-1/12$.

4. *Why `riemannZeta_one_sub` fails as a total equality at $s=1$ and at $s\in-\mathbb N$.* At $s=1$, the completed identity $\Lambda(0)=\Lambda(1)$ holds unconditionally in Lean: both equal the stored value $\Lambda_0(1)-1=\frac{\gamma-\log(4\pi)}{2}$ (§§1.2.2.2–1.2.2.3), because the undefined pole term $1/0$ vanishes on opposite slots. Yet in the un-completed equation at $s=1$, the left side is $\zeta(0)=-1/2$ (`riemannZeta_zero`), whereas the right side evaluates to
$$
 2(2\pi)^{-1}\Gamma(1)\cos\Bigl(\frac{\pi}{2}\Bigr)\zeta(1)=\frac{1}{\pi}\cdot 1\cdot 0\cdot\frac{\gamma-\log(4\pi)}{2}=0\ne-\frac{1}{2}:
$$
in classical analysis $\cos(\pi s/2)\zeta(s)\to(-\pi/2)\cdot 1=-\pi/2$ as $s\to1$ cancels the simple pole, whereas total evaluation multiplies $\cos(\pi/2)=0$ by the *finite* stored number $\zeta(1)$ and gets $0$. Likewise, at $s=0$ the left side is $\zeta(1)=\frac{\gamma-\log(4\pi)}{2}\ne0$, while on the right Lean's total $\Gamma(0)=0$ forces $0$; at $s=-2m$ ($m\ge1$) the left side is $\zeta(2m+1)>1$ while $\Gamma(-2m)=0$ and $\zeta(-2m)=0$ force $0$; and at $s=-(2m+1)$ ($m\ge0$), when $\zeta(2m+2)=\frac{(2\pi)^{2m+2}\lvert B_{2m+2}\rvert}{2(2m+2)!}>1$, both $\Gamma(-(2m+1))=0$ and $\cos\bigl(-\frac{(2m+1)\pi}{2}\bigr)=0$ force the right side to $0$. Every point excluded by `hs` and `hs'` is an actual falsification point of the total equality.

**Hand calculation B (nonzero shift $a=1/3$: seam defect, single-pole migration, legal evaluation at $s=1$, and $E_{1/3}(-1)=1/36$).** Set $a=1/3\in\mathbb R/\mathbb Z$, so $a\ne0$ and $\delta_{1/3}=0$.

1. *Asymmetric kernels and the seam at $x=1$.* The pair $P_{1/3}=(f_{1/3},g_{1/3},1/2,1,0,1)$ has kernels
$$
 f_{1/3}(x)=\sum_{n\in\mathbb Z}e^{-\pi(n+1/3)^2 x}=\sum_{\substack{m\ge1\\3\nmid m}}e^{-\pi m^2 x/9},\qquad
 g_{1/3}(x)=1+2\sum_{n=1}^\infty\cos\Bigl(\frac{2\pi n}{3}\Bigr)e^{-\pi n^2 x},
$$
with $(f_0,g_0)=(0,1)$ whereas $P_{1/3}^{\mathrm{symm}}$ has $(f_0,g_0)=(1,0)$. As seen in the Example, $f_{1/3}(1)=g_{1/3}(1)$ while $(f_{1/3}(1)-0)-(g_{1/3}(1)-1)=1$, so setting both modified kernels to $0$ at $x=1$ is essential. Away from $x=1$,
$$
 f_{1/3,\mathrm{modif}}(x)=\begin{cases}
 f_{1/3}(x), & x>1,\\
 f_{1/3}(x)-x^{-1/2}, & 0<x<1,
 \end{cases}\qquad
 g_{1/3,\mathrm{modif}}(x)=\begin{cases}
 g_{1/3}(x)-1, & x>1,\\
 g_{1/3}(x), & 0<x<1:
 \end{cases}
$$
because $f_0=0$, $g_{1/3}$ requires **no** subtraction on $(0,1)$ — indeed $g_{1/3}(x)=x^{-1/2}f_{1/3}(1/x)=O(x^{-1/2}e^{-\pi/(9x)})$ already vanishes faster than every power as $x\to0^+$.

2. *Single-pole migration.* Theorem 4(2) with $\delta_{1/3}=0$ reads
$$
 \Lambda_{\mathrm{even}}(1/3,s)=\Lambda_{\mathrm{even},0}(1/3,s)-\frac{1}{1-s},\qquad
 \Lambda_{\cos}(1/3,s)=\Lambda_{\cos,0}(1/3,s)-\frac{1}{s}.
$$
Here $\Lambda_{\mathrm{even}}(1/3,s)$ is holomorphic at $s=0$ and has a single simple pole at $s=1$ (residue $+1$), while $\Lambda_{\cos}(1/3,s)$ is holomorphic at $s=1$ and has a single simple pole at $s=0$ (residue $-1$). Under $s\mapsto 1-s$, the lone pole $-\frac{1}{1-(1-s)}=-\frac{1}{s}$ of $\Lambda_{\mathrm{even}}(1/3,1-s)$ migrates to $s=0$ and matches the lone pole of $\Lambda_{\cos}(1/3,s)$.

3. *Closed-form Dirichlet series on $\Re s>1$ and holomorphy at $s=1$.* Grouping $m=\lvert 3n+1\rvert$ over $n\in\mathbb Z$ enumerates all positive integers $m\equiv\pm1\pmod3$ once each, so for $\Re s>1$,
$$
 E_{1/3}(s)=\frac{3^s}{2}\sum_{\substack{m\ge1\\3\nmid m}}m^{-s}=\frac{3^s}{2}(1-3^{-s})\zeta(s)=\frac{3^s-1}{2}\zeta(s).
$$
For $Z_{\cos}(1/3,s)$, $\cos(2\pi n/3)$ equals $+1$ when $3\mid n$ and $-1/2$ when $3\nmid n$, giving for $\Re s>1$
$$
 Z_{\cos}(1/3,s)=3^{-s}\zeta(s)-\frac{1}{2}(1-3^{-s})\zeta(s)=\frac{3^{1-s}-1}{2}\zeta(s).
$$
Both identities extend analytically to $\mathbb C\setminus\{1\}$. Moreover, as $s\to1$, $\frac{3^{1-s}-1}{2}=-\frac{\log 3}{2}(s-1)+O\bigl((s-1)^2\bigr)$ cancels the simple pole $\frac{1}{s-1}+O(1)$ of $\zeta(s)$, confirming Theorem 4(3) that $Z_{\cos}(1/3,\cdot)$ is entire with value $Z_{\cos}(1/3,1)=-\frac{\log 3}{2}$ (which also equals the conditionally convergent Fourier series $\sum_{n=1}^\infty\cos(2\pi n/3)/n=-\Re\log(1-e^{2\pi i/3})=-\frac12\log 3$).

4. *Legal evaluation at $s=1$ versus reverse-direction failure.* Because $a=1/3\ne0$, the hypothesis $(a\ne0\text{ or }s\ne1)$ of `hurwitzZetaEven_one_sub` holds **at $s=1$** (and $1\notin-\mathbb N$). Corollary 5(1) at $(1/3,1)$ is therefore a valid Lean theorem:
$$
 E_{1/3}(0)=2(2\pi)^{-1}\Gamma(1)\cos\Bigl(\frac{\pi}{2}\Bigr)Z_{\cos}(1/3,1)=\frac{1}{\pi}\cdot 1\cdot 0\cdot\Bigl(-\frac{\log 3}{2}\Bigr)=0,
$$
which agrees with $E_{1/3}(0)=-\delta_{1/3}/2=0$ and with $\lim_{s\to0}\frac{3^s-1}{2}\zeta(s)=0\cdot(-1/2)=0$: because $Z_{\cos}(1/3,\cdot)$ has no pole at $s=1$, the zero of $\cos(\pi s/2)$ honestly produces $E_{1/3}(0)=0$. By contrast, the reverse equation `cosZeta_one_sub` excludes $s=1$ ($n=0$ in $s\ne1-n$) even for $a=1/3\ne0$: at $s=1$, its left side is $Z_{\cos}(1/3,0)=-1/2$ (`cosZeta_apply_zero`, matching $\frac{3^1-1}{2}\zeta(0)=1\cdot(-1/2)=-1/2$), whereas on the right $\cos(\pi/2)=0$ multiplies the finite stored value $E_{1/3}(1)=\frac{\gamma-\log(4\pi)}{2}+\frac{3\log 3}{2}$ to give $0\ne-1/2$!

5. *Evaluating $s=2\mapsto 1-s=-1$.* At $s=2$, $Z_{\cos}(1/3,2)=\frac{3^{-1}-1}{2}\zeta(2)=-\frac{1}{3}\cdot\frac{\pi^2}{6}=-\frac{\pi^2}{18}$ (and $\Lambda_{\cos}(1/3,2)=\Lambda_{\mathrm{even}}(1/3,-1)=G(2)Z_{\cos}(1/3,2)=-\frac{\pi}{18}$). Corollary 5(1) at $(1/3,2)$ yields
$$
 E_{1/3}(-1)=2(2\pi)^{-2}\Gamma(2)\cos(\pi)\,Z_{\cos}(1/3,2)=\frac{1}{2\pi^2}\cdot 1\cdot(-1)\cdot\Bigl(-\frac{\pi^2}{18}\Bigr)=\frac{1}{36}.
$$
Two independent checks agree: $\frac{3^{-1}-1}{2}\zeta(-1)=(-\frac13)(-\frac{1}{12})=\frac{1}{36}$, and in terms of the second Bernoulli polynomial $B_2(x)=x^2-x+\frac16$, $B_2(1/3)=\frac19-\frac13+\frac16=-\frac{1}{18}$ gives $-\frac{B_2(1/3)}{2}=\frac{1}{36}$ (`hurwitzZetaEven_one_sub_two_mul_nat` at $k=1$). [DLMF 25.11.14](https://dlmf.nist.gov/25.11#E14)

**Reconnecting to `riemannZeta_one_sub` and downstream consumers.** At the archive's reduction `Formalism.VW.rh_of_right` (`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:28`, read in §1.4.2), a hypothetical zero $\zeta(s)=0$ in $\Re s<1/2$ with $s\ne1$ and $s\notin\{-2,-4,\dots\}$ is reflected to $w=1-s$, where $\Re w>1/2$. Line 28 invokes `riemannZeta_one_sub hnat h1` at argument $w=1-s$, discharging the two hypotheses of Corollary 5(3) as follows:

- `hnat : ∀ n : ℕ, 1 - s ≠ -n`: if $1-s=-n$, then $\Re(1-s)=-n\le0$, contradicting $\Re(1-s)>1/2$ (`linarith` on `ht : s.re < 1 / 2` and `(n : ℝ) ≥ 0`, lines 23–26);
- `h1 : 1 - s ≠ 1`: if $1-s=1$, then $s=0$, contradicting $\zeta(s)=0$ against `riemannZeta_zero` ($\zeta(0)=-1/2\ne0$, lines 17–22).

After rewriting `1 - (1 - s) = s`, `rh_of_right` obtains $0=\zeta(s)=2(2\pi)^{-(1-s)}\Gamma(1-s)\cos(\pi(1-s)/2)\zeta(1-s)$ and rules out each factor as explained in §1.4.2. No new RH research is involved: every step from $f_a(1/x)=x^{1/2}g_a(x)$ and `Gamma_mul_Gamma_add_half` to `RhOfRight.lean:28` is now accounted for in §§1.2.2.1–1.2.2.6 and Chapter 2, §2.3.2.1. A scan of the pinned Mathlib tree and all 175,187 `.lean` files of archive A2 records the consumers of this subsection's declarations below (archive consumers are listed without new analysis of their surrounding modules).

| Declaration produced here | Direct consumers in pinned Mathlib / archive A2 | Role in the book |
|---|---|---|
| `WeakFEPair.functional_equation₀`, `WeakFEPair.functional_equation` ([AbstractFuncEq.lean:421–429](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L421-L429)) | `completedHurwitzZetaEven_one_sub` and `_₀_one_sub` ([HurwitzZetaEven.lean:370, 380](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L370)); `completedHurwitzZetaOdd_one_sub` ([HurwitzZetaOdd.lean:365](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean#L365), $f_0=g_0=0$); archive `WeakFEPair` instances and `f_modif`/`Λ₀` bounds in `TateMain.lean:115, 131`, `ContinuousOnThetaCFunLtr.lean:175–220`, `FunctionalEquationPairEntirePartBound.lean:8–55`, `ContinuousSetIntegralIoiOne.lean:121–202`, `ImportsSide.lean:8–17` | Theorem 4 (even case, non-zero pole corrections) and §1.3.2.1 (odd case, zero pole corrections) |
| `completedHurwitzZetaEven_one_sub` ([HurwitzZetaEven.lean:365–372](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L365-L372)) | `completedCosZeta_one_sub` (`:385`); `hurwitzZetaEven_one_sub` (`:766`); `completedRiemannZeta_one_sub` ([RiemannZeta.lean:108](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L108)); `ZMod.completedLFunction_one_sub_of_one_lt_even` → `completedLFunction_one_sub_even` ([ZMod.lean:415, 459–505](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L415)) → `IsPrimitive.completedLFunction_one_sub` ([DirichletContinuation.lean:284–314](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L284-L314)) | Theorem 4(4), Corollary 5, §1.3.4, and Chapter 2, §2.4.2 (even primitive Dirichlet branch) |
| `completedRiemannZeta_one_sub` ([RiemannZeta.lean:106–109](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L106-L109)) | `IsPrimitive.completedLFunction_one_sub` ($N=1$ branch, `DirichletContinuation.lean:289`); archive `Claim.zeta` (`ClaimStrip.lean:99`) and `RiemannHypothesisOfEveryCharacter.lean:222` | §1.4.2 ("RH a second time") and Chapter 2, §2.4.3 |
| `hurwitzZetaEven_one_sub` ([HurwitzZetaEven.lean:760–770](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L760-L770)) | `riemannZeta_one_sub` (`RiemannZeta.lean:180`); full Hurwitz formula `hurwitzZeta_one_sub` ([HurwitzZeta.lean:156–170](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L156-L170)); Bernoulli special values `hurwitzZetaEven_one_sub_two_mul_nat` ([HurwitzZetaValues.lean:124–143](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean#L124-L143), consumer in archive `BLval.lean:8, 35`) | Corollary 5(3) and Hand calculation B(5) |
| `riemannZeta_one_sub` ([RiemannZeta.lean:178–180](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L178-L180)) | Archive `Formalism.VW.rh_of_right` (`RhOfRight.lean:28`), `RHofHalfPlane.lean:26, 56`, `ZetaZeroFreeRegion.lean:176` | §1.2.3, §1.4.2, and Chapter 2, §2.4.3 |

**Remarks.**

1. *Riemann (1859) and Jacobi (1829).* In his November 1859 *Monatsberichte* memoir `[Riemann1859]` (pp. 673–674; p. 3 of Wilkins's edition), Riemann sets $\psi(x)=\sum_{n=1}^\infty e^{-n^2\pi x}$, quotes $2\psi(x)+1=x^{-1/2}(2\psi(1/x)+1)$ from Jacobi's *Fundamenta Nova* `[Jacobi1829]` (p. 184), splits the Mellin integral of $\psi$ at $x=1$, substitutes $x\mapsto 1/x$ on $(0,1)$, and writes
$$
 \Pi\Bigl(\frac s2-1\Bigr)\pi^{-s/2}\zeta(s)=\frac{1}{s(s-1)}+\int_1^\infty\psi(x)\bigl(x^{s/2-1}+x^{-(1+s)/2}\bigr)\,dx,
$$
noting immediately that the right-hand side "remains unchanged when $s$ is replaced by $1-s$". Because Riemann starts from $\psi(x)=(f_0(x)-1)/2$, the upper subtraction $f_0=1$ is built in before splitting; on $(0,1)$, rewriting $\psi(x)=\frac12 x^{-1/2}+\frac12 x^{-1/2}\cdot 2\psi(1/x)-\frac12$ produces both pole terms $\frac{1}{s-1}-\frac{1}{s}=\frac{1}{s(s-1)}$ from the lower interval $(0,1)$. Mathlib's `WeakFEPair` obtains the identical right-hand side without splitting an already-convergent integral on $\Re s>1$ first: it builds the entire function $\Lambda_0$ directly as the $(0,\infty)$-Mellin transform of $f_{\mathrm{modif}}$, proves $\Lambda_0(k-s)=\varepsilon\Lambda_0^{\mathrm{symm}}(s)$ on all of $\mathbb C$ by global $t\mapsto 1/t$ inversion, and only connects $\Lambda$ back to $\mathcal M(f-f_0)$ on $\Re s>k$ afterwards (`hasMellin`).

2. *Hurwitz's formula (1882) via parity decomposition.* Classically, Hurwitz `[Hurwitz1882]` proved the functional equation of $\zeta(s,a)=\sum_{n=0}^\infty(n+a)^{-s}$ ($0<a\le1$) by contour integration around a Hankel loop, obtaining `[DLMF 25.11.9]`
$$
 \zeta(1-s,a)=\frac{2\,\Gamma(s)}{(2\pi)^s}\sum_{n=1}^\infty\frac{\cos\bigl(\frac{\pi s}{2}-2\pi n a\bigr)}{n^s}\qquad(\Re s>1,\;0<a\le1).
$$
David Loeffler's Mathlib formalization avoids Hankel contours altogether by splitting $\zeta(s,a)=E_a(s)+O_a(s)$ into its even and odd parts in $a\in\mathbb R/\mathbb Z$: Theorem 4 and Corollary 5(1) give $E_a(1-s)=\Gamma_{\mathbb C}(s)\cos(\pi s/2)Z_{\cos}(a,s)$ at weight $k=1/2$ with $(f_0,g_0)=(\delta_a,1)$, §1.3.2.1 gives $O_a(1-s)=\Gamma_{\mathbb C}(s)\sin(\pi s/2)Z_{\sin}(a,s)$ at weight $k=3/2$ with $(f_0,g_0)=(0,0)$, and `hurwitzZeta_one_sub` (`HurwitzZeta.lean:156–170`) adds the two and expands $\cos(\pi s/2)\cos(2\pi n a)+\sin(\pi s/2)\sin(2\pi n a)=\cos(\pi s/2-2\pi n a)$ into the exponential zeta functions $L(e^{\pm 2\pi i a\cdot},s)$. Notice also that Mathlib's $H_a=\text{`hurwitzZeta`}$ on $\mathbb R/\mathbb Z$ satisfies $H_0(s)=\zeta(s)$ (`hurwitzZeta_zero`, $a=0$ corresponds to classical $a=1$, where $\zeta(s,1)=\zeta(s)$, `[DLMF 25.11.3]`), whereas for $0<a<1$ it agrees with classical $\zeta(s,a)$ (`hasSum_nat_hurwitzZeta_of_mem_Ioc`). [DLMF 25.4.1–4](https://dlmf.nist.gov/25.4#E1) · [DLMF 25.5.13–14](https://dlmf.nist.gov/25.5#E13) · [DLMF 25.11.3, 25.11.9](https://dlmf.nist.gov/25.11#E9)

3. *Deligne's archimedean factors.* The notation $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$ and $\Gamma_{\mathbb C}(s)=2(2\pi)^{-s}\Gamma(s)$ in `Deligne.lean` follows Deligne `[Deligne1979]`, §5.3: the completed even Hurwitz function carries the factor $\Gamma_{\mathbb R}(s)$, the completed odd Hurwitz function (§1.3.2.1) carries $\Gamma_{\mathbb R}(s+1)$, and their product $\Gamma_{\mathbb R}(s)\Gamma_{\mathbb R}(s+1)=\Gamma_{\mathbb C}(s)$ (§1.2.2.5) is what turns division by $\Gamma_{\mathbb R}(1-s)$ into multiplication by $\Gamma_{\mathbb C}(s)\cos(\pi s/2)$ or $\Gamma_{\mathbb C}(s)\sin(\pi s/2)$.

4. *Where `ZMod.completedLFunction_one_sub_even` still uses the identity theorem.* Although `completedHurwitzZetaEven_one_sub` holds for *every* $s\in\mathbb C$, the finite discrete-Fourier combination for an even function $\Phi:\mathbb Z/N\mathbb Z\to\mathbb C$ in `ZMod.lean:409–505` first proves `completedLFunction_one_sub_of_one_lt_even` on $\Re s>1$ (applying `completedHurwitzZetaEven_one_sub` termwise at line 415 and identifying $\sum_x\Phi(x)Z_{\cos}(x/N,s)$ with $L(\widehat\Phi,s)$ via the Dirichlet series) and then extends to the connected open domain $U=\{s:(s\ne0\lor\sum\Phi=0)\land(s\ne1\lor\Phi(0)=0)\}$ by `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` around $s=2$. When $\chi$ is a primitive character of conductor $N>1$, both $\sum\chi=0$ and $\chi(0)=0$ hold, so $U=\mathbb C$ (`DirichletContinuation.lean:302`), while $N=1$ calls `completedRiemannZeta_one_sub` directly (`:289`).

**Source note.** The reading is R3 for `AbstractFuncEq.lean:80–138` (`WeakFEPair`, `IsStrongFEPair`, `h_feq'`, `symm`), `184–203` (`functional_equation_aux`), `247–316` (`f_modif`, `g_modif`, `hf_modif_int`, `hf_modif_FE`, `hf_modif_top`, `toStrongFEPair`, `isStrongFEPair_toStrongFEPair`), `376–388` (`Λ₀`, `Λ`, `Λ₀_eq`, `symm_Λ₀_eq`) and `420–429` (`functional_equation₀`, `functional_equation`); for `MellinTransform.lean:91–132` (`mellin`, `mellin_cpow_smul`, `mellin_const_smul`, `mellin_div_const`, `mellin_comp_rpow`) and `IntegralEqImproper.lean:1131–1143` (`integral_comp_rpow_Ioi`); for `HurwitzZetaEven.lean:102–105` (`evenKernel_eq_cosKernel_of_zero`), `254–392` (`hurwitzEvenFEPair`, `hurwitzEvenFEPair_zero_symm`, `hurwitzEvenFEPair_neg`, `completedHurwitzZetaEven`, `completedHurwitzZetaEven_eq`, `completedCosZeta`, `completedCosZeta_eq`, `completedHurwitzZetaEven_one_sub`, `completedHurwitzZetaEven₀_one_sub`, `completedCosZeta_one_sub`, `completedCosZeta₀_one_sub`), `488–526` (`hasSum_int_completedCosZeta`, `hasSum_nat_completedCosZeta`), `587–593` (`hurwitzZetaEven_def_of_ne_or_ne`), `697–753` (`cosZeta`, `cosZeta_apply_zero`, `cosZeta_neg_two_mul_nat_add_one`, `differentiableAt_cosZeta`, `differentiable_cosZeta_of_ne_zero`, `hasSum_int_cosZeta`, `hasSum_nat_cosZeta`, `LSeriesHasSum_cos`), and `760–783` (`hurwitzZetaEven_one_sub`, `cosZeta_one_sub`); for `RiemannZeta.lean:64–109, 121–128, 178–180`; and for the consumer bodies `HurwitzZeta.lean:156–191`, `HurwitzZetaValues.lean:124–143`, `ZMod.lean:409–425, 459–505`, `DirichletContinuation.lean:284–314`, and archive `RhOfRight.lean:1–62` and `ClaimStrip.lean:75–104`. Inherited from earlier sections are the theta-kernel bounds, Mellin convergence/differentiation criteria, `f_modif_aux1`/`f_modif_aux2`/`hasMellin`, and `hasSum_mellin_pi_mul_sq` (§1.2.2.1), `differentiableAt_update_of_residue` and `differentiable_Gammaℝ_inv` (§1.2.2.2), the stored value at $1$ (§1.2.2.3), `inv_Gammaℝ_one_sub` and the duplication formula (§1.2.2.5), the odd Hurwitz reflection (§1.3.2.1), and Euler's integral, recurrence, reflection, and improper-integral criteria for $\Gamma$ ([Chapter 2, §§2.3.2.1 and 2.3.2.3–2.3.2.4](02-functional-equations-and-primitive-characters.md#2321-why-gamma-has-no-zeros-in-the-right-half-plane)). Inputs retained by name (statements read, proof bodies not read here) are the Gaussian Poisson summation theorem `Complex.tsum_exp_neg_quadratic` (`PoissonSummation.lean:87`, feeding `jacobi_theta_two_functional_equation` at `TwoVariable.lean:465`), the general measure-theoretic change-of-variables theorem `integral_image_eq_integral_abs_deriv_smul` (`IntegralEqImproper.lean:1137`), `isLittleO_exp_neg_mul_rpow_atTop`, `HasSum.nat_add_neg`, `summable_one_div_int_add_rpow`, `cosZeta_two_mul_nat'` (`HurwitzZetaValues.lean:79`), `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, and `Countable.isConnected_compl_of_one_lt_rank`; archive consumers outside `RhOfRight.lean` and `ClaimStrip.lean` are listed from a static grep without reading their dependency cones. Riemann's 1859 memoir was read in D. R. Wilkins's German transcription and English translation (pp. 673–674 of *Monatsberichte*, p. 3 of Wilkins), alongside NIST DLMF §§25.4, 25.5, and 25.11; Hurwitz (1882) and Deligne (1979) were verified bibliographically without reading their original pages. The [proof map](../notes/proof-map.md#p1-chapter-1-completed-hurwitz-functional-equation) records all pinned paths and lines. The two traps in the Example, hand calculations A and B, and the consumer table are ours; the exact rational Bernoulli checks and Gauss–Legendre quadrature checks (`verify_fe_pair.py`) are consistency checks, not formal proof certificates, and no Lean compilation was run.

### 1.2.3 The excluded points are exactly the trivial zeros

The trivial zeros of $\zeta$ are $-2,-4,-6,\dots$, and Mathlib proves that they are zeros:
$\zeta(-2(n+1))=0$ for every $n\in\mathbb N$ [Lean] (`riemannZeta_neg_two_mul_nat_add_one`,
`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:173`). The hypothesis
`¬∃ n : ℕ, s = -2 * (n + 1)` excludes precisely these points: with $n\ge0$ the expression
$-2(n+1)$ runs through $-2,-4,\dots$ and never through $0$. The point $s=0$ needs no exclusion,
because $\zeta(0)=-1/2$ [Lean] (`riemannZeta_zero`,
`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:151`).

Classically, RH is often stated as "every zero with $0<\Re s<1$ has $\Re s=1/2$". Mathlib's
version is at least as strong: it asserts in addition that there are no zeros with $\Re s\le0$
other than the trivial ones. That extra content is a known theorem — it follows from the
functional equation in the form
$\zeta(1-s)=2(2\pi)^{-s}\Gamma(s)\cos(\pi s/2)\zeta(s)$ for $s\notin\{0,-1,-2,\dots\}$, $s\ne1$
[Lean, read] (`riemannZeta_one_sub`, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178`; its Gamma
factor comes from the duplication and reflection formulas and its completed reflection from the theta-kernel pair, see §§1.2.2.5–1.2.2.6), together
with $\zeta\ne0$ on $\Re s\ge1$ — so the two formulations are equivalent [Expository]. The
archive in fact proves the stronger form, and Section 1.4 shows the case analysis it uses.

### 1.2.4 One half

In `s.re = 1 / 2`, the left side `s.re` is a real number (`Complex.re : ℂ → ℝ`), so Lean
elaborates `1 / 2` as a real number, $0.5$. The well-known pitfall that `1 / 2` denotes $0$ in
natural-number arithmetic does not arise. The same holds in every `1 / 2` of `src/Statements.lean`,
each of which is compared with `s.re` [Lean, read] (`src/Statements.lean:4`, `:8`, `:12`,
`:16`). The same observation appears in the Comparator notes of
`leanprover-community/riemann-hypothesis` [Community].

## 1.3 The Dirichlet statements

### 1.3.1 The four definitions

The archive's `src/Statements.lean` reads, after `import Mathlib` [Lean, read]
(`src/Statements.lean:3`, `:6`, `:10`, `:14`):

```lean
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

The first is RH again, written out; Section 1.4 shows that the kernel treats it as identical to
Mathlib's definition. The second says that no Dirichlet L-function vanishes on the open
half-plane $\Re s>1/2$, except that the trivial character is allowed its pole at $s=1$. The third
and fourth are GRH in the critical strip, for all characters and for primitive ones.

### 1.3.2 From the finite Hurwitz sum to the classical Dirichlet L-function

**Motivation.** A Dirichlet character gives periodic coefficients in a
series that converges absolutely on $\Re s>1$. The zero statements also
evaluate the $L$-function in the critical strip. To identify the function
there, we first group the series by residue classes and then follow what
happens to their poles under continuation.

**Examples.** The nonprincipal character $\chi_3$ modulo $3$ sends the unit
$2$, of order two, to $-1$. The principal character $\chi_{0,4}$ modulo $4$
sends both units to $1$. Their values on a period are

| Character | Residues in order starting at $0$ | Sum |
|---|---|---:|
| $\chi_3$ | $(0,1,-1)$ | $0$ |
| $\chi_{0,4}$ | $(0,1,0,1)$ | $2$ |

The respective finite Hurwitz expressions are
$3^{-s}(\zeta(s,1/3)-\zeta(s,2/3))$ and
$4^{-s}(\zeta(s,1/4)+\zeta(s,3/4))$ in the convergence half-plane.
At $s=2$, keep two terms per Hurwitz series. For $\chi_3$ this gives
$3^{-2}(9+9/16-9/4-9/25)=1-1/4+1/16-1/25=309/400$.
For $\chi_{0,4}$ it gives
$4^{-2}(16+16/25+16/9+16/49)=1+1/9+1/25+1/49=12916/11025$.
In each case the expression on the right adds the first two periods
of the ordinary series.

**Definitions.** For $N\ge1$, a complex Dirichlet character modulo $N$
is a homomorphism from $(\mathbb Z/N\mathbb Z)^\times$ to $\mathbb C^\times$,
extended by zero on nonunits. The principal character is $1$ on units.
For $N=1$ the sole residue class is a unit, so its character is $1$ on every
integer. For any function $\Phi:\mathbb Z/N\mathbb Z\to\mathbb C$, set
$$
F_\Phi(s)=N^{-s}\sum_{j=0}^{N-1}\Phi(j)H_{j/N}(s).
$$
Here $N^{-s}=\exp(-s\log N)$ uses the real logarithm and $j$ runs over the
least nonnegative representatives. The notation $H_a$ denotes Mathlib's
total Hurwitz function at the class of $a$ in $\mathbb R/\mathbb Z$.
For $0<a<1$ and $\Re s>1$ it sums $1/(m+a)^s$ over $m\ge0$. At the
zero class the sum is $\sum_{m\ge1}m^{-s}$. Taking $a=1$ shifts the
index by one. Taking $a=0$ instead makes the first term zero under
Lean's conventions $0^s=0$ for $s\ne0$ and division by zero equal to zero.
For modulus one the finite sum thus recovers the Riemann zeta function [Lean, read]
([`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:67`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L67),
[`Mathlib/NumberTheory/LSeries/ZMod.lean:87`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L87)).
The ordinary series in Lean has a term at $n=0$ defined to be zero,
even when the coefficient there is $1$.

In Lean the zero extension is part of the character type, `MulChar (ZMod N) ℂ`. The character type is defined in [`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:40`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/DirichletCharacter/Basic.lean#L40) [Lean].
The finite sum and its character specialization are definitions [Lean, read]
([`Mathlib/NumberTheory/LSeries/ZMod.lean:83`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L83),
[`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:61`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L61)).
The parameter and zero-term conversions are [Lean, read]
([`Mathlib/Topology/Instances/AddCircle/Real.lean:77`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Instances/AddCircle/Real.lean#L77),
[`Mathlib/NumberTheory/LSeries/Basic.lean:88`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/Basic.lean#L88),
[`Mathlib/NumberTheory/LSeries/Basic.lean:100`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/Basic.lean#L100)).

**Lemma (grouping by residues).** For every $\Phi$ as above and $\Re s>1$,
$$
F_\Phi(s)=\sum_{n=1}^\infty\frac{\Phi(n\bmod N)}{n^s}.
$$

**Proof.** Set $\sigma=\Re s$ and let $M$ be the maximum of $|\Phi(j)|$ over the residues. The sum of
absolute values is bounded by $M\sum_{n\ge1}n^{-\sigma}$, which converges.
Insert the zero term at $n=0$. Euclidean division gives the bijection
$n\mapsto(n\bmod N,\lfloor n/N\rfloor)$ with inverse $(j,m)\mapsto j+Nm$.
Cutting each inner sum at $m<K$ covers exactly $0\le n<NK$. The omitted
terms have total norm at most $M\sum_{n\ge NK} n^{-\sigma}$, tending to
zero as $K$ increases. Hence we may sum by residue class and then add
the $N$ sums. For $j+Nm>0$ we have
$$
(j+Nm)^{-s}=N^{-s}(m+j/N)^{-s},
$$
using additivity of the real logarithm on positive factors. At
$(j,m)=(0,0)$ both formal summands are zero. Pulling $N^{-s}$ out
leaves the Hurwitz series in each residue class.

In Lean, `Nat.residueClassesEquiv` gives the bijection. `Nat.sumByResidueClasses`
transfers summability along the inverse and uses the product-indexed sum
followed by a finite outer sum. `ZMod.LFunction_eq_LSeries` uses the
bound on the finite residue ring and compares the norms with a convergent
$p$-series. It then expands the Hurwitz series, and uses
`mul_cpow_ofReal_nonneg` before reducing the coefficient of $j+Nm$ to
$\Phi(j)$. The character version specializes this proof [Lean, read]
([`Mathlib/Data/ZMod/Basic.lean:1296`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/ZMod/Basic.lean#L1296),
[`Mathlib/Analysis/SumOverResidueClass.lean:106`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SumOverResidueClass.lean#L106),
[`Mathlib/NumberTheory/LSeries/ZMod.lean:70`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L70),
[`Mathlib/NumberTheory/LSeries/Basic.lean:346`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/Basic.lean#L346),
[`Mathlib/NumberTheory/LSeries/ZMod.lean:93`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L93),
[`Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean:186`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean#L186),
[`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:75`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L75)).

**Proposition (identification).** Let $\chi$ be a complex Dirichlet character
modulo $N\ge1$. For nonprincipal $\chi$, $F_\chi$ is the unique entire
continuation of its Dirichlet series, including its value at $1$. For
principal $\chi$, $F_\chi$ on $\mathbb C\setminus\{1\}$ is the unique holomorphic
continuation there and has a simple pole at $1$ of residue $\varphi(N)/N$,
where $\varphi(N)$ counts the units modulo $N$.

**Proof.** The Hurwitz inputs are holomorphy of $H_a$ away from $1$
and holomorphy near $1$ of
$$
R_a(s)=H_a(s)-B(s),\qquad
B(s)=\frac{1}{(s-1)\Gamma_{\mathbb R}(s)},\qquad
\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2).
$$
The total convention gives $B(1)=0$. To see the direct Hurwitz steps,
write $H_a$ as the sum of its even and odd parts. In the convergence
half-plane, pairing $m$ with $-m-1$ in the bilateral series gives terms
$(u_m+v_m)/2$ and $(u_m-v_m)/2$, where $u_m=1/(m+a)^s$ and
$v_m=1/(m+1-a)^s$ with the same endpoint convention. Adding the parts
recovers $u_m$. Away from $1$ the even part is holomorphic, including
its updated value at $0$, and the odd part is entire. At $0$ the
completed even function has residue $-1$ for the zero class and $0$
otherwise. Since $s\Gamma_{\mathbb R}(s)$ tends to $2$ there, the
quotient has a finite limit. The even-part definition inserts that
limit, and the removable-singularity lemma gives holomorphy there. Near $1$, the even
part is the completed even function divided by $\Gamma_{\mathbb R}(s)$.
The completed even function is an entire term minus $\mathbf 1_{a=0}/s$
plus $1/(s-1)$, with $a=0$ denoting the zero class. Subtracting $B$
cancels the last term, including at $1$ under total division. The
remaining quotient is holomorphic near $1$ since $\Gamma_{\mathbb R}(1)=1$.
Adding the entire odd part gives the stated regularity of $R_a$.
These are the direct Hurwitz interface proofs [Lean, read]
([`Mathlib/NumberTheory/LSeries/HurwitzZeta.lean:66`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L66),
[`Mathlib/NumberTheory/LSeries/HurwitzZeta.lean:72`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L72),
[`Mathlib/NumberTheory/LSeries/HurwitzZeta.lean:88`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L88),
[`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:305`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L305),
[`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:554`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L554),
[`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:613`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L613),
[`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:630`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L630),
[`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:683`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L683),
[`Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:466`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean#L466),
[`Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:505`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean#L505)).

Put $S=\sum_j\chi(j)$. A nonprincipal character has a unit $b$ with
$\chi(b)\ne1$. Multiplication by $b$ permutes the residues, so
$S=\sum_j\chi(bj)=\chi(b)S$ and $S=0$. For the principal character,
$S=\varphi(N)>0$. Away from $1$, holomorphy of $F_\chi$ follows from
the finite sum and the entire factor $N^{-s}$. Near $1$, write
$$
F_\chi(s)=N^{-s}\left(\sum_j\chi(j)R_{j/N}(s)+S B(s)\right).
$$
When $S=0$, the last term vanishes identically, so the first term gives
a holomorphic expression even at $1$. This is the cancellation in
`ZMod.differentiableAt_LFunction`. The character wrapper uses the finite
character sum and applies pointwise differentiability at every $s$
[Lean, read] ([`Mathlib/NumberTheory/MulChar/Basic.lean:425`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/MulChar/Basic.lean#L425),
[`Mathlib/NumberTheory/MulChar/Basic.lean:607`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/MulChar/Basic.lean#L607),
[`Mathlib/NumberTheory/MulChar/Basic.lean:614`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/MulChar/Basic.lean#L614),
[`Mathlib/NumberTheory/LSeries/ZMod.lean:122`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L122),
[`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:92`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L92),
[`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:98`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L98)).
When $S>0$, multiplying by $s-1$ gives a holomorphic extension near $1$
with value $S/N$ there because $\Gamma_{\mathbb R}(1)=1$. This nonzero
value proves that the pole is simple. The pinned proof also computes
the average directly as a punctured limit [Lean, read]
([`Mathlib/NumberTheory/LSeries/ZMod.lean:136`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L136)).

For uniqueness, let $U=\mathbb C$ for a nonprincipal character and
$U=\mathbb C\setminus\{1\}$ for a principal character. Both are open and
connected. Any continuation on $U$ and $F_\chi$ agree in a neighborhood
of $2$ by the grouping lemma. The set on which their difference vanishes
in a neighborhood is nonempty and open in $U$. At a limit point in $U$,
a first nonzero coefficient in the local power series would make the
zeros isolated. Hence every coefficient vanishes there, so the set is
also closed in $U$. Connectedness gives equality throughout $U$.
The pinned identity principle uses the same neighborhood-equality
and preconnectedness hypotheses
([`Mathlib/Analysis/Analytic/Uniqueness.lean:223`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Uniqueness.lean#L223)).
The Euler-factor comparison is used in Chapter 2. The classical finite-sum formula appears in [DLMF §25.15(i), equation (25.15.3)](https://dlmf.nist.gov/25.15.E3).

**Notes on the examples.** For $\chi_3$, the opposite weights cancel
the common pole, so the total Lean value at $1$ belongs to the entire
continuation. For $\chi_{0,4}$, the weights add and the pole has residue
$2/4=1/2$. Lean still assigns a complex value at $1$. Its Hurwitz
terms there are the regularized limits after subtracting $B$
[Lean, read] ([`Mathlib/NumberTheory/LSeries/HurwitzZeta.lean:96`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L96)).
The residue comes from the punctured limit of $(s-1)F_{\chi_{0,4}}(s)$. The
archive therefore excludes $(\chi,s)=(1,1)$ in its half-plane statement
(`src/Statements.lean:8`).

There is also an exact check outside the convergence half-plane.
By the classical formula $\zeta(0,a)=1/2-a$ for $0<a<1$,
$L(0,\chi_3)=(1/2-1/3)-(1/2-2/3)=1/3$ and
$L(0,\chi_{0,4})=(1/2-1/4)+(1/2-3/4)=0$.
These values use the continuation just identified and the separate
classical value formula [Paper].
[DLMF §25.11(iv), equation (25.11.13)](https://dlmf.nist.gov/25.11.E13).

**Reading boundary.** The completed Hurwitz series and the underlying
theta kernels and modified Mellin transform arguments remain [Lean]
at their cited interfaces and [Open] for deeper reading
([`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:297`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L297),
[`Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:339`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean#L339),
[`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:376`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L376)).

#### 1.3.2.1 The odd Hurwitz part and its Mellin transform

An odd character weights $j$ and $-j$ with opposite signs in the finite Hurwitz sum. The relevant projection is therefore half the difference of the Hurwitz functions at the two shifts. To construct its continuation, weight each point of a shifted lattice by its signed distance from the origin. This weight kills the zero-distance term. The transformed kernel also has zero constant term, so the resulting Mellin integral needs no endpoint corrections.

**Examples.** At $a=1/2$, the shifts coincide and the lattice terms cancel in pairs $n\leftrightarrow -n-1$. At $a=1/4$, the two one-sided sums involve the positive integers congruent to $1$ and $3$ modulo four, respectively. Their difference produces the odd character modulo four.

**Definitions.** Fix $a\in\mathbb R/\mathbb Z$, represented by any real number, and put $e(u)=\exp(2\pi i u)$. For $t>0$ define
$$
 F_a(t)=\sum_{n\in\mathbb Z}(n+a)e^{-\pi(n+a)^2t},
 \qquad
 G_a(t)=2\sum_{n\ge1}n\sin(2\pi na)e^{-\pi n^2t}.
$$
Integer shifts of $a$ reindex the first sum and preserve the second. Both kernels change sign under $a\mapsto-a$. We use Jacobi's transformation from Gaussian Poisson summation and the classical Gamma integral and entire reciprocal Gamma function as inputs.

**Kernel lemma.** Both kernels are continuous for $t>0$ and exponentially small as $t\to\infty$ for fixed $a$. They satisfy $F_a(t)=t^{-3/2}G_a(1/t)$ and $G_a(t)=t^{-3/2}F_a(1/t)$. At $0^+$ both are $O(t^r)$ for every real $r$.

**Proof.** Write $\Theta(z,\tau)=\sum_{n\in\mathbb Z}\exp(\pi i n^2\tau+2\pi i nz)$ for $\Im\tau>0$. The Gaussian majorant on compact subsets also bounds the derivative series in $z$. Completing the square gives
$$
 F_a(t)=e^{-\pi a^2t}
       \left(\frac{\Theta_z(ait,it)}{2\pi i}+a\Theta(ait,it)\right).
$$
The quotient $\Theta_z(a,it)/(-2\pi)$ equals $G_a(t)$ because pairing opposite frequencies gives $-in(e(na)-e(-na))=2n\sin(2\pi na)$. Differentiate Jacobi's identity
$$
 \Theta(z,\tau)=(-i\tau)^{-1/2}e^{-\pi i z^2/\tau}
                     \Theta(z/\tau,-1/\tau).
$$
The derivative of the exponential brings down $-2\pi iz/\tau$. At $z=ait,\ \tau=it$ that term cancels the $a\Theta$ term in $F_a$. The Gaussian factors cancel, leaving $t^{-1/2}/(2\pi i\cdot it)=-t^{-3/2}/(2\pi)$ times $\Theta_z(a,i/t)$. Interchanging $t$ and $1/t$ gives the second inversion.

After dropping the zero-distance term, let $d>0$ be the least absolute distance in the shifted lattice. For $t\ge1$, the absolute sum for $F_a$ is at most $e^{-\pi d^2t/2}\sum_n |n+a|e^{-\pi(n+a)^2/2}$. The same estimate for $G_a$ uses minimum positive frequency $1$ and $|\sin|\le1$. Gaussian majorants for $t\ge\eta>0$ give local uniform convergence and continuity. Inversion now bounds each kernel near zero by $Ct^{-3/2}e^{-c/t}$ for some $c>0$, which beats every power of $t$. At infinity the exponential bounds likewise beat every power. $\square$

**Proposition (odd Hurwitz continuation and reflection).** Under the stated Poisson and Gamma inputs, set
$$
 M_H(w)=\int_0^\infty H(t)t^{w-1}\,dt,\qquad
 w=\frac{s+1}{2},\qquad D(s)=\Gamma_{\mathbb R}(s+1)=\pi^{-w}\Gamma(w).
$$
Then $C_a(s)=M_{F_a}(w)/2$ and $T_a(s)=M_{G_a}(w)/2$ are entire, and $C_a(1-s)=T_a(s)$ for all $s$. Multiplying by the entire reciprocal $D^{-1}$ defines entire functions $O_a=D^{-1}C_a$ and $S_a=D^{-1}T_a$. On $\Re s>1$,
$$
 O_a(s)=\frac12\sum_{\substack{n\in\mathbb Z\\n+a\ne0}}
                 \frac{\operatorname{sgn}(n+a)}{|n+a|^s},
 \qquad S_a(s)=\sum_{n\ge1}\frac{\sin(2\pi na)}{n^s}.
$$
For $0<a<1$, the odd series equals $(\zeta(s,a)-\zeta(s,1-a))/2$ in that region. At the zero class of the circle it is identically zero.

**Proof.** Use real logarithms in the positive-real powers. On each compact set of $w$, both endpoint estimates dominate the Mellin integrands and their parameter derivatives, which insert a factor $\log t$. For difference quotients, integrate this derivative along the segment joining the two parameters and use the same integrable majorant on a slightly larger compact disk. Dominated convergence gives entire transforms. Absolute convergence permits $u=1/t$:
$$
 M_{F_a}(3/2-w)=\int_0^\infty G_a(1/t)t^{-w-1}\,dt
               =\int_0^\infty G_a(u)u^{w-1}\,du.
$$
The shift matters because $3/2-w=(2-s)/2$ is the Mellin parameter for $1-s$. Both completions use the same half.

For $r\ne0$, substituting $u=\pi r^2t$ gives
$$
 \int_0^\infty r e^{-\pi r^2t}t^{w-1}\,dt
 =\Gamma(w)\pi^{-w}\operatorname{sgn}(r)|r|^{1-2w}
 =D(s)\operatorname{sgn}(r)|r|^{-s}.
$$
The absolute integral is $\Gamma(\Re w)\pi^{-\Re w}|r|^{-\Re s}$. For $\Re s>1$ these quantities are summable over $r=n+a\ne0$, and likewise over $r=n\ge1$ with bounded sine coefficients. This permits termwise integration. For $G_a$ the $2$ cancels the defining half, and $D$ is nonzero on this half-plane. Splitting at $n=0$ with negative indices written $-m-1$ gives the one-sided Hurwitz difference. The identity theorem gives uniqueness of the entire continuation. At integral $a$ the signed lattice cancels and the sine coefficients vanish. $\square$

**Finite-sum identification and reflection.** For $N\ge1$, let $\Phi$ be odd on $\mathbb Z/N\mathbb Z$, and put $a_j=j/N\bmod1$. In the ordinary finite Hurwitz sum and in its Mathlib completion, the even contributions sum to zero under $j\mapsto-j$. Thus
$$
 L_\Phi(s)=N^{-s}\sum_j\Phi(j)O_{a_j}(s),\qquad
 \mathcal C_\Phi(s)=N^{-s}\sum_j\Phi(j)C_{a_j}(s).
$$
Both are entire, with $L_\Phi=D^{-1}\mathcal C_\Phi$. The convergence-region identification in §1.3.2 therefore identifies this same entire function for an odd character, whether primitive or imprimitive.

Use the unnormalized discrete Fourier transform $\widehat\Phi(k)=\sum_j\Phi(j)e(-jk/N)$. It is odd by reindexing. The sine coefficient is
$$
 \sum_j\Phi(j)\sin(2\pi jk/N)
 =\frac{-\widehat\Phi(k)-\widehat\Phi(k)}{2i}
 =i\widehat\Phi(k).
$$
On $\Re s>1$, summing the sine Dirichlet series gives $iL_{\widehat\Phi}(s)$. The Lean proof computes this equality by subtracting exponential zeta sums with opposite phases. Multiplying by $D(s)$ gives $\sum_j\Phi(j)T_{a_j}(s)=i\mathcal C_{\widehat\Phi}(s)$. Applying the odd Hurwitz reflection to each summand at $1-s$ and using the identity theorem yields, for all $s$,
$$
 \mathcal C_\Phi(1-s)=N^{s-1}i\mathcal C_{\widehat\Phi}(s).
$$

For a primitive odd character, insert the primitive Fourier–Gauss formula $\widehat\chi(k)=\tau(\chi)\chi^{-1}(-k)$ with $\tau(\chi)=\sum_j\chi(j)e(j/N)$. The sign $\chi^{-1}(-1)=-1$ combines with $i$ to give $1/i$. Hence the odd branch of the primitive-character equation is
$$
 \mathcal C_\chi(1-s)=N^{s-1/2}\frac{\tau(\chi)}{i\sqrt N}\,
                                  \mathcal C_{\chi^{-1}}(s).
$$
The completion here uses just the Gamma factor. The conductor power is separate, as in Mathlib. Primitivity is used in the Fourier–Gauss substitution.

**The examples at $s=0,1$.** At $a=1/2$, the kernel cancellation gives $C_a=T_a=O_a=S_a=0$ at both points and everywhere else. For $a=1/4$, let $\chi_4$ have values $0,1,0,-1$ at $0,1,2,3$. This character is primitive since both proper divisor moduli have only the trivial character. Since $\sin(\pi n/2)=\chi_4(n)$, writing $\beta=L_{\chi_4}$ gives $S_{1/4}=\beta$ and $O_{1/4}=(4^s/2)\beta$. Their series identification extends to all $s$ by the identity theorem. For real $s>1$ each grouped difference $(4m+1)^{-s}-(4m+3)^{-s}$ is positive. Directly $\tau(\chi_4)=i-(-i)=2i$ and $\widehat\chi_4(k)=-2i\chi_4(k)$, giving root number $1$.

The alternating-series remainder is uniform for real $s\ge1$, bounded by the first omitted term with $s=1$. Taking $s\downarrow1$ gives $\beta(1)=1-1/3+1/5-\cdots=\pi/4$, the last evaluation by Abel's theorem for the arctangent series. Since $D(0)=1$ and $D(1)=1/\pi$, we have $T_{1/4}(1)=C_{1/4}(0)=O_{1/4}(0)=1/4$ and $\beta(0)=1/2$. Also $O_{1/4}(1)=\pi/2$ and $C_{1/4}(1)=T_{1/4}(0)=1/2$.

**Domain and source notes.** In general $O_a(0)=S_a(1)/\pi$ and $S_a(0)=O_a(1)/\pi$. At those points the Mellin parameters are $1/2$ and $1$, both in the domain of the integral. At $s=1$ in the modulo-four example, the absolute integrals of the nonzero summands have a divergent harmonic tail. The kernel integral and paired series still converge. At $s=0$ even the individual beta series terms fail to tend to zero. At negative odd integers, the reciprocal Gamma factor gives zeros of the ordinary functions, regardless of the values of their completions.

The ordinary reflection is $O_a(1-s)=D(1-s)^{-1}D(s)S_a(s)$ wherever $D(s)$ is finite. Gamma reflection and duplication express the coefficient there, by continuation at removable singularities, as $2(2\pi)^{-s}\Gamma(s)\sin(\pi s/2)$ for $s$ outside the nonpositive integers. Its value at $s=1$ is $1/\pi$ and its limit at $s=0$ is $\pi$, since $\Gamma(s)\sim1/s$. Indeed reflection gives the reciprocal of $\Gamma(1-s/2)$ as $\Gamma(s/2)\sin(\pi s/2)/\pi$, and duplication gives the product of $\Gamma(s/2)$ and $\Gamma((s+1)/2)$ as $2^{1-s}\sqrt\pi\,\Gamma(s)$. The analogous sine reflection follows by exchanging the two completed functions. The odd bracket in the classical primitive-character equation is $-2i\sin(\pi s/2)$, consistent with the coefficient obtained from the signed Fourier convention. The classical special value $\zeta(0,a)=1/2-a$ independently gives $O_{1/4}(0)=1/4$ from the difference of shifts. [DLMF 25.11.13](https://dlmf.nist.gov/25.11.E13) [DLMF 25.15.5](https://dlmf.nist.gov/25.15.E5)

The odd kernel wrappers, Mellin specialization, completed reflection and local odd finite-sum consumers are [Lean, read] at Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474 in archive A2 (SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc). The [proof map](../notes/proof-map.md#p1-chapter-1-odd-hurwitz-continuation) gives the declarations, argument substitutions and retained analytic inputs.

### 1.3.3 Quantifiers: what is covered

The statements quantify over every modulus $N$ (the instance `[NeZero N]` just says $N\ge1$),
over every character mod $N$ with complex values, primitive or not, trivial or not, and over every
complex $s$ in the stated region. The only exclusion in the half-plane statement is the pair
$(\chi,s)=(1,1)$, which is where the trivial character has its pole. "Primitive" is Mathlib's
notion: $\chi$ is primitive when its conductor, the least $d$ such that $\chi$ factors through
$(\mathbb Z/d\mathbb Z)^\times$, equals $N$ [Lean] (`IsPrimitive`,
`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:292`; `conductor`, `:246`).

### 1.3.4 The strip statement is the full GRH for Dirichlet L-functions

The third statement only speaks about the open strip $0<\Re s<1$. Nothing is lost, for the same
reasons as for $\zeta$ [Expository]:

- there are no zeros with $\Re s\ge1$ (except the excluded pole) [Lean]
  (`LFunction_ne_zero_of_one_le_re`,
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:398`);
- for primitive $\chi$, the functional equation
  $\Lambda(1-s,\chi)=N^{s-1/2}\,\varepsilon(\chi)\,\Lambda(s,\bar\chi)$ of the completed
  L-function [Lean] (`IsPrimitive.completedLFunction_one_sub`,
  `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:284`) shows that the zeros with
  $\Re s\le0$ are the trivial zeros coming from the Gamma factor;
- for imprimitive $\chi$ induced from a primitive $\chi^*$, the extra zeros are those of the
  Euler factors $1-\chi^*(p)p^{-s}$ with $p\mid N$, which lie on $\Re s=0$.

So `DirichletLZerosOnLine` is GRH for all Dirichlet L-functions in the usual sense. The
half-plane statement `DirichletLNonvanishingRightOfHalf` is equivalent to it, by the reflection
argument in Section 1.4; the archive proves the half-plane form first and derives the strip forms.
The Comparator notes make the same point about imprimitive characters [Community].

### 1.3.5 What is not covered

"GRH" in these statements means Dirichlet L-functions of $\mathbb Q$, and nothing else. In
particular the theorems say nothing directly about

- Hecke L-functions of number fields other than $\mathbb Q$, and Dedekind zeta functions of
  non-abelian number fields (the "extended Riemann hypothesis"),
- Artin L-functions and automorphic L-functions of higher rank.

Two qualifications. Dedekind zeta functions of *abelian* number fields factor into Dirichlet
L-functions of primitive characters, so RH for them does follow [Expository]. And Alpöge's note
says only that he expects the extended Riemann hypothesis "with more time" [Paper; remark p. 1].
Sutherland's verification page states the scope in one line: "'GRH' here means Dirichlet
L-functions only" [Community].

## 1.4 The internal target and the reduction to it

### 1.4.1 Definitional identities checked by the kernel

The archive's working statement is [Lean, read]
(`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13`):

```lean
def UpperTheory.EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

Its body is, symbol for symbol, the body of `DirichletLNonvanishingRightOfHalf`
(`src/Statements.lean:6`) and of `Claim.HalfPlane`
(`src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean:3`). But textual
identity of definitions in different files is not what makes the final theorems correct. What
does is that the kernel accepted each proof term at the stated type, which forces the relevant
definitions to unfold to the same proposition. Reading `src/Main.lean` with this in mind gives four
small facts that the kernel has checked [Lean, read]:

- `src/Main.lean:4` and `src/Main.lean:6` use the same term `rhOfAll`, whose type is Mathlib's
  `RiemannHypothesis` (`src/Supplements/Kernels/MainTheorems.lean:9`). So
  `RiemannZetaZerosOnLine` and `RiemannHypothesis` are definitionally equal. (They differ in
  appearance only: Mathlib writes `-2 * (n + 1)` and lets the coercion $\mathbb N\to\mathbb C$
  be inserted during elaboration; `src/Statements.lean` writes the coercion explicitly.)
- `src/Main.lean:8` proves `DirichletLNonvanishingRightOfHalf` with `allChi`, whose type is
  `UpperTheory.EveryCharacter` (`src/Supplements/Kernels/MainTheorems.lean:7`).
- `src/Main.lean:10` proves `DirichletLZerosOnLine` with the second component of `claimAll`,
  whose type is `Claim.Strip` (`src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean:6`).
- `src/Main.lean:12` proves `PrimitiveDirichletLZerosOnLine` with `critAll`, whose binders and
  conclusion are those of the statement (`src/Supplements/Kernels/MainTheorems.lean:11`).

### 1.4.2 From one half-plane to five theorems

The four reductions below are short and use only Mathlib's lemmas. `RhOfRight.lean` imports
Mathlib alone (`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:1`), and `ClaimStrip.lean`
imports only `HalfPlane.lean` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:1`),
which imports Mathlib alone (`src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean:1`)
[Lean, read]. `CritLine.lean` imports the file that defines `EveryCharacter`, and with it about
14,300 modules (our import count), but apart from one another the only archive declarations its three theorems
mention are the definition `UpperTheory.EveryCharacter` and `Formalism.VW.rh_of_right` (our check of every
identifier in the file against the declaration index) [Lean, read]. The passage from
`EveryCharacter` to the five final statements can therefore be audited without opening any other
part of the archive. We read all four proofs; the mathematics
is the following, and Chapter 2 gives it in full detail.

**RH from the half-plane.** `Formalism.VW.rh_of_every` specializes `EveryCharacter` to $N=1$ and
the trivial character, rewrites `LFunction 1` as `riemannZeta`, and obtains: $\zeta(s)\ne0$
whenever $\Re s>1/2$ and $s\ne1$ [Lean, read]
(`src/Formalism/GammaFactorNonvanishing/CritLine.lean:29`). Then `Formalism.VW.rh_of_right`
derives Mathlib's `RiemannHypothesis` from that [Lean, read]
(`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5`). Let $\zeta(s)=0$ with $s$ neither a
trivial zero nor $1$. If $\Re s>1/2$ the hypothesis is contradicted. If $\Re s<1/2$, put
$w=1-s$, so $\Re w>1/2$, $w\ne1$ (as $s\ne0$, because $\zeta(0)\ne0$) and $w\notin\{0,-1,-2,\dots\}$.
Applying `riemannZeta_one_sub` at $w$ gives
$$0=\zeta(s)=\zeta(1-w)=2(2\pi)^{-w}\,\Gamma(w)\,\cos(\pi w/2)\,\zeta(w).$$
Here $2(2\pi)^{-w}\ne0$, $\Gamma(w)\ne0$ since $\Re w>0$, and $\zeta(w)\ne0$ by hypothesis. The
cosine vanishes only if $w=2k+1$ for an integer $k$, i.e. $s=1-w=-2k$. Then $\Re s=-2k<1/2$
forces $k\ge0$; $k=0$ gives $s=0$, impossible since $\zeta(0)\ne0$; and $k\ge1$ gives a trivial
zero $s=-2k$, excluded by hypothesis. Hence the case $\Re s<1/2$ cannot occur, and
$\Re s=1/2$. The Lean proof carries out exactly this case analysis
(`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:34` onwards).

**Primitive characters in the strip.** `Formalism.VW.critLine` takes a primitive $\chi$ and a
zero $s$ with $0<\Re s<1$ [Lean, read]
(`src/Formalism/GammaFactorNonvanishing/CritLine.lean:11`). If $\Re s>1/2$, the hypothesis is
contradicted directly. If $\Re s<1/2$, the zero of $L(s,\chi)$ is a zero of Mathlib's completed
function $\Lambda(s,\chi)=\Gamma_{\mathbb R}(s+\mathfrak a)\,L(s,\chi)$, where
$\mathfrak a\in\{0,1\}$ is the parity of $\chi$ (`gammaFactor`,
`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:207`;
`LFunction_eq_completed_div_gammaFactor`, `:259`), because the Gamma factor does not vanish for
$\Re s>0$ (`Formalism.VW.gammaFactor_ne_zero`,
`src/Formalism/GammaFactorNonvanishing/CritLine.lean:6`); the functional equation for the
primitive character $\chi^{-1}=\bar\chi$ (which is primitive with the same conductor) moves it
to a zero of $L(1-s,\bar\chi)$ with $\Re(1-s)>1/2$, contradicting the hypothesis for $\bar\chi$.

**All characters in the strip.** `Claim.strip` handles an arbitrary $\chi$ mod $N$ [Lean, read]
(`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:59`). A zero of
$L(s,\chi)$ with $0<\Re s<1$ is a zero of $L(s,\chi^*)$ for the primitive character $\chi^*$
inducing $\chi$, because
$L(s,\chi)=L(s,\chi^*)\prod_{p\mid N}(1-\chi^*(p)p^{-s})$ and each factor satisfies
$|\chi^*(p)p^{-s}|\le p^{-\Re s}<1$ (`Claim.prim_zero` and `Claim.factor_ne_zero`,
`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:23`, `:7`). Then the
reflection step for primitive characters (`Claim.prim_reflect`, `:42`) finishes as above.

**RH a second time.** `Claim.zeta` derives RH from the half-plane statement through
`Claim.strip` for $0<\Re s<1$, Mathlib's non-vanishing for $\Re s\ge1$, and, for $\Re s\le0$, the
functional equation of the completed zeta function together with the zeros of
$\Gamma_{\mathbb R}$ [Lean, read]
(`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:75`). The file closes with
`Claim.zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl` (`:102`), another kernel-checked
definitional identity. `src/Main.lean` does not use this second derivation for its first theorem; it
is part of `claimAll` (`src/Supplements/Kernels/MainTheorems.lean:15`).

**From primitive to all characters, in the half-plane.** For completeness: the archive's own
route to `EveryCharacter` proves non-vanishing for primitive characters first and then extends it
to all characters by the same Euler-factor argument (`UpperTheory.Top.imprimitive`,
`src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5`) [Lean, read].

### 1.4.3 The consequence for the reader

Everything that is hard about the formal proof is the proof of one statement:

$$\textbf{(EC)}\qquad L(s,\chi)\neq0\quad\text{for every Dirichlet character }\chi\text{ and every }s\text{ with }\Re s>\tfrac12,\ (\chi,s)\ne(1,1).$$

Its proof, `UpperTheory.FinalTheorems.everyCharacter`
(`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:10`), is where
nearly all of the archive comes in: the file that contains it imports 175,173 of the 175,187
modules (our import count). The rest of this book is about that proof. The present chapter
only needs one fact about it: the theorem has no hypotheses. Every hypothesis bundle used along
the way — and there are many — is itself proved, because otherwise `allChi` could not have the
type `UpperTheory.EveryCharacter` with no arguments (`src/Supplements/Kernels/MainTheorems.lean:7`)
[Lean, read].

## 1.5 What "checked by Lean" means, and what the archive does

### 1.5.1 The guarantee

Lean is built around a small kernel that type-checks every declaration added to the environment.
Elaboration, tactics and automation run outside the kernel and are not trusted: they produce
terms, and the kernel checks the terms. A proof is therefore as reliable as (i) the kernel's
implementation, (ii) the axioms it uses, and (iii) the definitions in its statement
[Expository]. Point (iii) was the subject of Sections 1.2–1.4. Points (i) and (ii) are settled
by audits, which we now describe.

The standard axioms of Lean's foundations are `propext` (propositional extensionality),
`Classical.choice` (the axiom of choice) and `Quot.sound` (soundness of quotients). Mathlib
uses all three. A proof that uses any other axiom — for instance `sorryAx`, which `sorry`
introduces, or a user-declared `axiom` — is conditional on it, and Lean's command
`#print axioms t` lists every axiom on which `t` depends.

### 1.5.2 Axiom audits

Sutherland reports that `#print axioms` for the five theorems of `src/Main.lean` lists only
`propext`, `Classical.choice` and `Quot.sound`, and that the environment contains 15 axioms, all
in Lean's core library `Init` [Community; math.mit.edu/~drew/grh, version of 2026-11-20 22:05 UTC].
The LUMI run reports a finer audit from the compiled environment, in which 292 declarations
were examined one by one (the five theorems, the 243 `UpperTheory.LiteratureTheorems.*` and the
main internal steps): each depends on the same three axioms only [Community; LUMI README, commit
`82d91dbb`]. We have not run `#print axioms` ourselves: it needs the compiled archive, and the public
builds took hundreds of core-hours (about 900 for the LUMI compile itself) [Community; LUMI README].

### 1.5.3 Our text scan

As a complement — not a substitute — we scanned the source text of all 175,187 files
(`static_scan.py` in the run directory; 123 s CPU). The scan counts files containing each token:

| Token or construct | Files | Comment |
|---|---:|---|
| `axiom` declaration | 0 | |
| `sorry`, `admit` | 0, 0 | |
| `native_decide`, `ofReduceBool` | 0 | these would trust compiled code |
| `opaque` declaration | 0 | |
| `implemented_by`, `@[extern]` | 0 | |
| `unsafe` | 0 | |
| `set_option debug.*`, `skipKernelTC` | 0 | |
| `decide +kernel` | 34 | evaluation by the kernel itself, no compiled code |
| `set_option maxHeartbeats 0` | 4 | removes a time limit; no effect on soundness |
| `run_tac` | 16 | |
| `kexactB` | 50 | see below |
| `kcopy` | 4 | see below |
| `addDecl` | 1 | see below |
| lines beginning with `elab`, `macro`, `macro_rules` or `syntax` | 22 | custom syntax; see Section 1.5.4 |

A text scan can miss a construct introduced through a macro or a notation, and it cannot see
what a tactic does. It is useful as a map of where to look, and its zero counts agree with the
static scans reported by the LUMI run and by the Comparator notes [Community]. The Comparator notes
add that all notation in the archive is `local` or `scoped`, and that nothing in the source
reads or writes files, starts processes or reads the environment [Community]. The LUMI scan also
lists elaboration options such as `allowUnsafeReducibility true` (37 occurrences) and
`backward.isDefEq.respectTransparency false` (1,877) [Community]; such options change how the
elaborator searches for a proof term, not which terms the kernel accepts [Expository].

### 1.5.4 Metaprogramming in the archive

Four uses of Lean's metaprogramming facilities deserve a sentence each, because a reader who
finds them in the source may worry about them. The Comparator notes list the same items and
reach the same conclusion [Community; `verification/NOTES.md`, corrected after issue #2].

- **`kexactB`.** Defined in four lines [Lean, read]
  (`src/Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean:5`), it
  elaborates a term *without* an expected type and assigns it to the current goal. The
  elaborator therefore does not check that the term's type matches the goal. The kernel does,
  when the enclosing declaration is added: a mismatched term produces a declaration that the
  kernel rejects. Our grep finds 72 files that mention `kexactB` or the small macros `kc%`,
  `tr_via` and `tr_clause` built on it (including the files that define those macros); the
  Comparator notes count 67 files of use [Community].
- **`kcopy`.** A tactic defined at
  `src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:53` which, like `kexactB`,
  elaborates its argument without an expected type before assigning it [Lean] (we read its first
  lines); according to the Comparator notes it and the command `#kcopy_probe` rebuild a term
  field by field [Community]. Same remark.
- **`addDecl`.** The command `cpt_copy_thms`
  (`src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:87`) copies a
  set of existing definitions and theorems under new names, replacing the constants they refer
  to by the corresponding copies, and adds each copy with `addDecl`
  (`src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:78`) [Lean, read].
  `addDecl` submits the copy to the kernel, which checks it like any other declaration.
- **`BuildAid`.** The five files `src/BuildAid/D1.lean` … `src/BuildAid/D5.lean` each add one namespace
  (`CompanionTheory`, `CrystallineSemistableComparison`, `GlobalTheory`, `PositivityTheory`,
  `UpperTheory`) to the deny list of Lean's library-suggestion tool, for example
  `src/BuildAid/D1.lean:4` [Lean, read]. They contain no mathematics.

The general lesson is that in this archive "the tactic succeeded" is weak evidence and "the
kernel accepted the declaration" is the evidence that counts. That is why the independent kernel
replays in Section 1.6 matter.

### 1.5.5 Toolchain and Mathlib

The archive pins Lean `v4.33.1` (`lean-toolchain:1`) and Mathlib at commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`lakefile.toml:16`, matching
`lake-manifest.json`) [Lean, read]. The Comparator notes report that this commit is Mathlib's
tag `v4.33.1`, one commit on top of tag `v4.33.0` that changes only `lean-toolchain`, and that
each of the other eight pins in `lake-manifest.json` is a commit on the default branch (`main` or
`master`) of the corresponding upstream repository [Community]. Sutherland reports that the
8,322 Mathlib and 378 dependency `.olean` files used in his build are byte-identical to the
official cache [Community].

The same notes record which known Lean kernel issues the pinned version does and does not
include. The kernel soundness fixes released up to 4.33.1 are in, among them the fix for issue
#14576 (an axiom-free proof of `False` through wrong-structure projections). The runtime fixes
of 4.34.1 (issues #15241 and #15289, which according to the release notes could potentially be
turned into a proof of `False` with deliberately constructed input) are not [Community]. A pass by the 4.33.1 kernel alone is therefore weaker
evidence than passes by kernels not built on Lean's runtime and by a newer Lean; this is why the
nanoda and con-leche results, and the pending Comparator run under Lean 4.36.0, matter
[Expository].

## 1.6 Public verification status

The table summarizes what has been reported, by whom and when. All times are UTC on
2026-11-20 unless stated. "Export" means the output of `lean4export` on the module `Main`, a
text file of 61,570,595,788 bytes [Community; Sutherland page] that lists the declarations of
`Main`'s environment in a format independent checkers can read without running any Lean code.

| Check | Result | Source |
|---|---|---|
| Archive integrity | The 14 parts at `alpo.ge` join to sha256 `9631b4f0…9c7fc` | our re-download, 2026-11-21 04:01–04:06; same value in all public reports |
| Compile all 175,187 modules (Lean 4.33.1, Mathlib 4.33.1) | zero errors, finished 16:43 | [Community] Sutherland page |
| Independent sandboxed compile | 175,187/175,187, no Lean error, finished 22:21; `Main.olean` and `Statements.olean` hashes identical to Sutherland's | [Community] LUMI README and `results/build-summary.json` |
| Axioms of the five theorems | `propext`, `Classical.choice`, `Quot.sound` only | [Community] Sutherland page; LUMI dependency audit |
| `leanchecker` replay, every module | 175,187/175,187, zero rejections, about 18:17 | [Community] Sutherland page |
| nanoda (independent kernel, Rust) on the export | accepts; exit 0 at 19:05; 27 min 42 s on 80 threads | [Community] Sutherland page |
| con-leche master (independently written kernel) on the export, `--verified` mode | accepts 1,468,418 declarations; exit 0 at 21:19 | [Community] Sutherland page |
| con-leche `--compare`: challenge vs. solution | all five theorems "justified by the solution" | [Community] Sutherland page |
| lean4lean, module by module | 175,187/175,187, about 21:55; five needed a raised step limit on `decide +kernel` computations | [Community] Sutherland page |
| Lean default and paranoid kernels on the export | running, no verdict | [Open] Sutherland page |
| `lake comparator` (Lean 4.36.0) end to end | statement comparison and axiom check passed in one run; kernels in progress | [Open] Sutherland page |
| Sandboxed export identical to the unsandboxed one | comparison not yet made | [Open] Sutherland page, caveats |

Three remarks on this table.

- **The challenge file.** Comparator needs a "challenge": the five statements in a file that
  imports only Mathlib, with `sorry` as proofs. The archive does not ship one; the
  `leanprover-community/riemann-hypothesis` setup supplies `src/Challenge.lean` [Community]. We
  compared it with the archive: its four definitions are byte-identical to lines 3–16 of
  `src/Statements.lean`, and its five theorem statements are those of `src/Main.lean` (our
  `diff`, 2026-11-21 04:23 UTC).
- **Builds without a sandbox.** Compiling a Lean file runs code, so a malicious archive could in
  principle tamper with a build environment [Expository]. Sutherland's build ran without a
  sandbox and he says so; the LUMI build and the Comparator protocol use sandboxes [Community]. The
  identical `Main.olean` hashes from the sandboxed LUMI build make tampering with Sutherland's
  build implausible [Expository]; the pending comparison of a sandboxed export with the
  unsandboxed one would close the point [Open].
- **What is still running.** At our latest check (2026-11-21 12:42 UTC), Sutherland's page
  (updated 2026-11-21 10:05 UTC) added unconditional `kimihiro64/Robin1984` divisor-sum checks
  and a 240-module `lake build` path check, Lipponen's LUMI repository (updated 12:40 UTC)
  completed a full compiled-environment dependency walk across all 1,478,243 constants, and
  Ishaan Dixit reported that an independent unsandboxed `lean4export` matched Sutherland's
  61.57 GB export byte-for-byte (`5ea74b91…244e`) [Community]; the end-to-end `lake comparator`
  runs, the single-threaded Lean default/paranoid export kernels, and a sandboxed-export
  comparison remain in progress [Open]. Any reader of this chapter should check both pages for
  updates [Open].

Commentators have summarized the situation in strong terms. Sutherland is quoted as saying that
"the chance that anything is fishy here is approximately zero", while Buzzard, writing on the
Lean community's chat server, said that "we still await a successful comparator run" [Community;
both quoted in *Scientific American*, 2026-11-20].
Neither statement is about whether anyone understands the proof.

## 1.7 What a complete pass would and would not establish

Suppose the remaining runs finish cleanly. Then the following would be established beyond
reasonable doubt: the five Props of Section 1.1 follow from Lean's three standard axioms,
according to several independently implemented kernels.

Such a pass presupposes that Mathlib's `riemannZeta` and `DirichletCharacter.LFunction` are the
classical functions; Sutherland's page states the same proviso [Community]. Sections 1.2–1.3 give our
reasons for accepting it: each function is pinned down by its Dirichlet series in a half-plane
and by its analyticity [Expository].

It would *not* establish any of the following.

1. **That anyone understands why (EC) holds.** The LUMI README says so explicitly: a pass
   "would not establish that anyone understands the argument" [Community]. That gap is what this
   book is for.
2. **That the archive's intermediate statements mean what their names say.** This sounds
   alarming but is harmless for the truth of the final theorems: a Prop that is proved is proved,
   whatever it is called. A Prop named after Poitou–Tate duality that does not quite state
   Poitou–Tate duality, but is nonetheless proved in the archive, does not invalidate anything.
   Faithfulness of names matters for understanding and reuse, and we treat it as an
   [Open] audit item throughout [Expository].
3. **That hypothesis bundles are non-vacuous.** Also harmless for the final theorems, which have
   no hypotheses (Section 1.4.3). Vacuity questions matter only when one reads an intermediate
   theorem and wants to know whether its hypotheses can be met; the LUMI reports discuss several
   cases [Community].
4. **Anything about the extended Riemann hypothesis**, about Hecke L-functions of other number
   fields, or about Masullo's argument.

## 1.8 Masullo's intended statement, for comparison

Masullo's draft states its generality as "all number fields, all unitary Hecke characters"
[Paper; Masullo p. 6]. The statement is not yet written as a theorem. Chapter 13 announces that it will
deduce information on the zeros of Hecke L-functions of an arbitrary number field from the trace
formula of Theorem 12.5.1.1, and then restates that trace formula as Theorem 13.3.1.1, with a
spectral counting function $N_{\mathrm{spec}}(c)=\min\{N(c),[F:\mathbb Q]\}$ attached to each zero
$c$; the footnotes at that point read "Insert statement." and "State and prove the Main
Theorems, …" [Paper; pp. 521–522]. The formalization project for the draft observes that "Chapter 13,
which should deduce GRH from the trace formula, does not yet state its main theorem", and that
in its own Lean skeleton the last two target statements "were reconstructed from the
introduction and have not been reviewed" [Community; `mccorvie/riemann-masullo` README, retrieved
2026-11-21 04:05 UTC].

| | Lean archive | Masullo's draft |
|---|---|---|
| $\zeta(s)$ | RH proved (Mathlib's definition) | intended |
| Dirichlet $L(s,\chi)$ | GRH proved, all moduli and characters | intended (finite-order Hecke characters of $\mathbb Q$) |
| Hecke $L$-functions of other number fields, Dedekind $\zeta_K$ | not covered (abelian $K$ only through Dirichlet $L$) | intended |
| Form of the statement | five kernel-checked Lean theorems | to be stated in Chapter 13 |
| Checking | compiled and replayed by several kernels; Comparator pending | read closely by B. Conrad for months, per Vakil's announcement; community formalization of prerequisites in progress |

In short, Masullo's target is strictly broader, and the Lean theorem is far better established.
Chapters 2–13 explain the method of the Lean proof, Chapter 14 explains Masullo's, and
Chapter 15 compares them.

## 1.9 Checking this chapter yourself

The Lean facts in this chapter can be checked without building the archive:

```bash
# fetch and verify (the shell's brace range {01..14} does not zero-pad in bash 3.2; use seq -w)
for i in $(seq -w 1 14); do curl -sSLO https://alpo.ge/lean.tar.gz.part$i; done
for i in $(seq -w 1 14); do cat lean.tar.gz.part$i; done > lean.tar.gz
shasum -a 256 lean.tar.gz      # 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc
tar -xzf lean.tar.gz
sed -n 1,12p lean/src/Main.lean
sed -n 1,16p lean/src/Statements.lean
sed -n 1,16p lean/src/Supplements/Kernels/MainTheorems.lean
sed -n 1,33p lean/src/Formalism/GammaFactorNonvanishing/CritLine.lean
sed -n 1,63p lean/src/Formalism/GammaFactorNonvanishing/RhOfRight.lean
sed -n 1,105p lean/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean
```

The Mathlib lines are at
`https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean`
and the neighbouring files cited above.

**Summary of the chapter.** The five final theorems state RH and GRH for Dirichlet L-functions
faithfully, in terms of Mathlib's definitions [Lean, read], which are the classical functions
[Expository]. All five follow, by short Mathlib-only arguments that we have
read, from the single statement (EC) [Lean, read]. The axioms are the standard three [Community],
the archive contains no `sorry`, no declared axiom and no code-trusting construct in its source
text (our scan), and the proof has passed several independent kernels [Community]. The end-to-end
Comparator run and the Lean kernels' replay of the export are still pending [Open].
