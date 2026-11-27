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

The input from **Gaussian Poisson summation** is $f_a(t)=t^{-1/2}g_a(1/t)$. In Mathlib, the kernel proof substitutes $z=ait$ and $\tau=it$ into the two-variable Jacobi theta transformation. Then $z/\tau=a$ and $-1/\tau=i/t$. The exponential multiplier cancels $e^{-\pi a^2t}$, leaving the reciprocal of the positive square root of $-i\tau=t$. The theta transformation invokes `Complex.tsum_exp_neg_quadratic`, retained here as an imported Poisson input and read in full in §1.2.2.7 [Lean, read]. [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:132–153](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L132-L153) · [Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:465–490](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean#L465-L490) · [Mathlib/Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean:87](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean#L87)

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

Two analytical obstacles stand between the pointwise theta law $f_a(1/x)=x^{1/2}g_a(x)$ and a global functional equation on $\mathbb C$. First, the unmodified Mellin integrals of $f_a$ and $g_a$ diverge on half-planes: at $a=0$, $\int_0^\infty t^{w-1}f_0(t)\,dt$ has an *empty* domain of convergence on $\mathbb C$, while for $a\ne0$, $f_a(t)=O(e^{-c t})$ at $\infty$ and $g_a(t)=O(t^{-1/2}e^{-c/t})$ at $0^+$ make $\mathcal M(f_a)(1/2-w)$ and $\mathcal M(g_a)(w)$ converge together only on $\Re w<0$ ($\Re s<0$ for $w=s/2$), disjoint from the Dirichlet-series half-plane $\Re s>1$. Second, for a nonzero shift $a\in\mathbb R/\mathbb Z\setminus\{0\}$, the pair $(f_a,g_a)$ is not self-dual: $f_a(t)\to 0$ as $t\to\infty$ whereas $g_a(t)\to 1$, so reflection across $s\mapsto 1-s$ does not send the even Hurwitz zeta function back to itself, but exchanges it with a dual *cosine zeta* partner while swapping the pole locations $s=0$ and $s=1$. Mathlib packages both phenomena into the conditional interface `WeakFEPair`, builds an entire partner pair by piecewise subtraction with a deliberate zero at the seam $t=1$, proves Mellin inversion on the entire modified pair, and cancels the two rational pole terms algebraically before specializing to $a\in\mathbb R/\mathbb Z$ and $a=0$.

**Example (two traps: Bochner degeneracy on unmodified kernels and the seam defect at $x=1$).** Before stating the general interface, test the naive Mellin inversion on two concrete kernels from §1.2.2.1.

1. *Empty convergence strip at $a=0$ and Bochner totalization.* At $a=0$, $f_0(t)=g_0(t)=1+2\sum_{n\ge1}e^{-\pi n^2 t}$ tends to $1$ as $t\to\infty$ and behaves like $t^{-1/2}$ as $t\to0^+$. For every $w\in\mathbb C$, $t^{w-1}f_0(t)$ fails to be integrable on $(0,\infty)$: at $\infty$ convergence would require $\Re w<0$, whereas at $0$ it requires $\Re w>1/2$. In Mathlib, `mellin f w` is defined as a Bochner integral, which returns $0$ whenever the integrand is not integrable. Substituting $t\mapsto 1/t$ in `mellin f_0 (1/2 - w) = mellin g_0 w` is therefore *formally true* in Lean — both sides evaluate to $0=0$ for every $w\in\mathbb C$ — and proves nothing about $\zeta(s)$! Even if one subtracts the constant at $\infty$ beforehand, $(f_0(t)-1)=O(e^{-\pi t})$ at $\infty$ and $\sim t^{-1/2}$ at $0$, so $\int_0^\infty t^{w-1}(f_0(t)-1)\,dt$ converges on $\Re w>1/2$, while the reflected argument $1/2-w$ requires $\Re(1/2-w)>1/2$, i.e. $\Re w<0$, giving two *disjoint* half-planes. One must pass to kernels modified on $(0,1)$ and $(1,\infty)$ separately so that both sides converge on all of $\mathbb C$ simultaneously.

2. *The seam mismatch at $x=1$ when $f_\infty\ne\varepsilon g_\infty$.* Take $a=1/3$. Here $f_{1/3}(t)=\sum_{n\in\mathbb Z}e^{-\pi(n+1/3)^2 t}\to 0$ as $t\to\infty$ ($f_\infty=0$), whereas $g_{1/3}(t)=1+2\sum_{n\ge1}\cos(2\pi n/3)e^{-\pi n^2 t}\to 1$ ($g_\infty=1$), with weight $k=1/2$ and root number $\varepsilon=1$. At the inversion fixed point $x=1$, the theta identity $f_{1/3}(1/x)=x^{1/2}g_{1/3}(x)$ gives $f_{1/3}(1)=g_{1/3}(1)$ ($\approx 0.95678$). Suppose one defined the upper-tail subtraction on the *closed* ray $[1,\infty)$ and the lower-tail subtraction on $(0,1)$. Then at $x=1$ the modified $f$-kernel would take the value $f_{1/3}(1)-0=f_{1/3}(1)$, whereas the modified $g$-kernel would take the value $g_{1/3}(1)-1=f_{1/3}(1)-1$. Their difference at $x=1$ is $+1\ne0$, breaking the pointwise functional equation $f_{\mathrm{modif}}(1/x)=\varepsilon x^k g_{\mathrm{modif}}(x)$ at $x=1$. Pointwise symmetry at $x=1$ holds if and only if $f_{\mathrm{modif}}(1)=\varepsilon g_{\mathrm{modif}}(1)$ (for instance, symmetric midpoint averaging $f(1)-\frac12(f_0+\varepsilon g_0)$ also works); replacing $[1,\infty)$ by the open ray $(1,\infty)$ sets both modified kernels to $0$ at $x=1$ (`AbstractFuncEq.lean:244–246`), which is sufficient to restore exact pointwise symmetry without altering any Lebesgue integral because $\{1\}$ has measure zero.

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

**Theorem 4 (completed even Hurwitz and cosine functional equations, series identification, and $a=0$ self-duality).** Assume the Gaussian Poisson summation input (`Complex.tsum_exp_neg_quadratic`, proved in §1.2.2.7), which supplies $f_a(1/x)=x^{1/2}g_a(x)$ for every $a\in\mathbb R/\mathbb Z$ and $x>0$ (§1.2.2.1). For each $a\in\mathbb R/\mathbb Z$, set $\delta_a=1$ if $a=0$ and $\delta_a=0$ if $a\ne0$.

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

**Corollary 5 (de-completed functional equations and pointwise vs. uniform sharpness of the excluded sets).** Keep the Poisson assumption of Theorem 4 and the duplication and reflection formulas of §1.2.2.5 and [Chapter 2, §2.3.2.1](02-functional-equations-and-primitive-characters.md#2321-why-gamma-has-no-zeros-in-the-right-half-plane).

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
Moreover, under Lean's totalized values, the excluded sets in (1) and (3) are **pointwise sharp for every fixed $a\in\mathbb R/\mathbb Z$**, whereas the excluded set $s\in\{1-n:n\in\mathbb N\}$ in (2) is **sharp uniformly in $a$** (witnessed at $a=0$) but **not pointwise sharp in $a$** (for example, (2) holds as $0=0$ at $(a,s)=(1/6,0)$).

**Proof.** We track where each exclusion is spent in Mathlib's total arithmetic, and then check sharpness.

For (1), first express $E_a(1-s)$ as $\Lambda_{\mathrm{even}}(a,1-s)\cdot G(1-s)^{-1}$. By definition, $E_a(w)$ equals $\Lambda_{\mathrm{even}}(a,w)/G(w)$ away from $w=0$; at $w=0$, $G(0)=\pi^0\Gamma(0)=0$, so $\Lambda_{\mathrm{even}}(a,0)/G(0)=0$, which still agrees with the updated value $E_a(0)=-\delta_a/2$ *if and only if* $a\ne0$ ($\delta_a=0$). Thus $E_a(1-s)=\Lambda_{\mathrm{even}}(a,1-s)G(1-s)^{-1}$ holds whenever $a\ne0$ or $1-s\ne0$, which is precisely the hypothesis $(a\ne0\text{ or }s\ne1)$ (`hurwitzZetaEven_def_of_ne_or_ne`). Next, Theorem 4(2) rewrites $\Lambda_{\mathrm{even}}(a,1-s)$ as $\Lambda_{\cos}(a,s)$. From §1.2.2.5 (`Deligne.inv_Gammaℝ_one_sub`, lines 170–181), the Gamma-ratio identity
$$
 G(1-s)^{-1}=\Gamma_{\mathbb C}(s)\cos\Bigl(\frac{\pi s}{2}\Bigr)G(s)^{-1}
$$
holds under the hypothesis $\forall n\in\mathbb N,\;s\ne-n$: in Lean's proof of `inv_Gammaℝ_one_sub`, $s\ne-n$ ensures $\Gamma(s)\ne0$ so $\Gamma_{\mathbb C}(s)\ne0$ can be cancelled in $G(s)G(s+1)=\Gamma_{\mathbb C}(s)$ and $G(1-s)G(1+s)=1/\cos(\pi s/2)$. Finally, at $n=0$ the same hypothesis gives $s\ne0$, which drops the `Function.update` at $0$ in $Z_{\cos}(a,s)=\Lambda_{\cos}(a,s)G(s)^{-1}$. Rearranging the commutative product gives (1).

For (2), $Z_{\cos}(a,w)$ updates at $w=0$ with $-1/2\ne0$ for *every* $a$, so writing $Z_{\cos}(a,1-s)=\Lambda_{\cos}(a,1-s)G(1-s)^{-1}$ requires $1-s\ne0$, i.e. $s\ne1$ (the case $n=0$ of $s\ne1-n$). Theorem 4(2) at $1-s$ gives $\Lambda_{\cos}(a,1-s)=\Lambda_{\mathrm{even}}(a,s)$; the cases $n=m+1$ of $s\ne1-n$ give $\forall m\in\mathbb N,\;s\ne-m$ for `inv_Gammaℝ_one_sub`; and $n=1$ gives $s\ne0$, which drops the update at $0$ in $E_a(s)=\Lambda_{\mathrm{even}}(a,s)G(s)^{-1}$.

For (3), set $a=0$ in (1): the disjunction $(0\ne0\text{ or }s\ne1)$ simplifies to $s\ne1$, and Theorem 4(4) rewrites $E_0=\zeta$ and $Z_{\cos}(0,\cdot)=\zeta$.

To verify sharpness, hand calculation A(4) below shows that at $a=0$ every excluded point falsifies (3) (and hence falsifies (1) at $a=0$ and (2) uniformly in $a$, since $s=1$ in (2) also fails for every $a$ via $Z_{\cos}(a,0)=-1/2\ne0$). For (1) with fixed $a\in(0,1)$: at $s=-m$ ($m\ge1$), the right-hand side vanishes via $\Gamma(-m)=0$ while on the left $E_a(1+m)=\frac12\sum_{n\in\mathbb Z}\lvert n+a\rvert^{-(1+m)}>0$; at $s=0$, the right-hand side vanishes via $\Gamma(0)=0$, whereas the left-hand side is the stored value $E_a(1)=\Lambda_{\mathrm{even},0}(a,1)=-\frac12\bigl(\psi(a)+\psi(1-a)\bigr)-\frac12\bigl(\gamma+\log(4\pi)\bigr)$ (§§1.2.2.2–1.2.2.4, with $\psi=\Gamma'/\Gamma$). Because $\psi''(x)=-\sum_{k=0}^\infty(x+k)^{-3}<0$ on $(0,1)$, $\psi$ is strictly concave, so $\frac12\bigl(\psi(a)+\psi(1-a)\bigr)\le\psi(1/2)=-\gamma-2\log2$ and hence
$$
 E_a(1)\ge E_{1/2}(1)=\frac{\gamma+\log(4/\pi)}{2}\approx 0.40939>0,
$$
proving that (1) fails at $s=0$ for *every* $a\ne0$. By contrast, in (2) at the rational shift $a=1/6$, grouping residues modulo $6$ on $\Re w>1$ gives
$$
 Z_{\cos}\Bigl(\frac16,w\Bigr)=\Bigl(\frac12-2^{-w}-\frac32\,3^{-w}+3\cdot 6^{-w}\Bigr)\zeta(w)=\frac12(1-2^{1-w})(1-3^{1-w})\zeta(w);
$$
as $w\to1$, $(1-2^{1-w})$ cancels the simple pole of $\zeta(w)$ and $(1-3^{1-w})$ vanishes, forcing $Z_{\cos}(1/6,1)=0$. Thus at $(a,s)=(1/6,0)$, both sides of (2) equal $0$ ($Z_{\cos}(1/6,1)=0$ on the left and $\Gamma(0)=0$ on the right); likewise at $s=-1$ and the irrational shift $a^\ast=(3-\sqrt3)/6$ where $B_2(a^\ast)=0$, $Z_{\cos}(a^\ast,2)=\pi^2 B_2(a^\ast)=0$ agrees with $\Gamma(-1)=0$. $\square$

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
with $(f_0,g_0)=(0,1)$ whereas $P_{1/3}^{\mathrm{symm}}$ has $(f_0,g_0)=(1,0)$. As seen in the Example, $f_{1/3}(1)=g_{1/3}(1)$ while $(f_{1/3}(1)-0)-(g_{1/3}(1)-1)=1$, so setting both modified kernels to $0$ at $x=1$ is sufficient to enforce $f_{\mathrm{modif}}(1)=\varepsilon g_{\mathrm{modif}}(1)$ (and is Mathlib's convention, `AbstractFuncEq.lean:244–246`). Away from $x=1$,
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

- `hnat : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ)`: from `hlt : s.re < 1 / 2` (line 8), lines 15–17 derive `ht : 1 / 2 < (1 - s).re`; if $1-s=-n$, then $\Re(1-s)=-n\le0$, contradicting `ht` (`linarith` with `(n : ℝ) ≥ 0`, lines 22–27);
- `h1 : (1 - s) ≠ 1`: lines 11–14 first record `hs0 : s ≠ 0` from $\zeta(s)=0$ against `riemannZeta_zero` ($\zeta(0)=-1/2\ne0$), and lines 18–21 deduce $1-s\ne1$.

After rewriting `1 - (1 - s) = s`, `rh_of_right` obtains $0=\zeta(s)=2(2\pi)^{-(1-s)}\Gamma(1-s)\cos(\pi(1-s)/2)\zeta(1-s)$ and rules out each factor as explained in §1.4.2. No new RH research is involved: every step from Gaussian Poisson summation (§1.2.2.7) and `Gamma_mul_Gamma_add_half` (§1.2.2.5) to `RhOfRight.lean:28` is now accounted for in §§1.2.2.1–1.2.2.7 and Chapter 2, §2.3.2.1. A scan of the pinned Mathlib tree and all 175,187 `.lean` files of archive A2 records the consumers of this subsection's declarations below (archive consumers are listed without new analysis of their surrounding modules).

| Declaration produced here | Direct consumers in pinned Mathlib / archive A2 | Role in the book |
|---|---|---|
| `WeakFEPair.functional_equation₀`, `WeakFEPair.functional_equation` ([AbstractFuncEq.lean:421–429](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L421-L429)) | `completedHurwitzZetaEven_one_sub` and `_₀_one_sub` ([HurwitzZetaEven.lean:370, 380](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L370)); `completedHurwitzZetaOdd_one_sub` ([HurwitzZetaOdd.lean:365](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean#L365), $f_0=g_0=0$); archive `WeakFEPair` instances and `f_modif`/`Λ₀` bounds in `TateMain.lean:115, 131`, `ContinuousOnThetaCFunLtr.lean:175–220`, `FunctionalEquationPairEntirePartBound.lean:8–55`, `ContinuousSetIntegralIoiOne.lean:121–202`, `ImportsSide.lean:8–17` | Theorem 4 (even case, non-zero pole corrections) and §1.3.2.1 (odd case, zero pole corrections) |
| `completedHurwitzZetaEven_one_sub` ([HurwitzZetaEven.lean:365–372](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L365-L372)) | `completedCosZeta_one_sub` (`:385`); `hurwitzZetaEven_one_sub` (`:766`); `completedRiemannZeta_one_sub` ([RiemannZeta.lean:108](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L108)); `ZMod.completedLFunction_one_sub_of_one_lt_even` → `completedLFunction_one_sub_even` ([ZMod.lean:415, 459–505](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L415)) → `IsPrimitive.completedLFunction_one_sub` ([DirichletContinuation.lean:284–314](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L284-L314)) | Theorem 4(4), Corollary 5, §1.3.4, and Chapter 2, §2.4.2 (even primitive Dirichlet branch) |
| `completedRiemannZeta_one_sub` ([RiemannZeta.lean:106–109](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L106-L109)) | `IsPrimitive.completedLFunction_one_sub` ($N=1$ branch, `DirichletContinuation.lean:289`); archive `Claim.zeta` (`ClaimStrip.lean:99`) and `RiemannHypothesisOfEveryCharacter.lean:222` | §1.4.2 ("RH a second time") and Chapter 2, §2.4.3 |
| `hurwitzZetaEven_one_sub` ([HurwitzZetaEven.lean:760–770](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L760-L770)) | `riemannZeta_one_sub` (`RiemannZeta.lean:180`); full Hurwitz formula `hurwitzZeta_one_sub` ([HurwitzZeta.lean:156–170](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L156-L170)); Bernoulli special values `hurwitzZetaEven_one_sub_two_mul_nat` ([HurwitzZetaValues.lean:124–143](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean#L124-L143), consumer in archive `BLval.lean:8, 35`) | Corollary 5(3) and Hand calculation B(5) |
| `riemannZeta_one_sub` ([RiemannZeta.lean:178–180](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L178-L180)) | Archive `Formalism.VW.rh_of_right` (`RhOfRight.lean:28`), `RHofHalfPlane.lean:26, 56`, `ZetaZeroFreeRegion.lean:176` | §1.2.3, §1.4.2, and Chapter 2, §2.4.3 |

**Remarks.**

1. *Riemann (1859) and Jacobi (1829).* In his November 1859 *Monatsberichte* memoir `[Riemann1859]` (pp. 671–680; pp. 2–3 of Wilkins's edition), Riemann first proves the functional equation by a Hankel contour integral and remarks on p. 2 of Wilkins's edition that $\Pi(s/2-1)\pi^{-s/2}\zeta(s)$ *"bleibt ungeändert, wenn $s$ in $1-s$ verwandelt wird"* ("remains unchanged when $s$ is replaced by $1-s$"). On p. 3 he gives his second proof to exhibit that symmetry visibly: setting $\psi(x)=\sum_{n=1}^\infty e^{-n^2\pi x}$, quoting $2\psi(x)+1=x^{-1/2}(2\psi(1/x)+1)$ from Jacobi's *Fundamenta Nova* `[Jacobi1829]` (p. 184), splitting the Mellin integral of $\psi$ at $x=1$, and substituting $x\mapsto 1/x$ on $(0,1)$ to write
$$
 \Pi\Bigl(\frac s2-1\Bigr)\pi^{-s/2}\zeta(s)=\frac{1}{s(s-1)}+\int_1^\infty\psi(x)\bigl(x^{s/2-1}+x^{-(1+s)/2}\bigr)\,dx.
$$
Because Riemann starts from $\psi(x)=(f_0(x)-1)/2$, the upper subtraction $f_0=1$ is built in before splitting; on $(0,1)$, rewriting $\psi(x)=\frac12 x^{-1/2}+\frac12 x^{-1/2}\cdot 2\psi(1/x)-\frac12$ produces both pole terms $\frac{1}{s-1}-\frac{1}{s}=\frac{1}{s(s-1)}$ from the lower interval $(0,1)$. Mathlib's `WeakFEPair` obtains the identical right-hand side without splitting an already-convergent integral on $\Re s>1$ first: it builds the entire function $\Lambda_0$ directly as the $(0,\infty)$-Mellin transform of $f_{\mathrm{modif}}$, proves $\Lambda_0(k-s)=\varepsilon\Lambda_0^{\mathrm{symm}}(s)$ on all of $\mathbb C$ by global $t\mapsto 1/t$ inversion, and only connects $\Lambda$ back to $\mathcal M(f-f_0)$ on $\Re s>k$ afterwards (`hasMellin`).

2. *Hurwitz's formula (1882) via parity decomposition.* Classically, Hurwitz `[Hurwitz1882]` (pp. 92–93; see `[OswaldSteuding2015]`) introduced the contour-integral functional equation of $\zeta(s,a)=\sum_{n=0}^\infty(n+a)^{-s}$ for **rational** parameters $a=k/m$ ($1\le k\le m$) in his study of Dirichlet series for binary quadratic forms; for general real shifts, the modern formula (`[DLMF 25.11.9]`) reads
$$
 \zeta(1-s,a)=\frac{2\,\Gamma(s)}{(2\pi)^s}\sum_{n=1}^\infty\frac{\cos\bigl(\frac{\pi s}{2}-2\pi n a\bigr)}{n^s}\qquad(\Re s>0\text{ for }0<a<1;\;\Re s>1\text{ for }a=1).
$$
David Loeffler's Mathlib formalization avoids Hankel contours altogether by splitting $\zeta(s,a)=E_a(s)+O_a(s)$ into its even and odd parts in $a\in\mathbb R/\mathbb Z$: Theorem 4 and Corollary 5(1) give $E_a(1-s)=\Gamma_{\mathbb C}(s)\cos(\pi s/2)Z_{\cos}(a,s)$ at weight $k=1/2$ with $(f_0,g_0)=(\delta_a,1)$, §1.3.2.1 gives $O_a(1-s)=\Gamma_{\mathbb C}(s)\sin(\pi s/2)Z_{\sin}(a,s)$ at weight $k=3/2$ with $(f_0,g_0)=(0,0)$, and `hurwitzZeta_one_sub` (`HurwitzZeta.lean:156–170`) adds the two and expands $\cos(\pi s/2)\cos(2\pi n a)+\sin(\pi s/2)\sin(2\pi n a)=\cos(\pi s/2-2\pi n a)$ into the exponential zeta functions $L(e^{\pm 2\pi i a\cdot},s)$. Notice also that Mathlib's $H_a=\text{`hurwitzZeta`}$ on $\mathbb R/\mathbb Z$ satisfies $H_0(s)=\zeta(s)$ (`hurwitzZeta_zero`, $a=0$ corresponds to classical $a=1$, where $\zeta(s,1)=\zeta(s)$, `[DLMF 25.11.3]`), whereas for $0<a<1$ it agrees with classical $\zeta(s,a)$ (`hasSum_nat_hurwitzZeta_of_mem_Ioc`). [DLMF 25.4.1–4](https://dlmf.nist.gov/25.4#E1) · [DLMF 25.5.13–14](https://dlmf.nist.gov/25.5#E13) · [DLMF 25.11.3, 25.11.9](https://dlmf.nist.gov/25.11#E9)

3. *Deligne's archimedean factors.* The notation $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$ and $\Gamma_{\mathbb C}(s)=2(2\pi)^{-s}\Gamma(s)$ in `Deligne.lean` follows Deligne `[Deligne1979]`, §5.3: the completed even Hurwitz function carries the factor $\Gamma_{\mathbb R}(s)$, the completed odd Hurwitz function (§1.3.2.1) carries $\Gamma_{\mathbb R}(s+1)$, and their product $\Gamma_{\mathbb R}(s)\Gamma_{\mathbb R}(s+1)=\Gamma_{\mathbb C}(s)$ (§1.2.2.5) is what turns division by $\Gamma_{\mathbb R}(1-s)$ into multiplication by $\Gamma_{\mathbb C}(s)\cos(\pi s/2)$ or $\Gamma_{\mathbb C}(s)\sin(\pi s/2)$.

4. *Where `ZMod.completedLFunction_one_sub_even` still uses the identity theorem.* Although `completedHurwitzZetaEven_one_sub` holds for *every* $s\in\mathbb C$, the finite discrete-Fourier combination for an even function $\Phi:\mathbb Z/N\mathbb Z\to\mathbb C$ in `ZMod.lean:409–505` first proves `completedLFunction_one_sub_of_one_lt_even` on $\Re s>1$ (applying `completedHurwitzZetaEven_one_sub` termwise at line 415 and identifying $\sum_x\Phi(x)Z_{\cos}(x/N,s)$ with $L(\widehat\Phi,s)$ via the Dirichlet series) and then extends to the connected open domain $U=\{s:(s\ne0\lor\sum\Phi=0)\land(s\ne1\lor\Phi(0)=0)\}$ by `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` around $s=2$. When $\chi$ is a primitive character of conductor $N>1$, both $\sum\chi=0$ and $\chi(0)=0$ hold, so $U=\mathbb C$ (`DirichletContinuation.lean:302`), while $N=1$ calls `completedRiemannZeta_one_sub` directly (`:289`).

**Source note.** The reading is R3 for `AbstractFuncEq.lean:80–138` (`WeakFEPair`, `IsStrongFEPair`, `h_feq'`, `symm`), `184–203` (`functional_equation_aux`), `247–316` (`f_modif`, `g_modif`, `hf_modif_int`, `hf_modif_FE`, `hf_modif_top`, `toStrongFEPair`, `isStrongFEPair_toStrongFEPair`), `376–388` (`Λ₀`, `Λ`, `Λ₀_eq`, `symm_Λ₀_eq`) and `420–429` (`functional_equation₀`, `functional_equation`); for `MellinTransform.lean:91–132` (`mellin`, `mellin_cpow_smul`, `mellin_const_smul`, `mellin_div_const`, `mellin_comp_rpow`) and `IntegralEqImproper.lean:1131–1143` (`integral_comp_rpow_Ioi`); for `HurwitzZetaEven.lean:102–105` (`evenKernel_eq_cosKernel_of_zero`), `254–392` (`hurwitzEvenFEPair`, `hurwitzEvenFEPair_zero_symm`, `hurwitzEvenFEPair_neg`, `completedHurwitzZetaEven`, `completedHurwitzZetaEven_eq`, `completedCosZeta`, `completedCosZeta_eq`, `completedHurwitzZetaEven_one_sub`, `completedHurwitzZetaEven₀_one_sub`, `completedCosZeta_one_sub`, `completedCosZeta₀_one_sub`), `488–526` (`hasSum_int_completedCosZeta`, `hasSum_nat_completedCosZeta`), `587–593` (`hurwitzZetaEven_def_of_ne_or_ne`), `697–753` (`cosZeta`, `cosZeta_apply_zero`, `cosZeta_neg_two_mul_nat_add_one`, `differentiableAt_cosZeta`, `differentiable_cosZeta_of_ne_zero`, `hasSum_int_cosZeta`, `hasSum_nat_cosZeta`, `LSeriesHasSum_cos`), and `760–783` (`hurwitzZetaEven_one_sub`, `cosZeta_one_sub`); for `RiemannZeta.lean:64–109, 121–128, 178–180`; and for the consumer bodies `HurwitzZeta.lean:156–191`, `HurwitzZetaValues.lean:124–143`, `ZMod.lean:409–425, 459–505`, `DirichletContinuation.lean:284–314`, and archive `RhOfRight.lean:1–62` and `ClaimStrip.lean:75–104`. Inherited from earlier sections are the theta-kernel bounds, Mellin convergence/differentiation criteria, `f_modif_aux1`/`f_modif_aux2`/`hasMellin`, and `hasSum_mellin_pi_mul_sq` (§1.2.2.1), `differentiableAt_update_of_residue` and `differentiable_Gammaℝ_inv` (§1.2.2.2), the stored value at $1$ (§1.2.2.3), `inv_Gammaℝ_one_sub` and the duplication formula (§1.2.2.5), the odd Hurwitz reflection (§1.3.2.1), and Euler's integral, recurrence, reflection, and improper-integral criteria for $\Gamma$ ([Chapter 2, §§2.3.2.1 and 2.3.2.3–2.3.2.4](02-functional-equations-and-primitive-characters.md#2321-why-gamma-has-no-zeros-in-the-right-half-plane)). The Gaussian Poisson summation theorem `Complex.tsum_exp_neg_quadratic` (`Gaussian/PoissonSummation.lean:87`) and `jacobiTheta₂_functional_equation` (`TwoVariable.lean:465`), retained at the boundary of this subsection, are read at R3 in §1.2.2.7; remaining named inputs here are the general measure-theoretic change-of-variables theorem `integral_image_eq_integral_abs_deriv_smul` (`IntegralEqImproper.lean:1137`), `isLittleO_exp_neg_mul_rpow_atTop`, `HasSum.nat_add_neg`, `summable_one_div_int_add_rpow`, `cosZeta_two_mul_nat'` (`HurwitzZetaValues.lean:79`), `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, and `Countable.isConnected_compl_of_one_lt_rank`; archive consumers outside `RhOfRight.lean` and `ClaimStrip.lean` are listed from a static grep without reading their dependency cones. Riemann's 1859 memoir was read in D. R. Wilkins's German transcription and English translation (pp. 2–3; original *Monatsberichte* pagination 671–680 cited bibliographically), alongside NIST DLMF §§25.4, 25.5, and 25.11; Hurwitz (1882, pp. 92–93) was checked via OCR and `[OswaldSteuding2015]`, and Deligne (1979) bibliographically. The [proof map](../notes/proof-map.md#p1-chapter-1-completed-hurwitz-functional-equation) records all pinned paths and lines. The two traps in the Example, the $a=1/6$ sharpness counterexample, hand calculations A and B, and the consumer table are ours; the exact rational checks and direct $(0,\infty)$ Mellin quadrature checks on the raw series `f_modif` and `g_modif` (`verify_ch01_poisson_fe.py`, cross-checked to 45 digits) are consistency checks, not formal proof certificates, and no Lean compilation was run.

#### 1.2.2.7 From Poisson summation to theta inversion

**Motivation.** Section 1.2.2.6 reduced the functional equation of $\zeta(s)$ and of the even Hurwitz family $E_a(s)$ to the conditional `WeakFEPair` interface, leaving a single analytic root input at the bottom of the Chapter 1 functional-equation chain: the pointwise kernel inversion
$$
 f_a(1/x)=x^{1/2}g_a(x)\qquad(a\in\mathbb R/\mathbb Z,\;x>0),
$$
supplied in Mathlib by Gaussian Poisson summation (`Complex.tsum_exp_neg_quadratic`) through the two-variable Jacobi theta transformation (`jacobiTheta₂_functional_equation`). Meanwhile, [Chapter 14, §§14.4.2–14.4.2.3](14-masullos-trace-formula-route.md#1442-poisson-summation-on-the-real-line-and-a-prime-power-toy-model) already read the top-level circle-Fourier assembly of `Real.fourierCoeff_tsum_comp_add` and `Real.tsum_eq_tsum_fourier`, together with the Stone–Weierstrass and $L^2(\mathbb R/\mathbb Z)$ density proofs behind `fourierBasis`, while retaining two direct analytic layers as named inputs:

1. *The periodization, coefficient-interchange, and decay-tier suppliers on $\mathbb R$*: how compact-translate norm summability produces a $1$-periodic continuous function in the compact-open topology, justifies swapping $\int_0^1$ with $\sum_{n\in\mathbb Z}$ and patching unit-interval translates into a whole-line Fourier integral, and splits into four distinct hypothesis tiers separating $L^2$ completeness from unordered pointwise reconstruction.
2. *The complex Gaussian and theta-specialization suppliers*: how the polar-coordinate value $\int_{\mathbb R}e^{-bx^2}\,dx=\sqrt{\pi/b}$ ($b>0$, which also closes `Gamma_one_half_eq` retained in §§1.2.2.2–1.2.2.5) extends holomorphically to $\Re b>0$ with its principal square-root branch, shifts across horizontal strips by a rectangular Cauchy contour to give $\mathcal F(e^{-\pi a x^2+2\pi b x})$, and feeds both a direct scaled-Gaussian argument and Mathlib's `jacobiTheta₂` wrapper to inhabit the exact same `h_feq` field of `hurwitzEvenFEPair a`.

Opening those two layers — without repeating the Gamma chain of §§1.2.2.3–1.2.2.5, the Mellin `WeakFEPair` algebra of §1.2.2.6, or the circle Stone–Weierstrass/$L^2$ density proofs of §§14.4.2.1–14.4.2.3 — completes the Chapter 1 functional-equation spine down to standard multivariable/contour calculus and dominated convergence.

**Examples (why $L^2$ Fourier series do not evaluate lattice sums, and why scale, phase, and branch all matter).** Two elementary tests pinpoint what the hypotheses of Poisson summation and complex Gaussian inversion must control.

1. *Lattice sampling sees measure-zero sets and unordered summability.* Changing a function $f\in L^1(\mathbb R)$ at the integers $n\in\mathbb Z$ leaves its Fourier transform $\mathcal F f(\xi)=\int_{\mathbb R}e^{-2\pi i x\xi}f(x)\,dx$ and the $L^2(\mathbb R/\mathbb Z)$ class of its periodization $P_f(x)=\sum_{n\in\mathbb Z}f(x+n)$ completely unchanged, yet alters $\sum_{n\in\mathbb Z}f(n)$ arbitrarily. Even when $f\in C_c(\mathbb R)$ is continuous and compactly supported — so $P_f$ is continuous and finite-summed — $L^2(\mathbb R/\mathbb Z)$ convergence of its Fourier series does not force $\mathcal F f\in\ell^1(\mathbb Z)$. In Mathlib, infinite sums over $\mathbb Z$ are unordered `tsum`s (`∑'`), which return `0` whenever a series is not absolutely summable; hence unordered $\ell^1(\mathbb Z)$ summability of $m\mapsto\mathcal F f(m)$ is the exact bridge from $L^2(\mathbb R/\mathbb Z)$ completeness to a non-vacuous Lean identity $\sum_{n\in\mathbb Z}f(x+n)=\sum_{m\in\mathbb Z}e^{2\pi i m x}\mathcal F f(m)$.
2. *Scaling vs. twisting, and the square-root branch on $\Re a>0$.* On the real Gaussian $h_t(u)=e^{-\pi t u^2}$ ($t>0$), spatial dilation $u\mapsto\sqrt{t}\,u$ stretches frequency by $1/\sqrt{t}$ and divides amplitude by $\sqrt{t}$, giving $\mathcal F h_t(\xi)=t^{-1/2}e^{-\pi\xi^2/t}$. Translating in space by $a\in\mathbb R$ multiplies $\mathcal F$ by the linear phase $e^{2\pi i a\xi}$, whereas twisting in space by $e^{2\pi i r u}$ shifts the dual lattice from $m$ to $m-r$. In Jacobi's two-variable theta function $\Theta(z,\tau)=\sum_{n\in\mathbb Z}e^{2\pi i n z+\pi i n^2\tau}$ ($\Im\tau>0$), the quadratic parameter is $a=-i\tau$ with $\Re a=\Im\tau>0$: the prefactor $a^{-1/2}=(-i\tau)^{-1/2}$ is no longer a positive real root unless $\tau=it$, and selecting the wrong sign branch on the right half-plane would flip the root number $\varepsilon=+1$ of `hurwitzEvenFEPair` to $-1$.

**Definitions (Fourier normalization, continuous periodization, four Poisson tiers, and Jacobi–Hurwitz kernels).** For $f:\mathbb R\to\mathbb C$ and $\xi\in\mathbb R$, Mathlib's scalar Fourier integral (`Real.fourierIntegral_eq`, specializing `VectorFourier.fourierIntegral`) is
$$
 \mathcal F f(\xi)=\int_{\mathbb R}e^{-2\pi i x\xi}f(x)\,dx.
$$
Given $f\in C(\mathbb R,\mathbb C)$, its *formal unit-periodization* in the topological group $C(\mathbb R,\mathbb C)$ (equipped with the compact-open topology) is $P_f=\sum_{n\in\mathbb Z}\tau_n f$, where $(\tau_n f)(x)=f(x+n)$. On $\mathbb C$, write $w^{1/2}=\exp\bigl(\tfrac12\log w\bigr)$ for the principal complex power (`cpow`), where $\Im\log w=\arg w\in(-\pi,\pi]$; on the open right half-plane $\mathbb H_{\mathrm{right}}=\{a\in\mathbb C:\Re a>0\}$, $\arg a\in(-\pi/2,\pi/2)$ and $\Re(a^{1/2})>0$.

We distinguish the **four hypothesis tiers** of one-dimensional Poisson summation formalized in `Mathlib/Analysis/Fourier/PoissonSummation.lean`:

- **Tier I (compact-translate norm summability + $\ell^1$ Fourier samples, `Real.tsum_eq_tsum_fourier`).** $f\in C(\mathbb R,\mathbb C)$, for every compact $K\subset\mathbb R$ one has $\sum_{n\in\mathbb Z}\sup_{x\in K}\lvert f(x+n)\rvert<\infty$ (`h_norm`), and $\sum_{m\in\mathbb Z}\lvert\mathcal F f(m)\rvert<\infty$ (`hFf`).
- **Tier II (one-sided power decay + $\ell^1$ Fourier samples, `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`).** $f\in C(\mathbb R,\mathbb C)$, there exists $b>1$ such that $f(x)=O(\lvert x\rvert^{-b})$ as $\lvert x\rvert\to\infty$ (`hf`), and $\sum_{m\in\mathbb Z}\lvert\mathcal F f(m)\rvert<\infty$ (`hFf`).
- **Tier III (two-sided power decay, Stein–Weiss criterion, `Real.tsum_eq_tsum_fourier_of_rpow_decay`).** $f\in C(\mathbb R,\mathbb C)$ and there exists $b>1$ such that $f(x)=O(\lvert x\rvert^{-b})$ as $\lvert x\rvert\to\infty$ (`hf`) and $\mathcal F f(\xi)=O(\lvert\xi\rvert^{-b})$ as $\lvert\xi\rvert\to\infty$ (`hFf`).
- **Tier IV (Schwartz class, `SchwartzMap.tsum_eq_tsum_fourier`).** $f\in\mathcal S(\mathbb R,\mathbb C)$, i.e. $f\in C^\infty(\mathbb R,\mathbb C)$ and $\sup_{x\in\mathbb R}\lvert x\rvert^k\lvert f^{(j)}(x)\rvert<\infty$ for all $k,j\in\mathbb N$.

For $(z,\tau)\in\mathbb C^2$, Mathlib's two-variable theta series (`jacobiTheta₂`, classical $\theta_3(\pi z\mid\tau)$ in `[DLMF 20.2.3]`) and even Hurwitz kernels (`evenKernel`, `cosKernel` for $a\in\mathbb R/\mathbb Z$ and $x\in\mathbb R$, choosing any representative $a\in\mathbb R$) are
$$
 \Theta(z,\tau)=\sum_{n\in\mathbb Z}\exp\bigl(2\pi i n z+\pi i n^2\tau\bigr),
$$
$$
 f_a(x)=\mathbf 1_{(0,\infty)}(x)\,\Re\bigl(e^{-\pi a^2 x}\Theta(aix,ix)\bigr),\qquad
 g_a(x)=\mathbf 1_{(0,\infty)}(x)\,\Re\bigl(\Theta(a,ix)\bigr).
$$
For $x>0$, $2\pi i n(aix)+\pi i n^2(ix)-\pi a^2 x=-\pi(n+a)^2 x$ is real and $\Re(e^{2\pi i n a}e^{-\pi n^2 x})$ pairs $\pm n$, matching the real sums of §1.2.2.1 while vanishing identically for $x\le0$. [Lean, read] [FourierTransform.lean:480–489](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/FourierTransform.lean#L480-L489) · [Analysis/Fourier/PoissonSummation.lean:103–226](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/PoissonSummation.lean#L103-L226) · [TwoVariable.lean:78–80](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean#L78-L80) · [HurwitzZetaEven.lean:65–100](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L65-L100)

**Lemma 1 (compact-open periodization, whole-line $L^1$ patching, and the four-tier Poisson hierarchy).** Let $f:\mathbb R\to\mathbb C$.

1. *Periodization and unit-interval interchange.* Assume $f\in C(\mathbb R,\mathbb C)$ satisfies `h_norm`: for every compact $K\subset\mathbb R$, $\sum_{n\in\mathbb Z}\sup_{x\in K}\lvert f(x+n)\rvert<\infty$. Then:
   - the series $P_f=\sum_{n\in\mathbb Z}\tau_n f$ converges unconditionally in $C(\mathbb R,\mathbb C)$ with $P_f(x)=\sum_{n\in\mathbb Z}f(x+n)$ for every $x\in\mathbb R$, and $P_f(x+1)=P_f(x)$ (descending to $\widetilde P_f\in C(\mathbb R/\mathbb Z,\mathbb C)$);
   - $f\in L^1(\mathbb R)$, and for every $m\in\mathbb Z$,
     $$
      \widehat{\widetilde P_f}(m)=\int_0^1 e^{-2\pi i m x}\Bigl(\sum_{n\in\mathbb Z}f(x+n)\Bigr)\,dx=\mathcal F f(m).
     $$
2. *Implications IV $\Rightarrow$ III $\Rightarrow$ II $\Rightarrow$ I and reconstruction.* Every Schwartz function lies in Tier III (with exponent $b=2$); Tier III implies Tier II; Tier II implies Tier I. Under Tier I (hence under Tiers II, III, and IV), for every $x\in\mathbb R$ both series below are absolutely summable and satisfy
$$
 \sum_{n\in\mathbb Z}f(x+n)=\sum_{m\in\mathbb Z}e^{2\pi i m x}\mathcal F f(m),
$$
with uniform convergence in $x$ on every compact subset of $\mathbb R$.

**Proof.** (1) For each compact $K\subset\mathbb R$, restricting $\tau_n f$ to $K$ gives elements of the Banach space $C(K,\mathbb C)$ with $\lVert(\tau_n f)\rvert_K\rVert_\infty=\sup_{x\in K}\lvert f(x+n)\rvert$. By `h_norm` and the Weierstrass $M$-test (`summable_of_norm_bounded`), the restricted series converges unconditionally in $C(K,\mathbb C)$ for every compact $K$, which is convergence in the compact-open topology on $C(\mathbb R,\mathbb C)$ (`ContinuousMap.summable_of_locally_summable_norm`), with pointwise evaluation $P_f(x)=\sum_{n\in\mathbb Z}f(x+n)$ (`ContinuousMap.tsum_apply`). Reindexing $n\mapsto n+1$ along the bijection $\mathbb Z\to\mathbb Z$ yields $P_f(x+1)=\sum_{n\in\mathbb Z}f((x+1)+n)=\sum_{n\in\mathbb Z}f(x+(n+1))=P_f(x)$ (`ContinuousMap.periodic_tsum_comp_add_zsmul`, which also holds when the series is non-summable because Lean sets both `tsum`s to $0$).

Now specialize $K=[0,1]$. Setting $M_n=\sup_{x\in[0,1]}\lvert f(x+n)\rvert$, we have $\sum_{n\in\mathbb Z}M_n<\infty$. Because $\mathbb R=\bigcup_{n\in\mathbb Z}[n,n+1]$ and $\int_n^{n+1}\lvert f(y)\rvert\,dy=\int_0^1\lvert f(x+n)\rvert\,dx\le M_n\cdot 1$, the norms of $f\mathbf 1_{[n,n+1]}$ are summable, so $f\in L^1(\mathbb R)$ (`Real.integrable_of_summable_norm_Icc`). Fix $m\in\mathbb Z$ and set $g_m(y)=e^{-2\pi i m y}f(y)$. Since $\lvert e^{-2\pi i m x}\rvert=1$, we have $\lvert e^{-2\pi i m x}f(x+n)\rvert\le M_n$ on $[0,1]$, so dominated convergence for series on $(0,1]$ (`tsum_intervalIntegral_eq_of_summable_norm`) swaps $\int_0^1$ and $\sum_{n\in\mathbb Z}$:
$$
 \int_0^1 e^{-2\pi i m x}P_f(x)\,dx=\sum_{n\in\mathbb Z}\int_0^1 e^{-2\pi i m x}f(x+n)\,dx.
$$
Using $1$-periodicity $e^{-2\pi i m(x+n)}=e^{-2\pi i m x}$ and translation $y=x+n$, the $n$-th integral is $\int_n^{n+1}g_m(y)\,dy$. Because $g_m\in L^1(\mathbb R)$ and the half-open intervals $(n,n+1]$ ($n\in\mathbb Z$) partition $\mathbb R$ disjointly (`iUnion_Ioc_add_intCast`, `pairwise_disjoint_Ioc_add_intCast`), countable additivity of the Bochner integral (`Integrable.hasSum_intervalIntegral_comp_add_int`) sums those pieces to $\int_{\mathbb R}g_m(y)\,dy=\mathcal F f(m)$.

(2) *IV $\Rightarrow$ III:* If $f\in\mathcal S(\mathbb R,\mathbb C)$, then $\sup_{x\in\mathbb R}(1+\lvert x\rvert)^2\lvert f(x)\rvert<\infty$ from the $k=0,1,2$ seminorms (`SchwartzMap.isBigO_cocompact_rpow` at $-2$), so $f(x)=O(\lvert x\rvert^{-2})$ as $\lvert x\rvert\to\infty$; since $\mathcal F$ maps $\mathcal S(\mathbb R,\mathbb C)$ into itself (`SchwartzMap.fourierTransformCLM`), $\mathcal F f(\xi)=O(\lvert\xi\rvert^{-2})$ as well.

*III $\Rightarrow$ II:* If $\mathcal F f(\xi)=O(\lvert\xi\rvert^{-b})$ with $b>1$, comparing at nonzero integers with the convergent $p$-series $\sum_{m\ne0}\lvert m\rvert^{-b}<\infty$ (`Real.summable_abs_int_rpow`) gives $\sum_{m\in\mathbb Z}\lvert\mathcal F f(m)\rvert<\infty$.

*II $\Rightarrow$ I:* Suppose $f\in C(\mathbb R,\mathbb C)$ satisfies $\lvert f(y)\rvert\le C\lvert y\rvert^{-b}$ for $\lvert y\rvert\ge R_0$, with $b>1$. Given any compact $K\subset\mathbb R$, choose $r\ge0$ with $K\subset[-r,r]$. For every real $x>\max(2R_0,2r)$ and every $t\in[-r,r]$, we have $x+t\ge x-r>x/2>\max(R_0,0)$; since $b>0$ makes $u\mapsto u^{-b}$ decreasing on $(0,\infty)$,
$$
 \sup_{t\in K}\lvert f(t+x)\rvert\le\sup_{y\in[x-r,x+r]}C y^{-b}=C(x-r)^{-b}\le C\Bigl(\frac{x}{2}\Bigr)^{-b}=2^b C\,x^{-b}
$$
(`isBigO_norm_Icc_restrict_atTop`). Applying the same estimate to $y\mapsto f(-y)$ covers $x<-\max(2R_0,2r)$ (`_atBot`), so $\sup_{t\in K}\lvert f(t+n)\rvert=O(\lvert n\rvert^{-b})$ as $\lvert n\rvert\to\infty$ (`isBigO_norm_restrict_cocompact`), which is summable over $n\in\mathbb Z$ since $b>1$.

*Tier I reconstruction:* The abstract Hilbert step is proved in [§1.2.2.8](#1228-hilbert-expansion-and-the-norm-behind-poisson-summation). As read in [Chapter 14, §§14.4.2.1–14.4.2.3](14-masullos-trace-formula-route.md#14421-fourier-completeness-on-the-circle-and-pointwise-reconstruction), the characters $e_m(x)=e^{2\pi i m x}$ form a Hilbert basis `fourierBasis` of $L^2(\mathbb R/\mathbb Z)$ (`HilbertBasis.mk` and `HilbertBasis.hasSum_repr` in `l2Space.lean:446–448, 539–553`), so $\widetilde P_f\in C(\mathbb R/\mathbb Z)\subset L^2(\mathbb R/\mathbb Z)$ has $L^2$-convergent expansion $\sum_{m\in\mathbb Z}\widehat{\widetilde P_f}(m)e_m$. Under `hFf` ($\sum_m\lvert\mathcal F f(m)\rvert<\infty$), part (1) gives $\sum_m\lvert\widehat{\widetilde P_f}(m)\rvert<\infty$, so `hasSum_fourier_series_of_summable` (`AddCircle.lean:485–506`) upgrades $L^2$ convergence to uniform convergence in $C(\mathbb R/\mathbb Z,\mathbb C)$ and everywhere pointwise equality $\widetilde P_f(x)=\sum_{m\in\mathbb Z}\mathcal F f(m)e^{2\pi i m x}$. Evaluating at the quotient class of $x\in\mathbb R$ gives Tier I (`Analysis/Fourier/PoissonSummation.lean:106–117`). $\square$

[Lean, read] [Compact.lean:456–474](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/Compact.lean#L456-L474) · [Periodic.lean:30–45](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/Periodic.lean#L30-L45) · [DominatedConvergence.lean:219–242](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean#L219-L242) · [Lebesgue/Integral.lean:52–67](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean#L52-L67) · [IntervalIntegral/Basic.lean:1457–1469](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean#L1457-L1469) · [Analysis/Fourier/PoissonSummation.lean:52–226](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/PoissonSummation.lean#L52-L226) · [SchwartzSpace/Basic.lean:151–163](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean#L151-L163) · [SchwartzSpace/Fourier.lean:51–103](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean#L51-L103) · [l2Space.lean:446–553](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L446-L553)

**Lemma 2 (complex Gaussian integral, principal-branch selection, and contour-shifted Fourier transform).** Let $b\in\mathbb C$ satisfy $\Re b>0$.

1. *Complex Gaussian integral and $\Gamma(1/2)$ (`integral_gaussian`, `integral_gaussian_complex`, `Gamma_one_half_eq`).* For real $b>0$, $\int_{\mathbb R}e^{-b x^2}\,dx=\sqrt{\pi/b}$ (yielding $\Gamma(1/2)=\sqrt\pi$ upon substituting $t=x^2$ at $b=1$). For every $b\in\mathbb H_{\mathrm{right}}=\{z\in\mathbb C:\Re z>0\}$, the principal-branch power $(\pi/b)^{1/2}$ is selected uniquely:
$$
 I(b)=\int_{\mathbb R}e^{-b x^2}\,dx=\Bigl(\frac{\pi}{b}\Bigr)^{1/2}.
$$
2. *Rectangular Cauchy contour shift and quadratic Fourier transform (`integral_cexp_neg_mul_sq_add_real_mul_I`, `integral_cexp_quadratic`, `fourier_gaussian_pi'`).* For every $\Re b>0$ and $c,d\in\mathbb C$,
$$
 \int_{\mathbb R}e^{-b(x+c)^2}\,dx=\Bigl(\frac{\pi}{b}\Bigr)^{1/2},\qquad
 \int_{\mathbb R}e^{-b x^2+c x+d}\,dx=\Bigl(\frac{\pi}{b}\Bigr)^{1/2}\exp\Bigl(\frac{c^2}{4b}+d\Bigr).
$$
Consequently, for every $a\in\mathbb H_{\mathrm{right}}$, $b\in\mathbb C$, and $\xi\in\mathbb R$, the function $f_{a,b}(x)=e^{-\pi a x^2+2\pi b x}$ has Fourier transform
$$
 \mathcal F f_{a,b}(\xi)=\frac{1}{a^{1/2}}\exp\Bigl(\frac{\pi(b-i\xi)^2}{a}\Bigr).
$$

**Proof.** (1) First take real $b>0$. By Fubini's theorem (`integral_prod_mul`) and the polar-coordinate change of variables $(x,y)=(r\cos\theta,r\sin\theta)$ on $(0,\infty)\times(-\pi,\pi)$ (`integral_comp_polarCoord_symm`, `setIntegral_prod_mul`),
$$
 \Bigl(\int_{\mathbb R}e^{-b x^2}\,dx\Bigr)^2=\iint_{\mathbb R^2}e^{-b(x^2+y^2)}\,dx\,dy
 =\Bigl(\int_{-\pi}^{\pi}d\theta\Bigr)\Bigl(\int_0^\infty r e^{-b r^2}\,dr\Bigr)=2\pi\cdot\frac{1}{2b}=\frac{\pi}{b},
$$
where $-\frac{1}{2b}e^{-b r^2}$ is an explicit primitive of $r e^{-b r^2}$ on $(0,\infty)$ vanishing at $\infty$ (`integral_mul_cexp_neg_mul_sq`). Positivity of $e^{-b x^2}$ forces $\int_{\mathbb R}e^{-b x^2}\,dx>0$, giving $\sqrt{\pi/b}$ (`integral_gaussian`; at $b=1$, splitting $\mathbb R$ at $0$ and changing variables $t=x^2$ gives $\Gamma(1/2)=2\int_0^\infty e^{-x^2}\,dx=\sqrt\pi$, closing `Real.Gamma_one_half_eq` and `Complex.Gamma_one_half_eq` at `GaussianIntegral.lean:307–326`).

Now let $b$ vary in the convex open half-plane $\mathbb H_{\mathrm{right}}=\{\Re z>0\}$. On any open disk $D(b_0,\tfrac12\Re b_0)\subset\mathbb H_{\mathrm{right}}$, $\lvert e^{-z x^2}\rvert=e^{-(\Re z)x^2}\le e^{-\frac12(\Re b_0)x^2}$ and $\lvert -x^2 e^{-z x^2}\rvert\le x^2 e^{-\frac12(\Re b_0)x^2}$, both integrable on $\mathbb R$. Dominated differentiation under the integral sign gives $I'(b)=-\int_{\mathbb R}x^2 e^{-b x^2}\,dx$. Integrating by parts on $[-T,T]$ with $u(x)=x$ and $v'(x)=x e^{-b x^2}=\frac{d}{dx}\bigl(-\frac{1}{2b}e^{-b x^2}\bigr)$ gives
$$
 \int_{-T}^{T}x^2 e^{-b x^2}\,dx=\Bigl[-\frac{x}{2b}e^{-b x^2}\Bigr]_{-T}^{T}+\frac{1}{2b}\int_{-T}^{T}e^{-b x^2}\,dx
 =-\frac{T}{b}e^{-b T^2}+\frac{1}{2b}\int_{-T}^{T}e^{-b x^2}\,dx.
$$
Since $\lvert T e^{-b T^2}\rvert=T e^{-(\Re b)T^2}\to0$ as $T\to\infty$, letting $T\to\infty$ yields the first-order differential equation $I'(b)=-\frac{1}{2b}I(b)$. On $\mathbb H_{\mathrm{right}}$, the principal branch $b^{1/2}$ is holomorphic with $(b^{1/2})'=\frac12 b^{-1/2}$ (since $b\notin(-\infty,0]$), so the product rule gives
$$
 \frac{d}{db}\bigl(b^{1/2}I(b)\bigr)=\tfrac12 b^{-1/2}I(b)+b^{1/2}\Bigl(-\frac{1}{2b}I(b)\Bigr)=0.
$$
Because $\mathbb H_{\mathrm{right}}$ is convex, hence preconnected, $b^{1/2}I(b)$ is constant and equals its value at $b=1$: $1^{1/2}I(1)=\pi^{1/2}$. Thus $I(b)=b^{-1/2}\pi^{1/2}$. Finally, both $b\mapsto b^{-1/2}\pi^{1/2}$ and $b\mapsto(\pi/b)^{1/2}$ are continuous on the preconnected set $\mathbb H_{\mathrm{right}}$, have the same square $\pi/b$, and agree at $b=1$ (where $\pi^{1/2}\ne0$); by `IsPreconnected.eq_of_sq_eq`, they coincide everywhere on $\mathbb H_{\mathrm{right}}$, giving $I(b)=(\pi/b)^{1/2}$.

(2) Write $c=c_1+i c_2$ with $c_1,c_2\in\mathbb R$. Real translation invariance (`integral_add_right_eq_self`) reduces $\int_{\mathbb R}e^{-b(x+c_1+i c_2)^2}\,dx$ to $\int_{\mathbb R}e^{-b(x+i c_2)^2}\,dx$. The integrand $g(z)=e^{-b z^2}$ is entire, so Cauchy's theorem on the rectangle $[-T,T]\times[0,c_2]$ (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) reads
$$
 \int_{-T}^{T}e^{-b x^2}\,dx-\int_{-T}^{T}e^{-b(x+i c_2)^2}\,dx
 =i\int_0^{c_2}e^{-b(-T+i y)^2}\,dy-i\int_0^{c_2}e^{-b(T+i y)^2}\,dy.
$$
On the vertical sides $z=\pm T+i y$ with $\lvert y\rvert\le\lvert c_2\rvert$, expanding $z^2=T^2-y^2\pm 2i T y$ gives
$$
 \Re(-b z^2)=-(\Re b)(T^2-y^2)+2(\Im b)(\pm T)y\le-(\Re b)T^2+2\lvert\Im b\rvert\lvert c_2\rvert T+(\Re b)c_2^2,
$$
so each vertical integral is bounded in norm by $\lvert c_2\rvert\exp\bigl(-(\Re b)T^2+2\lvert\Im b\rvert\lvert c_2\rvert T+(\Re b)c_2^2\bigr)$ (`norm_verticalIntegral_le`), which tends to $0$ as $T\to\infty$ because $\Re b>0$ makes the quadratic $-(\Re b)T^2$ dominate the linear cross-term $2\lvert\Im b\rvert\lvert c_2\rvert T$ (`tendsto_verticalIntegral`). Passing to $T\to\infty$ yields $\int_{\mathbb R}e^{-b(x+i c_2)^2}\,dx=I(b)=(\pi/b)^{1/2}$. Completing the square $-b x^2+c x+d=-b\bigl(x-\frac{c}{2b}\bigr)^2+\frac{c^2}{4b}+d$ then gives `integral_cexp_quadratic`. Setting $(-b,c,d)=(-\pi a,2\pi(b-i\xi),0)$ evaluates $\mathcal F f_{a,b}(\xi)$ to $(\pi/(\pi a))^{1/2}e^{\pi(b-i\xi)^2/a}=(a^{-1})^{1/2}e^{\pi(b-i\xi)^2/a}$; since $\Re a>0$ implies $\arg a\in(-\pi/2,\pi/2)$ and in particular $\arg a\ne\pi$, `Complex.inv_cpow` rewrites $(a^{-1})^{1/2}=1/a^{1/2}$. $\square$

[Lean, read] [GaussianIntegral.lean:159–274](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean#L159-L274) · [GaussianIntegral.lean:307–326](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean#L307-L326) · [Gaussian/FourierTransform.lean:49–225](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean#L49-L225)

**Theorem 3 (Gaussian Poisson summation, Jacobi theta inversion, and the two equivalent bridges to `hurwitzEvenFEPair`).**

1. *Quadratic Gaussian Poisson summation (`Complex.tsum_exp_neg_quadratic`).* For every $a\in\mathbb C$ with $\Re a>0$ and every $b\in\mathbb C$, both series below are unordered-summable over $\mathbb Z$ and satisfy
$$
 \sum_{n\in\mathbb Z}\exp\bigl(-\pi a n^2+2\pi b n\bigr)=\frac{1}{a^{1/2}}\sum_{m\in\mathbb Z}\exp\Bigl(\frac{\pi(b+i m)^2}{a}\Bigr).
$$
2. *Two-variable Jacobi theta inversion (`jacobiTheta₂_functional_equation`).* For *every* $(z,\tau)\in\mathbb C^2$ (including $\Im\tau\le0$ under Lean's total `tsum` convention),
$$
 \Theta(z,\tau)=\frac{1}{(-i\tau)^{1/2}}\exp\Bigl(-\frac{\pi i z^2}{\tau}\Bigr)\Theta\Bigl(\frac{z}{\tau},-\frac{1}{\tau}\Bigr).
$$
3. *Supplying `(hurwitzEvenFEPair a).h_feq` directly vs. via `jacobiTheta₂`.* Fix $a\in\mathbb R/\mathbb Z$ (with any real representative $a\in\mathbb R$). For every $x\in\mathbb R$, `evenKernel_functional_equation` states
$$
 f_a(x)=x^{-1/2}g_a(1/x),
$$
and for every $x>0$, $f_a(1/x)=x^{1/2}g_a(x)$, supplying the exact `h_feq` field (`k = 1/2`, `ε = 1`) of `hurwitzEvenFEPair a` consumed in §1.2.2.6, Theorem 4. Moreover, applying Lemma 1(2) directly to the scaled-and-shifted real Gaussian $\phi_{t,a}(u)=e^{-\pi t(u+a)^2}$ ($t=1/x>0$) and routing through part (2) at $(z,\tau)=(ai/x,i/x)$ invoke part (1) at the **identical** quadratic parameters $(1/x,-a/x)$ up to a cancelling real Gaussian factor $e^{-\pi a^2/x}$.

**Proof.** (1) Fix $a\in\mathbb H_{\mathrm{right}}$ and $b\in\mathbb C$, and set $f(u)=e^{-\pi a u^2+2\pi b u}$ for $u\in\mathbb R$. First check rapid power decay (`cexp_neg_quadratic_isLittleO_abs_rpow_cocompact`). Set $\alpha=-\pi\Re a<0$ and $\beta=2\pi\Re b$. For $u\ge\max\bigl(1,\frac{2\lvert\beta\rvert}{\lvert\alpha\rvert}\bigr)$, we have $\alpha u+\beta\le\frac12\alpha<0$ and $u\ge1$, whence
$$
 \Re(-\pi a u^2+2\pi b u)=u(\alpha u+\beta)\le\tfrac12\alpha u^2\le\tfrac12\alpha u.
$$
Hence $\lvert f(u)\rvert\le e^{-\frac12\lvert\alpha\rvert u}=o(u^r)$ as $u\to+\infty$ for every $r\in\mathbb R$ (`isLittleO_exp_neg_mul_rpow_atTop`). Replacing $u$ by $-u$ (which sends $b\mapsto-b$ while keeping $\alpha<0$) gives the same estimate as $u\to-\infty$; in particular $f(u)=O(\lvert u\rvert^{-2})$ as $\lvert u\rvert\to\infty$.

Next, by Lemma 2(2),
$$
 \mathcal F f(\xi)=\frac{1}{a^{1/2}}\exp\Bigl(\frac{\pi(b-i\xi)^2}{a}\Bigr)
 =\frac{e^{\pi b^2/a}}{a^{1/2}}\exp\Bigl(-\frac{\pi}{a}\xi^2-\frac{2\pi i b}{a}\xi\Bigr).
$$
Because $\Re(1/a)=\frac{\Re a}{\lvert a\rvert^2}>0$, the quadratic coefficient $-\pi/a$ again has strictly negative real part $-\frac{\pi\Re a}{\lvert a\rvert^2}<0$. Applying the same quadratic decay estimate to $\xi\mapsto\exp\bigl(-(\pi/a)\xi^2-(2\pi i b/a)\xi\bigr)$ gives $\mathcal F f(\xi)=O(\lvert\xi\rvert^{-2})$ as $\lvert\xi\rvert\to\infty$. Notice that Mathlib invokes **Tier III** of Lemma 1(2) at $b_{\mathrm{decay}}=2$ and $x=0$ (`Real.tsum_eq_tsum_fourier_of_rpow_decay`), avoiding constructing all Schwartz derivative seminorms! Evaluating Tier III at $x=0$ and reindexing $m\mapsto-m$ (`Equiv.neg ℤ`) yields
$$
 \sum_{n\in\mathbb Z}e^{-\pi a n^2+2\pi b n}=\sum_{m\in\mathbb Z}\mathcal F f(m)
 =\frac{1}{a^{1/2}}\sum_{m\in\mathbb Z}\exp\Bigl(\frac{\pi(b-i m)^2}{a}\Bigr)
 =\frac{1}{a^{1/2}}\sum_{m\in\mathbb Z}\exp\Bigl(\frac{\pi(b+i m)^2}{a}\Bigr).
$$

(2) Split on whether $\Im\tau>0$.
- *Case $\Im\tau\le0$ (`jacobiTheta₂_undef`).* For any $(w,\sigma)$ with $\Im\sigma\le0$, we have $-\pi n^2\Im\sigma\ge0$ for all $n\in\mathbb Z$. If $\Im w\le0$, then for $n\ge0$, $\lvert e^{2\pi i n w+\pi i n^2\sigma}\rvert=e^{-2\pi n\Im w-\pi n^2\Im\sigma}\ge1$; if $\Im w>0$, then for $n\le0$, $-2\pi n\Im w\ge0$ again gives modulus $\ge1$. In both subcases the general term fails to tend to $0$, so the series is not summable and Lean's `tsum` returns $\Theta(w,\sigma)=0$. Since $\Im\tau\le0$ also implies $\Im(-1/\tau)=\frac{\Im\tau}{\lvert\tau\rvert^2}\le0$ (including $\tau=0$, where $-1/0=0$), both $\Theta(z,\tau)$ and $\Theta(z/\tau,-1/\tau)$ equal $0$, and (2) holds as $0=0$.
- *Case $\Im\tau>0$.* Then $a=-i\tau$ satisfies $\Re a=\Im\tau>0$, and $\tau=i a\ne0$. Applying part (1) with $(a,b)=(-i\tau,iz)$ gives $-a\pi n^2+2\pi b n=\pi i n^2\tau+2\pi i n z$, while on the right
$$
 \frac{\pi(i z+i m)^2}{-i\tau}=-\frac{\pi(z+m)^2}{-i\tau}=-\frac{\pi i(z+m)^2}{\tau}
 =-\frac{\pi i z^2}{\tau}+2\pi i m\Bigl(\frac{z}{\tau}\Bigr)+\pi i m^2\Bigl(-\frac{1}{\tau}\Bigr).
$$
Pulling the $m$-independent factor $e^{-\pi i z^2/\tau}$ out of the summable `tsum` gives (2).

(3) *Route 1 (Mathlib's `jacobiTheta₂` production).* If $x\le0$, then $1/x\le0$, so $f_a(x)=0$ and $g_a(1/x)=0$ by definition (`HurwitzZetaEven.lean:135–138`), giving $0=x^{-1/2}\cdot0$. Now let $x>0$ and substitute $(z,\tau)=(aix,ix)$ into part (2). Since $\Im(ix)=x>0$, we have $-i\tau=x>0$ (so $(-i\tau)^{1/2}=x^{1/2}>0$ is positive real), $z/\tau=(aix)/(ix)=a$, $-1/\tau=-1/(ix)=i/x$, and
$$
 -\frac{\pi i z^2}{\tau}=-\frac{\pi i(aix)^2}{ix}=-\frac{\pi i(-a^2 x^2)}{ix}=+\pi a^2 x.
$$
Multiplying both sides of (2) by $e^{-\pi a^2 x}$ cancels $e^{-\pi a^2 x}\cdot e^{+\pi a^2 x}=1$:
$$
 e^{-\pi a^2 x}\Theta(aix,ix)=x^{-1/2}\Theta(a,i/x).
$$
Taking real parts (`Complex.re`) commutes with multiplication by the real scalar $x^{-1/2}$ and yields $f_a(x)=x^{-1/2}g_a(1/x)$ (`evenKernel_functional_equation`). At `HurwitzZetaEven.lean:276`, evaluating this identity at $1/x$ ($x>0$) and rewriting $(1/x)^{-1/2}=x^{1/2}$ (`Real.inv_rpow hx.le`) gives $f_a(1/x)=x^{1/2}g_a(x)$, which is literally `(hurwitzEvenFEPair a).h_feq`.

*Route 2 (direct scaled-and-shifted Gaussian).* For $t>0$ and $a\in\mathbb R$, consider $\phi_{t,a}(u)=e^{-\pi t(u+a)^2}=e^{-\pi a^2 t}f_{t,-at}(u)$ on $\mathbb R$. By real translation $y=u+a$ and Lemma 2(2) at $(t,0)$,
$$
 \mathcal F\phi_{t,a}(\xi)=\int_{\mathbb R}e^{-2\pi i u\xi}e^{-\pi t(u+a)^2}\,du
 =e^{2\pi i a\xi}\int_{\mathbb R}e^{-2\pi i y\xi}e^{-\pi t y^2}\,dy
 =e^{2\pi i a\xi}\,t^{-1/2}e^{-\pi\xi^2/t}.
$$
Both $\phi_{t,a}$ and $\mathcal F\phi_{t,a}$ lie in $\mathcal S(\mathbb R,\mathbb C)$ (and satisfy Tier III with $b=2$). Applying Lemma 1(2) at $u=0$ gives
$$
 f_a(t)=\sum_{n\in\mathbb Z}e^{-\pi t(n+a)^2}=\sum_{m\in\mathbb Z}e^{2\pi i m a}\,t^{-1/2}e^{-\pi m^2/t}=t^{-1/2}g_a(1/t)
$$
(since $\pm m$ pairing kills $i\sin(2\pi m a)$), and setting $t=1/x$ again yields $f_a(1/x)=x^{1/2}g_a(x)$. Unfolding $\phi_{1/x,a}(u)=e^{-\pi a^2/x}e^{-\pi(1/x)u^2-2\pi(a/x)u}$ shows that Route 2 and Route 1 at $(z,\tau)=(ai/x,i/x)$ both evaluate part (1) at $(a_{\mathrm{quad}},b_{\mathrm{quad}})=(1/x,-a/x)$. $\square$

[Lean, read] [Gaussian/PoissonSummation.lean:38–129](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean#L38-L129) · [TwoVariable.lean:123–161](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean#L123-L161) · [TwoVariable.lean:465–491](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean#L465-L491) · [HurwitzZetaEven.lean:132–154](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L132-L154) · [HurwitzZetaEven.lean:254–277](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L254-L277)

**Hand calculation A (translated and scaled Gaussian $\phi_{t,a}(u)=e^{-\pi t(u+a)^2}$: phase, scale, zero-modes, parity, and the $a=1/2$ crossover).** Let $t>0$ and $a\in\mathbb R$, and test Route 2 on $\phi_{t,a}(u)=e^{-\pi t(u+a)^2}$.

1. *Parity, phase cancellation, and why the two `WeakFEPair` constants $(\delta_a,1)$ differ.* Under reflection $u\mapsto-u$, $\phi_{t,a}(-u)=e^{-\pi t(-u+a)^2}=\phi_{t,-a}(u)$, so $\phi_{t,a}$ is an even function of $u$ on $\mathbb R$ when $a=0$ (and its lattice restriction $n\mapsto\phi_{t,a}(n)$ is symmetric under $n\leftrightarrow-n-1$ when $a=1/2$), whereas for generic $a\notin\frac12\mathbb Z$ it has no reflection symmetry about $0$. Correspondingly, each individual Fourier sample $\mathcal F\phi_{t,a}(m)=t^{-1/2}e^{2\pi i m a}e^{-\pi m^2/t}$ carries a non-real phase $e^{2\pi i m a}$. Pairing $+m$ and $-m$ for $m\ge1$ cancels the odd imaginary part $i\sin(2\pi m a)$ and leaves real cosines, while the **dual zero-mode $m=0$** contributes
$$
 \mathcal F\phi_{t,a}(0)=\int_{\mathbb R}e^{-\pi t(u+a)^2}\,du=t^{-1/2}
$$
**independently of the shift $a$** (translation invariance of Lebesgue measure). Thus as $t\to0^+$, $f_a(t)=t^{-1/2}+2t^{-1/2}\sum_{m\ge1}\cos(2\pi m a)e^{-\pi m^2/t}\sim t^{-1/2}$ for *every* $a$, which is the Poisson source of $g_0=1$ and the universal simple pole $-\frac{1}{1-s}$ of $\Lambda_{\mathrm{even}}(a,s)$ at $s=1$. By contrast, as $t\to\infty$ on the spatial side, a zero-exponent term $(n+a)^2=0$ occurs **if and only if** $a\in\mathbb Z$, producing $f_0=\delta_a\in\{0,1\}$.

2. *Concrete numerical check at the half-integer shift $a=1/2$ ($t=1/4$ and $t=1$).* Set $a=1/2$ ($\delta_{1/2}=0$, corresponding to $E_{1/2}(s)=(2^s-1)\zeta(s)$ in §1.2.2.1).
- *Spatial lattice sum at $t=1/4$:* The shifted integers $n+1/2$ have no zero term; pairing $n=k$ with $n=-k-1$ ($k\ge0$) pairs equal distances $\pm(k+1/2)$:
$$
 f_{1/2}\Bigl(\frac14\Bigr)=2\sum_{k=0}^\infty e^{-\pi(k+1/2)^2/4}
 =2e^{-\pi/16}+2e^{-9\pi/16}+2e^{-25\pi/16}+2e^{-49\pi/16}+\cdots.
$$
Evaluating the first four shells gives $2e^{-\pi/16}\approx 1.6434499161$, $2e^{-9\pi/16}\approx 0.3416396723$, $2e^{-25\pi/16}\approx 0.0147635889$, and $2e^{-49\pi/16}\approx 0.0001326256$ (four-pair sum $1.9999858029$; adding $k=4$, $2.4767\times10^{-7}$, gives $1.9999860506$).
- *Dual Fourier sum at $t=1/4$ ($x=1/t=4$ in `h_feq`):* Here the scale factor is $t^{-1/2}=(1/4)^{-1/2}=2$, and the half-shift phase is $e^{2\pi i m(1/2)}=(-1)^m$:
$$
 2\,g_{1/2}(4)=2\Bigl(1+2\sum_{m=1}^\infty(-1)^m e^{-4\pi m^2}\Bigr)
 =2-4e^{-4\pi}+4e^{-16\pi}-\cdots.
$$
The zero-mode $m=0$ alone gives $2$; subtracting the single alternating $m=\pm1$ correction $-4e^{-4\pi}\approx-1.3949369425\times10^{-5}$ already gives $1.9999860506305752$ to sixteen significant digits (the $m=\pm2$ term is $+4e^{-16\pi}\approx 5.92\times10^{-22}$), directly confirming $f_{1/2}(1/4)=4^{1/2}g_{1/2}(4)$.
- *Self-dual crossover $t=1$:* At $t=1$, $f_{1/2}(1)=g_{1/2}(1)=2\sum_{k=0}^\infty e^{-\pi(k+1/2)^2}=1+2\sum_{m=1}^\infty(-1)^m e^{-\pi m^2}\approx 0.9135791381561168$.

**Hand calculation B (nonzero rational twist $r=1/3$: phase-to-shift exchange, zero-term asymmetry, concurrent shift $c=1/4$, and odd-parity weight).** Now place a nonzero rational additive character on the spatial side by setting $r=1/3$ and $\psi_{t,1/3}(u)=e^{2\pi i u/3}e^{-\pi t u^2}$ ($t>0$).

1. *Pure twist $r=1/3$: parity split and why the dual zero-mode disappears.* Split $\psi_{t,1/3}$ into its even real part and odd imaginary part:
$$
 \psi_{t,1/3}(u)=\cos\Bigl(\frac{2\pi u}{3}\Bigr)e^{-\pi t u^2}+i\sin\Bigl(\frac{2\pi u}{3}\Bigr)e^{-\pi t u^2}.
$$
On the unshifted lattice $n\in\mathbb Z$, the **spatial zero-term $n=0$** equals $\psi_{t,1/3}(0)=1$, while pairing $\pm n$ ($n\ge1$) kills the odd sine part identically and doubles $\cos(2\pi n/3)\in\{-1/2,-1/2,+1\}$, producing the cosine kernel $g_{1/3}(t)=1+2\sum_{n=1}^\infty\cos(2\pi n/3)e^{-\pi n^2 t}$. On the frequency side, Lemma 2(2) with $(a,b)=(t,i/3)$ gives
$$
 \mathcal F\psi_{t,1/3}(\xi)=\frac{1}{t^{1/2}}\exp\Bigl(\frac{\pi(i/3-i\xi)^2}{t}\Bigr)=t^{-1/2}e^{-\pi(\xi-1/3)^2/t}.
$$
The spatial phase $e^{2\pi i u/3}$ has turned into a **dual rational shift $\xi\mapsto\xi-1/3$**, and because $m-1/3\ne0$ for every $m\in\mathbb Z$, the dual sum has **no zero-exponent term**:
$$
 g_{1/3}(t)=\sum_{n\in\mathbb Z}\psi_{t,1/3}(n)=t^{-1/2}\sum_{m\in\mathbb Z}e^{-\pi(m-1/3)^2/t}=t^{-1/2}f_{1/3}(1/t)
$$
(reindexing $m\mapsto-m$ sends $(m-1/3)^2$ to $(m+1/3)^2$). This is `(hurwitzEvenFEPair (1/3)).symm.h_feq`! Moreover, as $t\to0^+$, the nearest dual lattice point $m=0$ ($m-1/3=-1/3$) dominates with $g_{1/3}(t)\sim t^{-1/2}e^{-\pi/(9t)}\to0$ faster than every power of $t$ — showing directly from Poisson summation why $g_{1/3,\mathrm{modif}}$ in §1.2.2.6, Hand calculation B(1), required no $(0,1)$ subtraction. Numerically, at $t=1/3$, the primal oscillating series $1-e^{-\pi/3}-e^{-4\pi/3}+2e^{-3\pi}-\cdots\approx 0.6340769191036943$ matches $\sqrt3\bigl(e^{-\pi/3}+e^{-4\pi/3}+e^{-7\pi/3}+\cdots\bigr)\approx 0.6078109354+0.0262658921+9.16\times10^{-8}=0.6340769191$; at $t=3$, $g_{1/3}(3)=3^{-1/2}f_{1/3}(1/3)\approx 0.9999193004824297$.

2. *Concurrent spatial shift $c=1/4$ and twist $r=1/3$ at $t=1$ (full complex Tier I).* Evaluating Lemma 1(2) for $\psi_{1,1/3}$ at $x=c=1/4$ breaks the $n\leftrightarrow-n$ symmetry on $\mathbb Z+1/4$, so **both** parity components survive and the sum is genuinely complex:
$$
 \sum_{n\in\mathbb Z}e^{2\pi i(n+1/4)/3}e^{-\pi(n+1/4)^2}
 =\sum_{m\in\mathbb Z}e^{2\pi i m/4}\mathcal F\psi_{1,1/3}(m)
 =\sum_{m\in\mathbb Z}i^m e^{-\pi(m-1/3)^2}\approx 0.7051844385+0.2437665727\,i
$$
($m=0$ gives $e^{-\pi/9}\approx 0.70534668$, $m=1$ gives $+i e^{-4\pi/9}\approx+0.24752012\,i$, $m=-1$ gives $-i e^{-16\pi/9}\approx-0.00375355\,i$, $m=2$ gives $-e^{-25\pi/9}\approx-0.00016224$). Notice the phase bookkeeping: because $\psi_{1,1/3}(n+1/4)$ already shifts $u$ inside $e^{2\pi i u/3}$, no extra cross-phase appears; if one sums the unshifted-phase series $\sum_{n\in\mathbb Z}e^{2\pi i n/3}e^{-\pi(n+1/4)^2}$ instead, factoring out $e^{-2\pi i(1/3)(1/4)}=e^{-\pi i/6}$ multiplies the right-hand side by $e^{-\pi i/6}$.

3. *Odd-parity linear weight $u\psi_{1,1/3}(u)$ (connection to §1.3.2.1).* Multiplying $\psi_{1,1/3}(u)$ by the odd factor $u$ kills the $n=0$ term ($0\cdot1=0$) and reverses parity: now the even real part $u\cos(2\pi u/3)e^{-\pi u^2}$ cancels on $\pm n$, while the imaginary part doubles to $2i\sum_{n\ge1}n\sin(2\pi n/3)e^{-\pi n^2}$. Since $\mathcal F(u\psi_{1,1/3})(\xi)=-\frac{1}{2\pi i}\frac{d}{d\xi}\bigl(e^{-\pi(\xi-1/3)^2}\bigr)=-i(\xi-1/3)e^{-\pi(\xi-1/3)^2}$, Tier IV Poisson summation at $x=0$ gives the purely imaginary identity
$$
 \sum_{n\in\mathbb Z}n e^{2\pi i n/3}e^{-\pi n^2}
 =2i\sum_{n=1}^\infty n\sin\Bigl(\frac{2\pi n}{3}\Bigr)e^{-\pi n^2}
 =-i\sum_{m\in\mathbb Z}\Bigl(m-\frac13\Bigr)e^{-\pi(m-1/3)^2}\approx 0.0748366215\,i,
$$
which (after reindexing $m\mapsto-m$ so $-(m-1/3)=m+1/3$) is $i G_{1/3}(1)=i F_{1/3}(1)$ from §1.3.2.1!

**Counterexamples (deleting individual hypotheses across the tiers and at $\Re a=0$).** Each condition in Lemma 1 and Theorem 3(1) does genuine work:

1. *Deleting $\ell^1(\mathbb Z)$ Fourier summability `hFf` while keeping $f\in C_c(\mathbb R)$ (`hc`, `h_norm`, and `hf` for every $b>1$).* Define
$$
 f(x)=\mathbf 1_{[0,1]}(x)\sum_{k=2}^\infty\frac{\sin(2\pi k x)}{k\log k}.
$$
Each term vanishes at $x=0,1$. To see that the sine series converges uniformly on $[0,1]$ (a special case of the Chaundy–Jolliffe criterion $k b_k\to0$), fix $x\in(0,1/2]$, set $n_0=\lfloor 1/(2x)\rfloor$, and split any tail $N\le k\le M$ ($N\ge2$) at $n_0$: for $k\le n_0$, $\sin(2\pi k x)\le 2\pi k x$ bounds the lower block by $2\pi x\sum_{k=N}^{n_0}\frac{1}{\log k}\le\frac{2\pi x n_0}{\log N}\le\frac{\pi}{\log N}$; for $k>\max(N,n_0)$, summation by parts with $\bigl\lvert\sum_{j=p}^{q}\sin(2\pi j x)\bigr\rvert\le\frac{1}{\sin(\pi x)}\le\frac{1}{2x}$ bounds the upper block by $\frac{2}{2x}\cdot\frac{1}{(n_0+1)\log N}\le\frac{2}{\log N}$, and $x\in[1/2,1)$ follows by $x\mapsto 1-x$. Thus $f\in C_c(\mathbb R)$ is continuous and supported in $[0,1]$, satisfying `hc`, `h_norm`, and $f(x)=O(\lvert x\rvert^{-b})$ for **every** $b>1$. Yet integrating termwise on $[0,1]$ gives $\mathcal F f(\pm k)=\mp\frac{1}{2i k\log k}$ for $k\ge2$ (and $0$ for $\lvert k\rvert\le1$), so $\sum_{m\in\mathbb Z}\lvert\mathcal F f(m)\rvert=\sum_{k=2}^\infty\frac{1}{k\log k}=\infty$. At $x=1/4$, the spatial sum has only the $n=0$ term
$$
 \sum_{n\in\mathbb Z}f\Bigl(\frac14+n\Bigr)=f\Bigl(\frac14\Bigr)=\sum_{j=1}^\infty\frac{(-1)^j}{(2j+1)\log(2j+1)}\approx-0.2233318681\ne0;
$$
although symmetric partial sums $\sum_{\lvert m\rvert\le N}e^{\pi i m/2}\mathcal F f(m)$ converge conditionally to $f(1/4)$, the moduli $\lvert e^{\pi i m/2}\mathcal F f(m)\rvert=\lvert\mathcal F f(m)\rvert$ are not summable, so Lean's unordered `∑' m, cexp (2 * π * I * x * m) * 𝓕 f m` evaluates to **`0` at every $x\in\mathbb R$**, falsifying Tier I/II at $x=1/4$ (`-0.22333… ≠ 0`).

2. *Deleting continuity `hc` while keeping compact support and $\mathcal F f\in\ell^1(\mathbb Z)$.* Let $f=\mathbf 1_{[-1/2,1/2]}$. Here $f$ is supported in $[-1/2,1/2]$ (`h_norm` and `hf` hold for all $b>1$) and $\mathcal F f(m)=\int_{-1/2}^{1/2}e^{-2\pi i m x}\,dx=\delta_{m,0}$, which is finitely supported (`hFf` holds trivially!). Yet at $x=1/2$, $\sum_{n\in\mathbb Z}f(1/2+n)=f(-1/2)+f(1/2)=1+1=2$, whereas $\sum_{m\in\mathbb Z}e^{\pi i m}\mathcal F f(m)=1\ne2$ (midpoint averaging $\frac12(f(x^-)+f(x^+))$, `[DLMF 1.8.15]`, restores $1=1$, as noted in Chapter 14, §14.4.2).

3. *Deleting `h_norm` while keeping $f\in C^\infty(\mathbb R)\cap L^1(\mathbb R)$, and deleting $\Re a>0$ in Theorem 3(1).* Choose a smooth bump $\eta\in C_c^\infty([-1/4,1/4])$ with $0\le\eta\le1$ and $\eta(0)=1$, and set $f(x)=\sum_{n\in\mathbb Z}\eta\bigl(2^{\lvert n\rvert}(x-n)\bigr)$. Because the supports $[n-2^{-\lvert n\rvert-2},n+2^{-\lvert n\rvert-2}]$ are disjoint with isolated locally finite neighborhoods, $f\in C^\infty(\mathbb R)$ and $\lVert f\rVert_{L^1}=\lVert\eta\rVert_{L^1}\sum_{n\in\mathbb Z}2^{-\lvert n\rvert}=3\lVert\eta\rVert_{L^1}<\infty$; yet $f(n)=1$ for every $n\in\mathbb Z$, so the lattice series $\sum_{n\in\mathbb Z}f(n)$ fails to converge (`h_norm` fails even on $K=\{0\}$). Similarly, on the imaginary boundary $\Re a=0$ of Theorem 3(1) (say $a=i$, $b=0$), $\lvert e^{-\pi i n^2}\rvert=1\not\to0$, so both sides of `Complex.tsum_exp_neg_quadratic` degenerate to Lean's non-summable junk value $0$, carrying no Gaussian transform content.

**Remarks.**

1. *Why Mathlib routes `Complex.tsum_exp_neg_quadratic` through Tier III rather than Tier IV.* Every complex-parameter Gaussian $u\mapsto e^{-\pi a u^2+2\pi b u}$ ($\Re a>0$) belongs to $\mathcal S(\mathbb R,\mathbb C)$, so mathematically Tier IV applies. In Lean, however, constructing an inhabitant of `SchwartzMap ℝ ℂ` requires proving polynomial decay bounds on *all* iterated Fréchet derivatives `iteratedFDeriv ℝ k f`. David Loeffler's proof (`Gaussian/PoissonSummation.lean:114`) instead invokes Tier III (`Real.tsum_eq_tsum_fourier_of_rpow_decay` at $b=2$, modeled on Stein–Weiss `[SteinWeiss1971]`, Ch. VII, §2, Corollary 2.6, pp. 251–252), needing only the zeroth-order bound `cexp_neg_quadratic_isLittleO_abs_rpow_cocompact` on $f$ and on its explicit closed-form Fourier transform $\mathcal F f$. Meanwhile, Tier II (`_of_rpow_decay_of_summable`) is used directly in archive A2 (`SummableOneAddSq.lean:184` and `PRowPoisson.lean:170`) for rougher kernels such as $(1+x^2)^{-1}$ whose Fourier transform $e^{-2\pi\lvert\xi\rvert}$ is manifestly in $\ell^1(\mathbb Z)$ without computing $O(\lvert\xi\rvert^{-b})$ bounds first, and Tier IV is invoked in `TateMain.lean:77`.

2. *Classical precedence and theta conventions.* Siméon-Denis Poisson introduced the summation formula in his 1823 *Journal de l'École Polytechnique* memoir `[Poisson1823]` (p. 420); Jacobi proved the theta transformation in *Fundamenta Nova* `[Jacobi1829]` (p. 184; `[DLMF 20.7.32]`). Note a naming quirk in Mathlib: `jacobiTheta₂ z τ` (`TwoVariable.lean:78`, with `jacobiTheta τ = jacobiTheta₂ 0 τ`) is the unshifted sum $\sum_{n\in\mathbb Z}e^{2\pi i n z+\pi i n^2\tau}$, which in Whittaker–Watson / NIST DLMF notation (`[DLMF 20.2.3]`) is $\theta_3(\pi z\mid\tau)$ (the subscript `₂` in Mathlib means "two-variable", not Jacobi's half-shifted $\theta_2$). Differentiating Theorem 3(2) with respect to $z$ gives `jacobiTheta₂'_functional_equation` (`TwoVariable.lean:493–528`), which supplies `oddKernel_functional_equation` in §1.3.2.1. [DLMF 1.8.14–16](https://dlmf.nist.gov/1.8#E14) · [DLMF 20.2.3, 20.7.32](https://dlmf.nist.gov/20.7#E32)

3. *Closing two retained Chapter 1 boundaries simultaneously.* Lemma 2(1) and Theorem 3 close **both** `Complex.tsum_exp_neg_quadratic` / `jacobiTheta₂_functional_equation` (retained at the boundary of §§1.2.2.1, 1.2.2.6, and 1.3.2.1) and `Real.Gamma_one_half_eq` / `Complex.Gamma_one_half_eq` (`GaussianIntegral.lean:307–326`, retained at the boundary of §§1.2.2.2–1.2.2.5). Across the entire Chapter 1 path from `GaussianIntegral.lean` and `Analysis/Fourier/PoissonSummation.lean` up to `riemannZeta_one_sub` and `RhOfRight.lean:28`, only standard real/complex analysis library theorems (polar coordinates, Fubini, rectangular Cauchy theorem, dominated convergence, Hilbert-sum representation, and `integral_image_eq_integral_abs_deriv_smul`) remain at interface level.

| Declaration read at R3 here | Direct consumers in pinned Mathlib / archive A2 | Role in the book |
|---|---|---|
| `ContinuousMap.periodic_tsum_comp_add_zsmul`, `Real.integrable_of_summable_norm_Icc`, `Integrable.hasSum_intervalIntegral_comp_add_int` ([Periodic.lean:30–45](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/Periodic.lean#L30-L45), [Lebesgue/Integral.lean:52–67](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean#L52-L67), [IntervalIntegral/Basic.lean:1457–1469](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean#L1457-L1469)) | `Real.fourierCoeff_tsum_comp_add` and `Real.tsum_eq_tsum_fourier` ([Analysis/Fourier/PoissonSummation.lean:52–117](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/PoissonSummation.lean#L52-L117)); archive `PoissonSum.lean:119–154` | Lemma 1(1) and Chapter 14, §14.4.2 |
| `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`, `Real.tsum_eq_tsum_fourier_of_rpow_decay`, `SchwartzMap.tsum_eq_tsum_fourier` ([Analysis/Fourier/PoissonSummation.lean:195–226](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/PoissonSummation.lean#L195-L226)) | `Complex.tsum_exp_neg_quadratic` (`Gaussian/PoissonSummation.lean:114`, via Tier III at $b=2$); archive `SummableOneAddSq.lean:184` and `PRowPoisson.lean:170` (Tier II), `TateMain.lean:77` (Tier IV) | Lemma 1(2) and Theorem 3(1) |
| `integral_gaussian_complex`, `Real.Gamma_one_half_eq`, `Complex.Gamma_one_half_eq`, `fourier_gaussian_pi'` ([GaussianIntegral.lean:237–274, 307–326](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean#L237-L326), [Gaussian/FourierTransform.lean:207–225](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean#L207-L225)) | `Complex.tsum_exp_neg_quadratic` (`Gaussian/PoissonSummation.lean:110`); `doublingGamma_one` (`BohrMollerup.lean:406`, §1.2.2.5); `Gammaℝ_one` and `hasDerivAt_Gammaℝ_one` (§§1.2.2.2–1.2.2.4) | Lemma 2 and §§1.2.2.2–1.2.2.5 |
| `Complex.tsum_exp_neg_quadratic` ([Gaussian/PoissonSummation.lean:87–117](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean#L87-L117)) | `jacobiTheta₂_functional_equation` ([TwoVariable.lean:476](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean#L476)); specializations `tsum_exp_neg_mul_int_sq` and `_pi_mul_int_sq` (`:119–129`) | Theorem 3(1)–(2) |
| `jacobiTheta₂_functional_equation` ([TwoVariable.lean:465–491](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean#L465-L491)) | `evenKernel_functional_equation` → `(hurwitzEvenFEPair a).h_feq` ([HurwitzZetaEven.lean:146, 276](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L146)); `jacobiTheta₂'_functional_equation` (`TwoVariable.lean:512`) → `oddKernel_functional_equation` (`HurwitzZetaOdd.lean:92`, §1.3.2.1); archive `ThetaFunctions.lean:12` | Theorem 3(3), §1.2.2.6, and §1.3.2.1 |

**Source note.** The reading is R3 for `Compact.lean:456–474` (`ContinuousMap.tsum_apply`, `summable_of_locally_summable_norm`), `Periodic.lean:30–45` (`periodic_tsum_comp_add_zsmul`), `DominatedConvergence.lean:219–242` (`hasSum_intervalIntegral_of_summable_norm`, `tsum_intervalIntegral_eq_of_summable_norm`), `Lebesgue/Integral.lean:52–67` (`Real.integrable_of_summable_norm_Icc`), `IntervalIntegral/Basic.lean:1457–1469` (`Integrable.hasSum_intervalIntegral_comp_add_int`), `l2Space.lean:446–448, 539–553` (`HilbertBasis.hasSum_repr`, `HilbertBasis.mk`), `Analysis/Fourier/PoissonSummation.lean:125–226` (`isBigO_norm_Icc_restrict_atTop`, `_atBot`, `isBigO_norm_restrict_cocompact`, Tiers II–IV), `SchwartzSpace/Basic.lean:151–163` (`isBigO_cocompact_rpow`), and `SchwartzSpace/Fourier.lean:51–103` (`fourierTransformCLM`); for `GaussianIntegral.lean:159–274, 307–326` (`integral_mul_cexp_neg_mul_sq`, `integral_gaussian_sq_complex`, `integral_gaussian`, `continuousAt_gaussian_integral`, `integral_gaussian_complex`, `Real.Gamma_one_half_eq`, `Complex.Gamma_one_half_eq`) and `Gaussian/FourierTransform.lean:49–225` (`norm_cexp_neg_mul_sq_add_mul_I`, `verticalIntegral_...`, `integral_cexp_neg_mul_sq_add_real_mul_I`, `integral_cexp_quadratic`, `fourier_gaussian_pi'`); and for `Gaussian/PoissonSummation.lean:38–129` (`cexp_neg_quadratic_isLittleO_abs_rpow_cocompact`, `Complex.tsum_exp_neg_quadratic`), `TwoVariable.lean:123–161, 465–491` (`jacobiTheta₂_undef`, `jacobiTheta₂_functional_equation`), and `HurwitzZetaEven.lean:65–100, 132–154, 254–277` (`evenKernel_def`, `cosKernel_def`, `evenKernel_functional_equation`, `hurwitzEvenFEPair`). Inherited without repetition are the top-level `AddCircle` bridge of `Real.fourierCoeff_tsum_comp_add` and `Real.tsum_eq_tsum_fourier` and the circle Stone–Weierstrass/$L^2$ density and `hasSum_fourier_series_of_summable` proofs ([Chapter 14, §§14.4.2–14.4.2.3](14-masullos-trace-formula-route.md#1442-poisson-summation-on-the-real-line-and-a-prime-power-toy-model)), the `WeakFEPair` Mellin functional equation (§1.2.2.6), and the differentiated odd-theta chain (§1.3.2.1). Inputs retained by name (statements read, proof bodies not expanded here) are `ContinuousMap.exists_tendsto_compactOpen_iff_forall`, `summable_of_norm_bounded`, `hasSum_integral_of_dominated_convergence`, `integrable_of_summable_norm_restrict`, `Integrable.hasSum_integral_iUnion`, `Orthonormal.isHilbertSum`, `Real.summable_abs_int_rpow`, `isLittleO_exp_neg_mul_rpow_atTop`, `one_add_le_sup_seminorm_apply`, `integral_prod_mul`, `integral_comp_polarCoord_symm`, `setIntegral_prod_mul`, `integral_Ioi_of_hasDerivAt_of_tendsto'`, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `IsPreconnected.eq_of_sq_eq`, `continuousAt_cpow_const`, `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, `intervalIntegral_tendsto_integral`, `integral_add_right_eq_self`, and `Complex.inv_cpow`. Classical references (`[Poisson1823]`, `[Jacobi1829]`, `[SteinWeiss1971]` Cor. VII.2.6, and NIST DLMF §§1.8(iv) and 20.2/20.7) were checked bibliographically and against DLMF. The [proof map](../notes/proof-map.md#p1-chapter-1-from-poisson-summation-to-theta-inversion) gives pinned paths and lines. Hand calculations A and B, the direct Route-2 comparison, and the hypothesis-deletion counterexamples are ours; all numerical and exact-rational assertions (`verify_ch01_poisson_fe.py`, 48 assertions in 0.23 s CPU, cross-checked to 45 digits) are consistency checks, not formal proof certificates, and no Lean kernel compilation was run.

#### 1.2.2.8 Hilbert expansion and the norm behind Poisson summation

**Motivation.** In [§1.2.2.7](#1227-from-poisson-summation-to-theta-inversion), periodization produces a continuous function on the circle and the Fourier integrals give its coordinates. Which norm lets us reconstruct the function from those coordinates? Orthogonality turns the squared $L^2$ norm of a finite sum into a sum of squares. Density ensures that the coordinates determine the entire function class. Evaluating at a point will require a separate argument.

**Example A. A finite orthogonal change of coordinates.** In $\mathbb R^2$ take $u=(3,4)/5$, $v=(-4,3)/5$, and $x=(2,-1)$. The squared lengths are $(9+16)/25=(16+9)/25=1$ and the dot product is $(-12+12)/25=0$. The matrix with columns $u,v$ has transpose as inverse. Applying that transpose to $x$ gives coordinates $(6-4)/5=2/5$ and $(-8-3)/5=-11/5$. Multiplying them by $u$ and $v$ gives $(6,8)/25$ and $(44,-33)/25$. Their sum is $(50,-25)/25=x$. The energy identity reads $4+1=4/25+121/25$. Keeping just $u$ leaves the second projection as residual, of squared norm $121/25$.

**Example B. A circle trigonometric polynomial.** Write $e_n(t)=\exp(2\pi i n t)$ and use measure $dt$ on $[0,1]$. The integral of $e_k$ is $1$ for $k=0$ and $(\exp(2\pi i k)-1)/(2\pi i k)=0$ otherwise. Take $P(t)=1+2\cos(2\pi t)+3\sin(2\pi t)$. Euler's formulas give $P=1+(1-3i/2)e_1+(1+3i/2)e_{-1}$. In $\int_0^1 e_{-n}(t)P(t)\,dt$, each term integrates to its coefficient when its frequency equals $n$ and to zero otherwise. The three coefficients reconstruct $P$ in any order. Their squared moduli add to $1+13/4+13/4=15/2$. Direct integration gives the same value for $\int_0^1 |P|^2\,dt$. The linear terms and the mixed sine–cosine term have zero mean, and the squared sine and cosine have mean $1/2$, giving $1+4/2+9/2$. Keeping only frequencies $\{0,1\}$ leaves $(1+3i/2)e_{-1}$ with squared norm $13/4$.

**Definitions.** Work in an inner product space $H$ over $\mathbb K=\mathbb R$ or $\mathbb C$, with the inner product linear in its second slot. An orthonormal family $(u_i)_{i\in I}$ satisfies $\langle u_i,u_j\rangle=\delta_{ij}$. Write $M=\overline{\operatorname{span}}\{u_i:i\in I\}$ for the norm closure of its finite linear combinations. The family is *total* when $M=H$. The space $\ell^2(I,\mathbb K)$ consists of scalar families $a$ with $\sup_F\sum_{i\in F}|a_i|^2<\infty$, with squared norm given by that supremum. Here $F$ ranges over finite subsets of $I$. An *unordered sum* of vectors $z_i$ equals $z$ if for every $\varepsilon>0$ some finite $F_0$ satisfies $\|\sum_{i\in F}z_i-z\|<\varepsilon$ for every finite $F\supseteq F_0$. This is the finite-subset net in Lean's ordinary HasSum. A Hilbert basis is a linear isometric equivalence $H\to\ell^2(I,\mathbb K)$ with basis vectors the inverse images of the unit coordinate vectors $\delta_i$.

**Lemma 1 (finite projections and Bessel's inequality).** For $x\in H$ put $c_i=\langle u_i,x\rangle$ and $P_F x=\sum_{i\in F}c_i u_i$. Then $c\in\ell^2$ and $\|c\|_2\le\|x\|$.

**Proof.** The residual is orthogonal to each $u_j$ with $j\in F$ because $\langle u_j,P_F x\rangle=c_j$. Expanding squared norms gives $\|x-P_Fx\|^2+\sum_{i\in F}|c_i|^2=\|x\|^2$. The bound follows by taking the supremum. $\square$

**Lemma 2 (synthesis and its range).** If $H$ is complete and $a\in\ell^2(I,\mathbb K)$, the unordered sum of $a_i u_i$ exists. The map $Sa=\sum_i a_i u_i$ is a linear isometry onto $M$.

**Proof.** Put $A=\sup_F\sum_{i\in F}|a_i|^2$. For $\varepsilon>0$ choose $F_0$ with $\sum_{i\in F_0}|a_i|^2>A-\varepsilon^2$. For finite sets $F,G$ containing $F_0$, the squared norm of the difference of the two finite sums is $\sum_{i\in F\triangle G}|a_i|^2$ by orthogonality. The symmetric difference avoids $F_0$, so this is at most $A-\sum_{i\in F_0}|a_i|^2$. Completeness of $H$ gives the limit. Addition and scalar multiplication pass through the limits. Finite Pythagoras and norm continuity give $\|Sa\|^2=A$.

The same tail bound gives $\|a-\sum_{i\in F}a_i\delta_i\|_2^2=A-\sum_{i\in F}|a_i|^2$, so the coordinate truncations converge in $\ell^2$. To see completeness of $\ell^2$, take a Cauchy sequence $(a^{(n)})$. Each coordinate converges because its modulus is bounded by the $\ell^2$ norm. For $m,n$ in a tail where $\|a^{(n)}-a^{(m)}\|_2\le\varepsilon$, hold $n$ fixed and let $m$ tend to infinity in a finite sum of squared differences. The resulting finite sum for $a^{(n)}-a$ is at most $\varepsilon^2$, where $a$ is the coordinatewise limit. Taking suprema gives membership in $\ell^2$ for the difference, hence also for $a$, and norm convergence. The isometric range is therefore complete and closed in $H$. It contains every $u_i=S\delta_i$, so it contains $M$. Each $Sa$ is a limit of finite linear combinations and belongs to $M$. $\square$

**Lemma 3 (the orthogonal complement test).** If $H$ is complete, then for any subspace $N$ we have $(N^\perp)^\perp=\overline N$. In particular, totality is equivalent to the condition that zero is the only vector orthogonal to every $u_i$.

**Proof.** Set $K=\overline N$. Inner product continuity gives $K^\perp=N^\perp$. For $x\in H$ let $d=\inf_{y\in K}\|x-y\|$ and take $y_n\in K$ with distances tending to $d$. The parallelogram identity and $(y_n+y_m)/2\in K$ bound $\|y_n-y_m\|^2$ by $2\|x-y_n\|^2+2\|x-y_m\|^2-4d^2$, which tends to zero. The sequence converges in $K$ to a minimizer $y$. Write $r=x-y$. For $w\in K$ and real $t$, minimality gives $0\le t^2\|w\|^2-2t\operatorname{Re}\langle r,w\rangle$. Letting $t$ tend to zero from both sides gives zero real part. Over $\mathbb C$, applying the same argument to $iw$ gives zero imaginary part. Thus $r\in K^\perp$. If $x\in(K^\perp)^\perp$, then $\langle r,x\rangle=\langle r,y\rangle+\|r\|^2=\|r\|^2$ is zero, so $x=y\in K$. The reverse inclusion follows from conjugate symmetry. Apply this identity to the span of the family to get the test. $\square$

**Theorem (Hilbert basis and unordered reconstruction).** Assume $H$ is complete and $(u_i)$ is orthonormal and total, equivalently its span has zero orthogonal complement. Then $x\mapsto(\langle u_i,x\rangle)_{i\in I}$ is a linear isometric equivalence onto $\ell^2(I,\mathbb K)$ with inverse $S$. Its basis vectors are the $u_i$. For every $x\in H$ the unordered sum $\sum_i\langle u_i,x\rangle u_i$ equals $x$, and $\sum_i|\langle u_i,x\rangle|^2=\|x\|^2$.

**Proof.** Lemma 2 gives surjectivity of $S$ under totality. Apply the continuous functional $\langle u_j,\cdot\rangle$ to the finite synthesis sums. It is eventually equal to $a_j$, since the finite sets eventually contain $j$. Thus $S^{-1}x$ has the stated coordinates and $S^{-1}u_i=\delta_i$. Its squared norm equals $\|x\|^2$, giving Parseval's identity. Apply $S$ to the convergent coordinate truncations of $S^{-1}x$. By continuity of $S$ and $S(a_i\delta_i)=a_i u_i$, the resulting finite sums converge to $x$ in norm. For a countable family this implies convergence along every enumeration, since each fixed finite set is eventually included. $\square$

**Failure without totality.** Keep only $u=(3,4)/5$ from Example A. The unit vector $v=(-4,3)/5$ belongs to the orthogonal complement. Its only retained coordinate is zero, so the reconstructed vector and the squared coefficient sum are both zero, although $\|v\|^2=1$. In general Lemma 1 still gives coefficients in $\ell^2$, and their sum is a vector $y\in M$. Testing against every $u_i$ shows $x-y\in M^\perp$ by continuity. The sum therefore recovers the orthogonal projection, with $\|x\|^2=\|y\|^2+\|x-y\|^2$.

**Remark on the Lean proof.** [Lean, read] Mathlib first constructs synthesis for the orthogonal isometries $a\mapsto a u_i$. In `OrthogonalFamily.linearIsometry` the square-summability criterion guarantees existence and the finite norm identity proves the isometry by taking limits. `OrthogonalFamily.range_linearIsometry` uses completeness of the source to show the range is closed and uses single-coordinate vectors to exhibit the generators in that range. `Orthonormal.isHilbertSum` identifies the supremum of the scalar-line ranges with the span of the family. `IsHilbertSum.mk` uses density to obtain surjectivity. `HilbertBasis.mk` stores the inverse of synthesis as `repr`, and `coe_mk` identifies its basis vectors. The optional constructor `mkOfOrthogonalEqBot` converts the complement hypothesis by the double-complement theorem. [l2Space.lean:184–253](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L184-L253) · [l2Space.lean:277–314](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L277-L314) · [l2Space.lean:347–354](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L347-L354) · [l2Space.lean:533–563](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L533-L563) · [Projection/Submodule.lean:34–92](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean#L34-L92)

[Lean, read] For a given Hilbert basis, `repr_apply_apply` transports the inner product to the coordinate space and tests against $\delta_i$. `hasSum_repr_symm` transports the unordered identity from `lp.hasSum_single` through the continuous linear inverse of `repr`. Each mapped single-coordinate term is $a_i u_i$ by linearity. `hasSum_repr` substitutes $a=\operatorname{repr}(x)$ and simplifies the inverse composed with the forward map. Ambient completeness is a hypothesis of the constructor. The expansion lemma itself takes the basis as given; the summation-filter Cauchy criteria, countable-support theorem, closed-range supply, and continuous-linear `HasSum` transport behind these steps are read in [§1.2.2.9](#1229-unordered-summation-finite-tail-cauchy-criteria-and-banach-completeness). [l2Space.lean:376–447](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L376-L447) · [lpSpace.lean:1149–1192](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Lp/lpSpace.lean#L1149-L1192) · [lpSpace.lean:1343–1370](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Lp/lpSpace.lean#L1343-L1370)

**Remark on the Poisson consumer.** The circle character orthonormality and dense-span proofs come from [Chapter 14, §§14.4.2.1–14.4.2.3](14-masullos-trace-formula-route.md#14421-fourier-completeness-on-the-circle-and-pointwise-reconstruction). On the circle with probability Haar measure, `fourierBasis` feeds those two hypotheses to `HilbertBasis.mk`. The coordinate of an $L^2$ class at $n$ is its Fourier integral because the first slot conjugates $e_n$. Then `hasSum_fourier_series_L2` applies `HilbertBasis.hasSum_repr` to give $L^2$ reconstruction. [AddCircle.lean:261–283](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L261-L283) · [AddCircle.lean:407–436](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L407-L436)

For the continuous periodization $F$ in §1.2.2.7, Tier I also assumes absolute summability of the sampled Fourier transform. The periodization coefficient identity transfers this to $\sum_n|\widehat F(n)|<\infty$. Since $\|e_n\|_\infty=1$, the finite-subset Fourier sums converge uniformly to a continuous $G$. The inequality $\|h\|_2\le\|h\|_\infty$ on the probability circle transfers uniform limits to $L^2$. Uniqueness there identifies the classes of $G$ and $F$. If $G-F$ were nonzero at a point, continuity would bound its modulus below on an open arc of positive measure, contradicting that equality. Evaluation is continuous for the uniform norm. Lean follows this route from `hasSum_fourier_series_of_summable` to `has_pointwise_sum_fourier_series_of_summable`, invoked by `Real.tsum_eq_tsum_fourier`. The Gaussian specialization and theta and Hurwitz uses are in §§1.2.2.6–1.2.2.7. [AddCircle.lean:485–506](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L485-L506) · [LpSpace/ContinuousFunctions.lean:178–194](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean#L178-L194) · [Fourier/PoissonSummation.lean:103–117](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/PoissonSummation.lean#L103-L117)

The Hilbert theorem alone gives no pointwise Fourier convergence assertion. Point values depend on representatives, and even on continuous functions the $L^2$ norm does not control evaluation. For example, $g_N(t)=\max(1-N\,d(t,0),0)$ with circular distance $d$ satisfies $g_N(0)=1$ and $\|g_N\|_2^2=2\int_0^{1/N}(1-Nt)^2\,dt=2/(3N)$ for $N\ge2$. Square summability also allows $a_n=1/n$ for positive $n$ and zero elsewhere. Synthesis gives an $L^2$ class with these coefficients, yet the symmetric Fourier partial sums at $0$ are harmonic partial sums and diverge. For the classical circle Parseval identity, compare [NIST DLMF §1.8(i)](https://dlmf.nist.gov/1.8#Px2).

#### 1.2.2.9 Unordered summation, finite-tail Cauchy criteria, and Banach completeness

**Motivation.** Both Analytic Spine bridges read immediately above spend infinite sums over infinite index sets before any ordered partial-sum limit is chosen. In [§1.2.2.7](#1227-from-poisson-summation-to-theta-inversion), unit-periodization restricts translates $\tau_n f$ to compact sets $K\subset\mathbb R$ and forms their sum in the Banach space $C(K,\mathbb C)$ (`Compact.lean:473`), while circle reconstruction passes from $\sum_{m\in\mathbb Z}\lvert\widehat F(m)\rvert<\infty$ to uniform convergence in $C(\mathbb R/\mathbb Z,\mathbb C)$ (`AddCircle.lean:498`) and then evaluates at a point (`AddCircle.lean:506`). In [§1.2.2.8](#1228-hilbert-expansion-and-the-norm-behind-poisson-summation), orthogonal synthesis constructs $S:\ell^2(I,\mathbb K)\to H$ over an arbitrary index set $I$ from square-summable scalars (`Subspace.lean:198–239`, `l2Space.lean:184–216`), closes its isometric image via completeness (`l2Space.lean:253`), and recovers $x=\sum_{i\in I}\langle u_i,x\rangle u_i$ by pushing single-coordinate sums through the continuous linear inverse of `repr` (`l2Space.lean:429–447`). Section 1.2.2.8 left that underlying summation-filter and Banach-completeness machinery at its named boundary.

Two related pieces already proved elsewhere in this book must be kept distinct from what is proved here:

1. *[Chapter 2, §2.6](02-functional-equations-and-primitive-characters.md#26-lean-counterpart-for-this-chapter) (§2.6.3.1)* proved the finite-tail estimate and fiber regrouping directly on $\mathbb C$ under a finite absolute-mass bound $\sup_F\sum_{i\in F}\lvert f(i)\rvert<\infty$, together with the **finite-dimensional** converse that unordered `HasSum` in $\mathbb C$ forces absolute summability by splitting into real/imaginary positive and negative quadrants, while keeping `summable_iff_cauchySeq_finset`, `Summable.of_norm`, and `Summable.of_norm_bounded` named at `[Lean]`. That complex quadrant argument is specific to finite dimension and is cited, not re-proved, here.
2. *[Chapter 9, §9.4](09-heights-slopes-and-near-orthogonality.md#94-lemmas-and-proofs) (§9.4.10)* read only the completeness-free subsequence bridge (`Analysis/Normed/Group/InfiniteSum.lean:93–107`, `hasSum_iff_tendsto_nat_of_summable_norm`), which upgrades sequential partial sums $N\mapsto\sum_{n<N}x_n$ to unordered `HasSum` once a candidate limit $a$ is **already** given and $\sum_n\lVert x_n\rVert<\infty$.

What remains — and is read at R3 below — is how a Banach space (or complete uniform additive group) **constructs** the unordered limit $a$ from finite-tail bounds over an arbitrary index set $I$, when norm summability is sufficient (`Summable.of_norm`, `Summable.of_norm_bounded`) yet not necessary (`summable_iff_cauchySeq_finset`), why nonzero support is automatically countable in any normed group without separability (`Summable.countable_support`), and how continuous linear maps and closed isometric embeddings transport `HasSum` and `tsum` back into `l2Space.lean`.

**Examples (four distinct convergence regimes on one coordinate grid).** Let $(e_n)_{n\in\mathbb N}$ denote the standard unit vectors in $\ell^2(\mathbb N)=\ell^2(\mathbb N,\mathbb R)$, and let $c_{00}(\mathbb N)\subset\ell^2(\mathbb N)$ denote the dense normed subspace of finitely supported sequences equipped with the induced $\ell^2$ norm. Four elementary series on $\mathbb N$ separate the concepts that collapse on $\mathbb C$:

| Family on $\mathbb N$ | Ambient space | Norm sum $\sum_{n\ge0}\lVert v_n\rVert_2$ | Finite-tail norm $\sup_{T\cap A_0=\emptyset}\lVert\sum_{n\in T}v_n\rVert_2$ | Unordered `HasSum`? | Ordered $\lim_{N\to\infty}\sum_{n<N}v_n$? |
|---|---|---|---|---|---|
| $y_n=2^{-(n+1)}e_n$ | $\ell^2(\mathbb N)$ (complete) | $1<\infty$ | $\le 2^{-N}$ off $\{0,\dots,N-1\}$ | Yes, sum $(2^{-(n+1)})_{n\ge0}$ | Yes, same limit |
| $x_n=(n+1)^{-1}e_n$ | $\ell^2(\mathbb N)$ (complete) | $+\infty$ (harmonic) | $<N^{-1/2}$ off $\{0,\dots,N-1\}$ | Yes, sum $((n+1)^{-1})_{n\ge0}$ | Yes, along **every** bijection $\mathbb N\to\mathbb N$ |
| $z_n=(-1)^n(n+1)^{-1}e_0$ | $\ell^2(\mathbb N)$ (complete) | $+\infty$ (harmonic) | $\ge 1/2$ on disjoint even blocks | **No** | Yes, $(\log 2)e_0$ (order-dependent) |
| $x_n=(n+1)^{-1}e_n$ or $y_n=2^{-(n+1)}e_n$ | $c_{00}(\mathbb N)$ (incomplete) | $+\infty$ for $x_n$; $1$ for $y_n$ | $<N^{-1/2}$ for $x_n$; $\le 2^{-N}$ for $y_n$ | **No** (`tsum` defaults to $0$) | **No** in $c_{00}(\mathbb N)$ |

In infinite-dimensional $\ell^2(\mathbb N)$, orthogonality decouples directions so $(x_n)$ is unconditionally summable despite $\sum_{n\ge0}\lVert x_n\rVert_2=\infty$; along a single line $\mathbb R e_0$, $(z_n)$ converges conditionally in natural order yet fails the finite-subset Cauchy test; and deleting completeness by restricting the ambient space from $\ell^2(\mathbb N)$ to $c_{00}(\mathbb N)$ destroys the unordered limit even for the norm-summable family $(y_n)$. [Expository]

**Definitions (summation filters, `HasSum`, `Summable`, `tsum`, and Cauchy partial-sum nets).** Let $I$ be any index type and let $\mathcal F(I)=\mathrm{Finset}\,I$ denote the set of finite subsets of $I$, ordered by inclusion $\subseteq$. Because $\mathcal F(I)$ is a semilattice with $\emptyset\in\mathcal F(I)$ and binary union $\cup$, its upper-tail filter (`Filter.atTop` on $\mathrm{Finset}\,I$) is proper (`NeBot`) and generated by the principal rays $\mathcal R(A_0)=\{F\in\mathcal F(I):A_0\subseteq F\}$ as $A_0$ ranges over $\mathcal F(I)$.

1. *Summation filters (`SummationFilter`).* A *summation filter* on $I$ is a filter $L$ on $\mathcal F(I)$ (`SummationFilter I`). The **unconditional summation filter** `SummationFilter.unconditional I` has underlying filter `Filter.atTop` on $\mathcal F(I)$; every unconditional summation filter satisfies `LeAtTop` ($L\le\mathrm{atTop}$) and `NeBot` ($L\ne\bot$). On $I=\mathbb N$ (or any linear order locally finite below), the **ordered conditional filter** `SummationFilter.conditional ℕ` is the pushforward `Filter.map Finset.range Filter.atTop` generated by initial segments $\{0,1,\dots,N-1\}$ (`SummationFilter.conditional_filter_eq_map_range`); because every finite $A_0\subset\mathbb N$ lies inside $\{0,\dots,N-1\}$ for $N> \max A_0$, `conditional ℕ` refines `unconditional ℕ` (`SummationFilter.le_atTop : (conditional ℕ).filter ≤ atTop`). For any injective embedding $g:J\hookrightarrow I$, pulling back finite subsets by preimage defines `L.comap g` via $F\mapsto g^{-1}(F)$.
2. *Partial sums, `HasSum`, `Summable`, and `tsum`.* Let $M$ be a commutative monoid with a topology (`[AddCommMonoid M] [TopologicalSpace M]`). For $x:I\to M$, write $S_x(F)=\sum_{i\in F}x_i$ ($F\in\mathcal F(I)$). Given $a\in M$ and a summation filter $L$ on $I$:
   - $\mathrm{HasSum}(x,a,L)$ means $\lim_{F\to L}S_x(F)=a$, i.e. $S_x$ pushes $L$ into the neighborhood filter $\mathcal N(a)$ (`Tendsto (fun s : Finset I => ∑ b ∈ s, x b) L.filter (𝓝 a)`); when $L=\mathrm{unconditional}\,I$, we write simply $\mathrm{HasSum}(x,a)$, which unfolds to: for every neighborhood $V\in\mathcal N(a)$ there exists $A_0\in\mathcal F(I)$ such that $S_x(F)\in V$ for all $F\in\mathcal F(I)$ with $A_0\subseteq F$.
   - $\mathrm{Summable}(x,L)$ means $\exists a\in M,\;\mathrm{HasSum}(x,a,L)$ (written $\mathrm{Summable}(x)$ for $L=\mathrm{unconditional}\,I$). Whenever $L'\le L$, $\mathrm{HasSum}(x,a,L)\implies\mathrm{HasSum}(x,a,L')$ (`HasSum.mono_filter`); in particular, on $\mathbb N$, unconditional `HasSum` implies ordered `conditional ℕ` convergence (`Summable.mono_filter`).
   - The totalized infinite sum $\sum'_{i\in I}x_i$ (`tsum`, notation `∑' i, x i`, or `∑'[L] i, x i`) is defined by classical choice: if $x$ has finite support (`Function.support x` finite) and $L\le\mathrm{atTop}$ is `NeBot`, it returns the finite sum over $\operatorname{supp}(x)$; otherwise, if $\mathrm{Summable}(x,L)$ holds it chooses a witness $a$ with $\mathrm{HasSum}(x,a,L)$, and if $\neg\mathrm{Summable}(x,L)$ it returns **$0\in M$** (`tsum_eq_zero_of_not_summable`). When $M$ is $T_2$ (`[T2Space M]`) and $L\ne\bot$, limits are unique (`HasSum.unique`), so $\mathrm{HasSum}(x,a,L)\implies\sum'_{i\in I}[L]x_i=a$ (`HasSum.tsum_eq`), while $\mathrm{Summable}(x,L)$ gives $\mathrm{HasSum}(x,\sum'_{i\in I}[L]x_i,L)$ (`Summable.hasSum`).
3. *Uniform Cauchy filters and finset-Cauchy nets.* Let $(X,\mathcal U)$ be a uniform space. A filter $\mathcal G$ on $X$ is **Cauchy** (`Cauchy 𝒢`) if $\mathcal G\ne\bot$ and $\mathcal G\times_f\mathcal G\le\mathcal U$, i.e. for every entourage $W\in\mathcal U$ there exists $P\in\mathcal G$ with $P\times P\subseteq W$. For a directed preorder $\alpha$ and $S:\alpha\to X$, `CauchySeq S` means `Cauchy (Filter.map S Filter.atTop)`. Taking $\alpha=\mathcal F(I)$ and $S=S_x$, `CauchySeq (fun s : Finset I => ∑ b ∈ s, x b)` is the statement that the finite-subset partial-sum net is Cauchy in $X$: for every $W\in\mathcal U$ there exists $A_0\in\mathcal F(I)$ such that $(S_x(A),S_x(B))\in W$ whenever $A_0\subseteq A$ and $A_0\subseteq B$ (`cauchy_map_iff`). [Lean, read] [SummationFilter.lean:32–48](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.lean#L32-L48) · [SummationFilter.lean:142–190](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.lean#L142-L190) · [SummationFilter.lean:215–254](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.lean#L215-L254) · [InfiniteSum/Defs.lean:106–147](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean#L106-L147) · [InfiniteSum/Defs.lean:201–202](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean#L201-L202) · [InfiniteSum/Defs.lean:308–349](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean#L308-L349) · [Cauchy.lean:31–70](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Cauchy.lean#L31-L70) · [Cauchy.lean:186–187](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Cauchy.lean#L186-L187)

**Lemma 1 (uniform-group and seminormed finite-tail Cauchy criteria, without completeness).** Let $I$ be any index set.

1. *Uniform additive group criterion (`cauchySeq_finset_iff_sum_vanishing`).* Let $G$ be a commutative topological group whose uniformity comes from subtraction (`[AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]`), and let $x:I\to G$. The partial-sum net $F\mapsto S_x(F)$ is Cauchy along `atTop` if and only if
   $$
    \forall U\in\mathcal N(0),\quad\exists A_0\in\mathcal F(I),\quad\forall T\in\mathcal F(I),\quad T\cap A_0=\emptyset\implies\sum_{i\in T}x_i\in U.
   $$
2. *Seminormed specialization (`cauchySeq_finset_iff_vanishing_norm`).* Let $E$ be a seminormed additive commutative group (`[SeminormedAddCommGroup E]`) and $x:I\to E$. Then $F\mapsto S_x(F)$ is Cauchy along `atTop` if and only if
   $$
    \forall\varepsilon>0,\quad\exists A_0\in\mathcal F(I),\quad\forall T\in\mathcal F(I),\quad T\cap A_0=\emptyset\implies\Bigl\lVert\sum_{i\in T}x_i\Bigr\rVert<\varepsilon.
   $$
3. *Cofinite norm-comparison (`cauchySeq_finset_of_norm_bounded_eventually`, `cauchySeq_finset_of_norm_bounded`).* In any `SeminormedAddCommGroup E` (complete or not), if $g:I\to\mathbb R$ is unconditionally summable in $\mathbb R$ and the set $E_0=\{i\in I:\lVert x_i\rVert>g(i)\}$ is finite (in particular if $\lVert x_i\rVert\le g(i)$ for all $i\in I$), then $F\mapsto S_x(F)$ is Cauchy along `atTop` in $E$.

**Proof.** (1) Because $G$ is an `IsUniformAddGroup`, the uniformity $\mathcal U$ of $G$ is the pullback of $\mathcal N(0)$ under $(u,v)\mapsto v-u$ (`uniformity_eq_comap_nhds_zero`). Unfolding `CauchySeq S_x` against this basis shows that $S_x$ is Cauchy along `atTop` if and only if for every $U\in\mathcal N(0)$ there exists $A_0\in\mathcal F(I)$ such that $S_x(B)-S_x(A)\in U$ whenever $A_0\subseteq A$ and $A_0\subseteq B$.

($\Rightarrow$) Suppose $S_x$ is Cauchy and let $U\in\mathcal N(0)$. Choose $A_0\in\mathcal F(I)$ from the Cauchy property for $U$. Given any finite $T\subseteq I$ with $T\cap A_0=\emptyset$, both $A=A_0$ and $B=A_0\cup T$ contain $A_0$, and disjointness gives $S_x(A_0\cup T)=S_x(A_0)+S_x(T)$ (`Finset.sum_union`). Hence
$$
 S_x(T)=S_x(A_0\cup T)-S_x(A_0)\in U.
$$

($\Leftarrow$) Conversely, assume the disjoint-tail condition and let $U\in\mathcal N(0)$. Continuity of $(y,z)\mapsto z-y$ at $(0,0)$ supplies a $0$-neighborhood $V\in\mathcal N(0)$ such that $v_2-v_1\in U$ whenever $v_1,v_2\in V$ (`exists_nhds_half_neg`, the additive form of `exists_nhds_split_inv`). Choose $A_0\in\mathcal F(I)$ for $V$. Let $A,B\in\mathcal F(I)$ satisfy $A_0\subseteq A$ and $A_0\subseteq B$, and put $s=A\cap B$. Then $A_0\subseteq s$, while $A\setminus s$ and $B\setminus s$ are disjoint from $s$, hence disjoint from $A_0$: if $i\in(A\setminus s)\cap A_0$, then $i\in A_0\subseteq B$ and $i\in A$, contradicting $i\notin A\cap B$. Partitioning $A=(A\setminus s)\sqcup s$ and $B=(B\setminus s)\sqcup s$ cancels the shared core $S_x(s)$:
$$
 S_x(B)-S_x(A)=\bigl(S_x(B\setminus s)+S_x(s)\bigr)-\bigl(S_x(A\setminus s)+S_x(s)\bigr)=S_x(B\setminus s)-S_x(A\setminus s).
$$
By choice of $A_0$, both $S_x(A\setminus s)$ and $S_x(B\setminus s)$ lie in $V$, so their difference lies in $U$.

(2) Every `SeminormedAddCommGroup E` is an `IsUniformAddGroup` (`SeminormedAddCommGroup.to_isUniformAddGroup`), and the open balls $B(0,\varepsilon)=\{v\in E:\lVert v\rVert<\varepsilon\}$ ($\varepsilon>0$) form a basis of $\mathcal N(0)$ (`Metric.nhds_basis_ball`). Rewriting (1) along this basis gives (2). (Directly in norms, the neighborhood-halving step is simply $V=B(0,\varepsilon/2)$ with the triangle inequality $\lVert S_x(B\setminus s)-S_x(A\setminus s)\rVert\le\lVert S_x(B\setminus s)\rVert+\lVert S_x(A\setminus s)\rVert<\varepsilon/2+\varepsilon/2=\varepsilon$.)

(3) Since $g:I\to\mathbb R$ is summable, its partial sums converge in $\mathbb R$, hence form a Cauchy net (`Tendsto.cauchy_map` in `summable_iff_cauchySeq_finset.mp`). Given $\varepsilon>0$, part (2) applied to $g$ in $\mathbb R$ yields $A_1\in\mathcal F(I)$ such that $\lvert\sum_{i\in T}g(i)\rvert<\varepsilon$ whenever $T\cap A_1=\emptyset$. Because $E_0=\{i\in I:\lVert x_i\rVert>g(i)\}$ is finite, $A_0=A_1\cup E_0$ belongs to $\mathcal F(I)$. For any finite $T\subseteq I$ disjoint from $A_0$, every $i\in T$ satisfies $i\notin E_0$, so $0\le\lVert x_i\rVert\le g(i)$, and $T\cap A_1=\emptyset$. By the finite triangle inequality (`norm_sum_le`),
$$
 \Bigl\lVert\sum_{i\in T}x_i\Bigr\rVert\le\sum_{i\in T}\lVert x_i\rVert\le\sum_{i\in T}g(i)=\Bigl\lvert\sum_{i\in T}g(i)\Bigr\rvert<\varepsilon,
$$
and part (2) concludes that $S_x$ is Cauchy along `atTop`. When $\lVert x_i\rVert\le g(i)$ everywhere, $E_0=\emptyset$ gives `cauchySeq_finset_of_norm_bounded`. $\square$

[Lean, read] [InfiniteSum/Group.lean:211–234](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Group.lean#L211-L234) · [IsUniformGroup/Defs.lean:143–145](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/IsUniformGroup/Defs.lean#L143-L145) · [Group/Basic.lean:785–791](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/Group/Basic.lean#L785-L791) · [Normed/Group/Uniform.lean:382–384](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/Uniform.lean#L382-L384) · [Normed/Group/InfiniteSum.lean:46–76](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/InfiniteSum.lean#L46-L76)

**Lemma 2 (reindexing invariance, sharp countable-support conditions, and sequential evaluation).** Let $I,J$ be arbitrary index sets.

1. *Injective extension by zero and support bijections (`SummationFilter.comap_unconditional`, `Function.Injective.hasSum_iff`, `hasSum_subtype_support`, `Equiv.hasSum_iff_of_support`).* Let $M$ be a commutative topological monoid, $x:I\to M$, and $a\in M$.
   - If $g:J\to I$ is injective and $\operatorname{supp}(x)=\{i\in I:x_i\ne0\}\subseteq\operatorname{range}(g)$, then
     $$
      \mathrm{HasSum}(x\circ g,a)\iff\mathrm{HasSum}(x,a).
     $$
   - In particular, $\mathrm{HasSum}(x,a)\iff\mathrm{HasSum}(x\vert_{\operatorname{supp}(x)},a)$, and if $y:J\to M$ admits a bijection $e:\operatorname{supp}(x)\xrightarrow{\sim}\operatorname{supp}(y)$ with $y_{e(i)}=x_i$ for all $i\in\operatorname{supp}(x)$, then $\mathrm{HasSum}(x,a)\iff\mathrm{HasSum}(y,a)$.
2. *Cofinite vanishing and countable support (`Summable.vanishing`, `Summable.tendsto_cofinite_zero`, `Summable.hasFiniteSupport_of_discreteTopology`, `Summable.countable_support`).* Let $G$ be a commutative topological group and $x:I\to G$ be unconditionally summable (or, if $G$ is an `IsUniformAddGroup`, merely satisfy the finset-Cauchy condition of Lemma 1(1)).
   - For every $U\in\mathcal N(0)$, the set $\{i\in I:x_i\notin U\}$ is finite, i.e. $x_i\to0$ along the cofinite filter on $I$. If $G$ carries the discrete topology, $\operatorname{supp}(x)$ is finite.
   - Assume in addition that $G$ is **first-countable** (`[FirstCountableTopology G]`) and **$T_1$** (`[T1Space G]`) — both of which hold automatically in every `NormedAddCommGroup` without any separability or countable-index hypothesis. Then $\operatorname{supp}(x)=\{i\in I:x_i\ne0\}$ is **countable**.
3. *Enumeration independence (`HasSum.tendsto_sum_nat`).* Let $M$ be a commutative topological monoid, $x:I\to M$, and $\mathrm{HasSum}(x,a)$. If $\operatorname{supp}(x)$ is countably infinite, then for **every** bijection $\sigma:\mathbb N\xrightarrow{\sim}\operatorname{supp}(x)$,
   $$
    \lim_{N\to\infty}\sum_{k=0}^{N-1}x_{\sigma(k)}=a.
   $$
   If $\operatorname{supp}(x)$ is finite, then $\mathrm{HasSum}(x,\sum_{i\in\operatorname{supp}(x)}x_i)$ holds unconditionally, and if $M$ is $T_2$ (`[T2Space M]`) then $a=\sum_{i\in\operatorname{supp}(x)}x_i$.

**Proof.** (1) First check that for any injective $g:J\to I$, pulling back `atTop` on $\mathcal F(I)$ along $F'\mapsto g^{-1}(F')$ recovers `atTop` on $\mathcal F(J)$ (`SummationFilter.comap_unconditional`). Because $g$ is injective, $g^{-1}(F')\in\mathcal F(J)$ is well-defined (`Finset.preimage`), and for any $E\in\mathcal F(J)$ and $F'\in\mathcal F(I)$ we have the exact order adjunction
$$
 g(E)\subseteq F'\iff E\subseteq g^{-1}(F'),
$$
since $j\in E\implies g(j)\in g(E)\subseteq F'\implies j\in g^{-1}(F')$, while conversely $g(j)\in g(E)$ and $E\subseteq g^{-1}(F')$ give $j\in g^{-1}(F')$, hence $g(j)\in F'$. Thus the preimage of the principal ray $\mathcal R(E)$ on $\mathcal F(J)$ contains $\mathcal R(g(E))$ on $\mathcal F(I)$, giving $\mathrm{map}(g^{-1},\mathrm{atTop}_I)\le\mathrm{atTop}_J$. Notice that the reverse inequality uses only injectivity of $g$, with no range assumption (`SummationFilter.lean:180–190`): if $P\subseteq\mathcal F(J)$ satisfies $(g^{-1})^{-1}(P)\in\mathrm{atTop}_I$, pick $A_0\in\mathcal F(I)$ such that $A_0\subseteq F'\implies g^{-1}(F')\in P$; then for every $E'\supseteq g^{-1}(A_0)$ in $\mathcal F(J)$, setting $F'=A_0\cup g(E')\supseteq A_0$ yields $g^{-1}(F')=g^{-1}(A_0)\cup E'=E'$ by injectivity of $g$, so $E'\in P$. Hence $\mathrm{map}(g^{-1},\mathrm{atTop}_I)=\mathrm{atTop}_J$ unconditionally for every injective $g$.

Now compare the partial sums $S_{x\circ g}(g^{-1}(F'))$ and $S_x(F')$ (`Function.Injective.hasSum_comap_iff`). By injectivity, $g$ restricts to a bijection $g^{-1}(F')\xrightarrow{\sim}F'\cap\operatorname{range}(g)$, so $S_{x\circ g}(g^{-1}(F'))=\sum_{i\in F'\cap\operatorname{range}(g)}x_i$. Because $\operatorname{supp}(x)\subseteq\operatorname{range}(g)$, every $i\in F'\setminus\operatorname{range}(g)$ has $x_i=0$, hence $\sum_{i\in F'\cap\operatorname{range}(g)}x_i=\sum_{i\in F'}x_i=S_x(F')$. Composing $S_x$ with $\mathrm{map}(g^{-1},\mathrm{atTop}_I)=\mathrm{atTop}_J$ gives $\mathrm{map}(S_{x\circ g},\mathrm{atTop}_J)=\mathrm{map}(S_x,\mathrm{atTop}_I)$, whence $\mathrm{HasSum}(x\circ g,a)\iff\mathrm{HasSum}(x,a)$ (`Function.Injective.hasSum_iff`). Applying this to the subtype inclusion $\iota:\operatorname{supp}(x)\hookrightarrow I$ gives `hasSum_subtype_support`, and transporting between $\operatorname{supp}(x)$ and $\operatorname{supp}(y)$ along the bijection $e$ (`Equiv.hasSum_iff`) gives `Equiv.hasSum_iff_of_support`.

(2) First suppose $\mathrm{HasSum}(x,a)$ holds in a commutative topological group $G$ (without assuming `IsUniformAddGroup`), and let $U\in\mathcal N(0)$ (`Summable.vanishing`). Continuity of $(u,v)\mapsto u-v$ at $(a,a)$ yields $W\in\mathcal N(a)$ such that $w_1-w_2\in U$ for all $w_1,w_2\in W$. Pick $A_0\in\mathcal F(I)$ such that $S_x(F)\in W$ whenever $A_0\subseteq F$. For any finite $T\subseteq I$ with $T\cap A_0=\emptyset$, both $S_x(A_0\cup T)$ and $S_x(A_0)$ lie in $W$, so $S_x(T)=S_x(A_0\cup T)-S_x(A_0)\in U$ (if instead $G$ is an `IsUniformAddGroup` and $S_x$ is finset-Cauchy, Lemma 1(1) gives the same $A_0$ directly without $a$). Specializing to singleton sets $T=\{i\}$ for $i\notin A_0$ (`Summable.tendsto_cofinite_zero`) shows that $x_i=S_x(\{i\})\in U$ for all $i\notin A_0$; hence $\{i\in I:x_i\notin U\}\subseteq A_0$ is finite. If $G$ is discrete, $\{0\}\in\mathcal N(0)$, so $\operatorname{supp}(x)=\{i\in I:x_i\notin\{0\}\}$ is finite (`hasFiniteSupport_of_discreteTopology`).

Now assume `[FirstCountableTopology G]` and `[T1Space G]` (`Summable.countable_support`). By first-countability at $0$, $\mathcal N(0)$ admits a countable neighborhood basis $(U_n)_{n\in\mathbb N}$ (`IsCountablyGenerated.exists_antitone_basis`). By the $T_1$ separation axiom, for every $g\ne0$ in $G$ the complement $G\setminus\{g\}$ is an open neighborhood of $0$, so the filter kernel of $\mathcal N(0)$ reduces to $\{0\}$ (`ker_nhds`):
$$
 \bigcap_{n=0}^{\infty}U_n=\bigcap_{U\in\mathcal N(0)}U=\{0\}.
$$
Taking complements in $G$ and pulling back along $x:I\to G$ (`Tendsto.countable_compl_preimage_ker` via `countable_compl_ker`) writes the support of $x$ as a countable union:
$$
 \operatorname{supp}(x)=I\setminus x^{-1}(\{0\})=\bigcup_{n=0}^{\infty}\{i\in I:x_i\notin U_n\}.
$$
By the cofinite limit just proved, each set $\{i\in I:x_i\notin U_n\}$ is finite; a countable union of finite sets is countable.

(3) Suppose $\mathrm{HasSum}(x,a)$. If $\operatorname{supp}(x)$ is countably infinite and $\sigma:\mathbb N\xrightarrow{\sim}\operatorname{supp}(x)$ is any bijection, the composition $g=\iota\circ\sigma:\mathbb N\to I$ is injective with $\operatorname{range}(g)=\operatorname{supp}(x)$. Part (1) gives $\mathrm{HasSum}(x\circ g,a)$ on $\mathbb N$. Because `SummationFilter.conditional ℕ` refines `unconditional ℕ` (`SummationFilter.le_atTop`), monotonicity along filters (`HasSum.mono_filter`, wrapped as `HasSum.tendsto_sum_nat`) yields $\lim_{N\to\infty}\sum_{k\in\mathrm{range}\,N}x_{\sigma(k)}=a$. If $\operatorname{supp}(x)=F_0$ is finite, then $S_x(F)=S_x(F_0)$ for all $F\supseteq F_0$, and if $M$ is $T_2$ this constant tail forces $a=S_x(F_0)$ (`hasSum_fintype` + `HasSum.unique`; in general $\mathrm{HasSum}(x,S_x(F_0))$ always holds). $\square$

[Lean, read] [SummationFilter.lean:180–190](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.lean#L180-L190) · [InfiniteSum/Defs.lean:221–244](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean#L221-L244) · [InfiniteSum/Basic.lean:125–126](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean#L125-L126) · [InfiniteSum/Basic.lean:183–215](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean#L183-L215) · [InfiniteSum/Group.lean:330–390](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Group.lean#L330-L390) · [Cofinite.lean:138–147](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/Filter/Cofinite.lean#L138-L147) · [CountablyGenerated.lean:138–141](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/Filter/CountablyGenerated.lean#L138-L141) · [Separation/Basic.lean:633–634](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Separation/Basic.lean#L633-L634) · [NatInt.lean:48–50](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean#L48-L50)

**Theorem 3 (Banach filter completeness, norm-summability production, closed isometric ranges, and `HasSum` transport).** Let $I$ be any index set.

1. *Filter completeness gate and finite-tail equivalence (`cauchy_map_iff_exists_tendsto`, `UniformSpace.complete_of_cauchySeq_tendsto`, `summable_iff_cauchySeq_finset`, `summable_iff_vanishing_norm`).*
   - In any complete uniform additive group $G$ (`[AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]`), an $I$-indexed family $x:I\to G$ is unconditionally summable if and only if $F\mapsto S_x(F)$ is Cauchy along `atTop`, if and only if the finite-tail vanishing criterion of Lemma 1(1) holds (`summable_iff_vanishing`).
   - In any metric or Banach space $E$ (`[NormedAddCommGroup E] [CompleteSpace E]`), sequential Cauchy completeness of $\mathbb N$-indexed sequences already implies `CompleteSpace E` for **all** Cauchy filters (`UniformSpace.complete_of_cauchySeq_tendsto`), and for every $x:I\to E$,
     $$
      \mathrm{Summable}(x)\iff\forall\varepsilon>0,\;\exists A_0\in\mathcal F(I),\;\forall T\in\mathcal F(I),\;T\cap A_0=\emptyset\implies\Bigl\lVert\sum_{i\in T}x_i\Bigr\rVert<\varepsilon.
     $$
2. *Banach comparison tests and norm bound (`Summable.of_norm_bounded`, `Summable.of_norm_bounded_eventually`, `Summable.of_norm`, `HasSum.norm_le_of_bounded`, `norm_tsum_le_tsum_norm`).* Let $E$ be a Banach space (`[NormedAddCommGroup E] [CompleteSpace E]`) and $x:I\to E$.
   - If $g:I\to\mathbb R$ is summable in $\mathbb R$ and $\{i\in I:\lVert x_i\rVert>g(i)\}$ is finite (in particular if $\lVert x_i\rVert\le g(i)$ for all $i\in I$, or if $g(i)=\lVert x_i\rVert$ is summable in $\mathbb R$), then $x$ is unconditionally summable in $E$.
   - Without completeness, in any `SeminormedAddCommGroup`, if $\mathrm{HasSum}(x,a)$ and $\mathrm{HasSum}(g,b)$ (in $\mathbb R$) satisfy $\lVert x_i\rVert\le g_i$ for all $i\in I$, then $\lVert a\rVert\le b$ (`HasSum.norm_le_of_bounded`, and uniformly $\sum_{i\in F}\lVert x_i\rVert\le C$ for all $F\in\mathcal F(I)$ implies $\lVert a\rVert\le C$ via `le_of_tendsto' hx.norm`); if $\mathrm{Summable}(i\mapsto\lVert x_i\rVert)$ holds in $\mathbb R$, then $\lVert\sum'_{i\in I}x_i\rVert\le\sum'_{i\in I}\lVert x_i\rVert$ unconditionally in any `NormedAddCommGroup`.
3. *Continuous-linear vs. closed-embedding transport and closed isometric ranges (`HasSum.map`, `ContinuousLinearMap.hasSum`, `ContinuousLinearMap.map_tsum`, `IsClosedEmbedding.map_tsum`, `IsUniformInducing.isComplete_range`, `IsComplete.isClosed`).*
   - For any continuous additive monoid homomorphism (in particular any continuous linear map $T:E\to_L F$ between topological modules, requiring **no** completeness), $\mathrm{HasSum}(x,a,L)\implies\mathrm{HasSum}(T\circ x,T(a),L)$; if $E,F$ are $T_2$ and $\mathrm{Summable}(x)$, then $T\bigl(\sum'_{i\in I}x_i\bigr)=\sum'_{i\in I}T(x_i)$.
   - If $\iota:G\to H$ is an additive closed embedding between $T_2$ commutative topological monoids, then $\iota\bigl(\sum'_{i\in I}x_i\bigr)=\sum'_{i\in I}\iota(x_i)$ holds **without** assuming $\mathrm{Summable}(x)$. Moreover, every uniform-inducing map (in particular every linear isometry) from a `CompleteSpace` into a $T_0$ uniform space has complete, hence closed, range (`IsUniformInducing.isComplete_range`, `IsComplete.isClosed`).
4. *Exact payment to `l2Space` and the Chapter 1–2 consumers.* Let $H$ be a complete inner product space over $\mathbb K\in\{\mathbb R,\mathbb C\}$.
   - For an orthogonal family $(V_i)_{i\in I}$ of linear isometries $V_i:G_i\to H$ and $f\in\prod_{i\in I}G_i$, rewriting both sides with (1) (`summable_iff_cauchySeq_finset`) proves $\mathrm{Summable}(i\mapsto V_i(f_i))\iff\mathrm{Summable}(i\mapsto\lVert f_i\rVert^2)$ (`OrthogonalFamily.summable_iff_norm_sq_summable`), constructing `OrthogonalFamily.linearIsometry` and `hasSum_linearIsometry`, while (3) closes $\operatorname{range}(hV.\mathrm{linearIsometry})$ (`range_linearIsometry`).
   - For a `HilbertBasis` $b$ of $H$, transporting `lp.hasSum_single` ($f=\sum_{i\in I}\mathrm{single}_2(i,f_i)$ in $\ell^2(I,\mathbb K)$) through the continuous linear equivalence $b.\mathrm{repr}.\mathrm{symm}$ via (3) produces $\mathrm{HasSum}(i\mapsto f_i b_i, b.\mathrm{repr}.\mathrm{symm}(f))$ (`hasSum_repr_symm`) and $\mathrm{HasSum}(i\mapsto\langle b_i,y\rangle b_i,y)$ (`hasSum_repr`); applying (3) with $T=\langle x,\cdot\rangle$ yields $\mathrm{HasSum}(i\mapsto\langle x,b_i\rangle\langle b_i,y\rangle,\langle x,y\rangle)$ (`hasSum_inner_mul_inner`), and when $I=\mathbb N$, monotonicity along `SummationFilter.le_atTop` turns $b$ into a sequential `SchauderBasis` (`toSchauderBasis`).

**Proof.** (1) By definition (`Cauchy.lean:370–372`), `[CompleteSpace G]` asserts that for every Cauchy filter $\mathcal G$ on $G$ there exists $a\in G$ with $\mathcal G\le\mathcal N(a)$ (`CompleteSpace.complete`). Conversely, for any $a\in G$, the neighborhood filter $\mathcal N(a)$ is Cauchy (`cauchy_nhds`, because every entourage $W\in\mathcal U$ contains a symmetric $W'\in\mathcal U$ with $W'\circ W'\subseteq W$, and $W'[a]\in\mathcal N(a)$ satisfies $W'[a]\times W'[a]\subseteq W$), so any proper filter $\mathcal G\le\mathcal N(a)$ is Cauchy (`Tendsto.cauchy_map`). Applying this equivalence (`cauchy_iff_exists_le_nhds`) to the pushforward filter $\mathcal G=\mathrm{map}(S_x,\mathrm{atTop})$ yields `cauchy_map_iff_exists_tendsto`:
$$
 \mathrm{Cauchy}\bigl(\mathrm{map}(S_x,\mathrm{atTop})\bigr)\iff\exists a\in G,\;\mathrm{Tendsto}(S_x,\mathrm{atTop},\mathcal N(a)),
$$
whose symmetric form is literally `summable_iff_cauchySeq_finset`. Combining with Lemma 1(1)–(2) gives `summable_iff_vanishing` and `summable_iff_vanishing_norm`.

Why does ordinary sequential completeness of $\mathbb N$-indexed Cauchy sequences suffice to inhabit `[CompleteSpace E]` in a metric or normed space (`UniformSpace.complete_of_cauchySeq_tendsto`)? In any pseudometric space, the uniformity $\mathcal U$ has the countable antitone basis $W_n=\{(u,v):d(u,v)<2^{-n}\}$ ($n\in\mathbb N$). Given an arbitrary Cauchy filter $\mathcal G$ on $E$ (such as $\mathrm{map}(S_x,\mathrm{atTop})$ for uncountable $I$), pick $P_n\in\mathcal G$ with $P_n\times P_n\subseteq W_n$, replace $P_n$ by the descending chain $Q_n=\bigcap_{k\le n}P_k\in\mathcal G$ (nonempty because $\mathcal G\ne\bot$), and select one point $u_n\in Q_n$ for each $n\in\mathbb N$. For $m\ge n$, both $u_m$ and $u_n$ lie in $Q_n\subseteq P_n$, so $d(u_n,u_m)<2^{-n}$; hence $(u_n)_{n\in\mathbb N}$ is a Cauchy sequence in $E$, which by sequential completeness converges to some $a\in E$. Now let $V\in\mathcal N(a)$ contain $B(a,\varepsilon)$, choose $n$ with $2^{-n}<\varepsilon/2$ and $d(u_n,a)<\varepsilon/2$; for every $y\in Q_n$, $(u_n,y)\in W_n$ gives $d(y,a)\le d(y,u_n)+d(u_n,a)<2^{-n}+\varepsilon/2<\varepsilon$, so $Q_n\subseteq B(a,\varepsilon)\subseteq V$, proving $\mathcal G\le\mathcal N(a)$.

(2) Combining (1) (`summable_iff_cauchySeq_finset.mpr`) with Lemma 1(3) (`cauchySeq_finset_of_norm_bounded_eventually` and `cauchySeq_finset_of_norm_bounded`) immediately proves `Summable.of_norm_bounded_eventually` and `Summable.of_norm_bounded`; specializing $g(i)=\lVert x_i\rVert$ gives `Summable.of_norm` (`exact .of_norm_bounded h fun _ ↦ le_rfl`). For the norm bounds, if $\mathrm{HasSum}(x,a)$ and $\mathrm{HasSum}(g,b)$ satisfy $\lVert x_i\rVert\le g_i$, then $\lVert S_x(F)\rVert\le S_g(F)$ everywhere and `le_of_tendsto_of_tendsto' hx.norm hg` gives $\lVert a\rVert\le b$ (`HasSum.norm_le_of_bounded`; likewise $\sum_{i\in F}\lVert x_i\rVert\le C$ gives $\lVert a\rVert\le C$ via `le_of_tendsto' hx.norm`). When $h:\mathrm{Summable}(i\mapsto\lVert x_i\rVert)$ holds in $\mathbb R$ (`norm_tsum_le_tsum_norm`), nonnegativity of norms gives $\sum_{i\in F}\lVert x_i\rVert\le\sum'_{i\in I}\lVert x_i\rVert$ for every $F$; if $\mathrm{Summable}(x)$ holds in $E$, applying the finite-subtotal bound to `hx.hasSum` yields $\lVert\sum'_{i\in I}x_i\rVert\le\sum'_{i\in I}\lVert x_i\rVert$, whereas if $\neg\mathrm{Summable}(x)$ (which can happen when $E$ is incomplete!), Lean defines $\sum'_{i\in I}x_i=0$ and $0\le\sum'_{i\in I}\lVert x_i\rVert$ holds trivially (`tsum_nonneg`).

(3) Let $T:E\to F$ be a continuous additive homomorphism (`HasSum.map`, specialized to `ContinuousLinearMap.hasSum` / `HasSum.mapL`). For every $F_0\in\mathcal F(I)$, additivity gives $T(S_x(F_0))=\sum_{i\in F_0}T(x_i)=S_{T\circ x}(F_0)$ (`map_sum`). Composing `Tendsto S_x L (𝓝 a)` with `Continuous.tendsto T a` yields `Tendsto (T ∘ S_x) L (𝓝 (T a))`, which is $\mathrm{HasSum}(T\circ x,T(a),L)$. When $E,F$ are $T_2$ and $hx:\mathrm{Summable}(x)$, `hx.hasSum` gives $\mathrm{HasSum}(x,\sum'_i x_i)$, its image under $T$ gives $\mathrm{HasSum}(T\circ x,T(\sum'_i x_i))$, and `HasSum.tsum_eq` gives $\sum'_i T(x_i)=T(\sum'_i x_i)$ (`ContinuousLinearMap.map_tsum`).

Now let $\iota:G\to H$ be an additive closed embedding between $T_2$ topological monoids (`Topology.IsClosedEmbedding.map_tsum`). If $\mathrm{Summable}(x)$ holds in $G$, the previous paragraph already gives $\iota(\sum'_i x_i)=\sum'_i\iota(x_i)$. Suppose $\neg\mathrm{Summable}(x)$ in $G$, so $\iota(\sum'_i x_i)=\iota(0)=0$. Could $\iota\circ x$ nevertheless be summable in $H$, say $\mathrm{HasSum}(\iota\circ x,b)$? Every partial sum $S_{\iota\circ x}(F)=\iota(S_x(F))$ belongs to $\operatorname{range}(\iota)$; because $\iota$ is a **closed** embedding, $\operatorname{range}(\iota)$ is closed in $H$, so its net limit $b$ must lie in $\operatorname{range}(\iota)$ (`mem_of_tendsto`), say $b=\iota(a)$ with $a\in G$. Because $\iota$ is a topological embedding (`tendsto_nhds_iff`), $\iota(S_x(F))\to\iota(a)$ in $H$ pulls back to $S_x(F)\to a$ in $G$, contradicting $\neg\mathrm{Summable}(x)$! Hence $\neg\mathrm{Summable}(\iota\circ x)$, so $\sum'_i\iota(x_i)=0=\iota(\sum'_i x_i)$ as well. Finally, if $\iota:G\to H$ is uniform-inducing (`IsUniformInducing`) and $G$ is complete, any Cauchy filter $\mathcal G$ supported on $\operatorname{range}(\iota)$ pulls back to a proper Cauchy filter $\iota^{-1}(\mathcal G)$ on $G$, which converges in $G$ to some $a$ and pushes forward to $\iota(a)\in\operatorname{range}(\iota)$ (`IsUniformInducing.isComplete_range`); in a $T_0$ uniform space, any cluster point $z$ of a complete subset $R$ makes the principal-restricted filter $\mathcal N(z)\sqcap\mathcal P(R)$ Cauchy, forcing a limit $y\in R$ equal to $z$ by separation (`IsComplete.isClosed`).

(4) In `Subspace.lean:198–239` (`OrthogonalFamily.summable_iff_norm_sq_summable`), both `Summable (fun i => V i (f i))` (in complete $H$) and `Summable (fun i => ‖f i‖ ^ 2)` (in complete $\mathbb R$) are rewritten by (1) (`summable_iff_cauchySeq_finset`). For any two finite sets $s_1,s_2\supseteq A_0$, setting $s=s_1\cap s_2$ makes $s_1\setminus s_2$ and $s_2\setminus s_1$ disjoint and pairwise orthogonal, so Pythagorean orthogonality (`hV.norm_sq_sdiff_sum`) gives
$$
 \Bigl\lVert\sum_{i\in s_1}V_i(f_i)-\sum_{i\in s_2}V_i(f_i)\Bigr\rVert^2=\sum_{i\in s_1\setminus s_2}\lVert f_i\rVert^2+\sum_{i\in s_2\setminus s_1}\lVert f_i\rVert^2,
$$
bounding $\lvert\sum_{i\in s_1}\lVert f_i\rVert^2-\sum_{i\in s_2}\lVert f_i\rVert^2\rvert<\varepsilon$ from $\sqrt{\varepsilon}$-Cauchyness of $V_i(f_i)$ in the forward direction, and bounding the vector difference below $\varepsilon$ from $(\varepsilon^2/2)$-Cauchyness of $\lVert f_i\rVert^2$ on $(s_1,s_1\cap s_2)$ and $(s_2,s_1\cap s_2)$ in the reverse direction. In `l2Space.lean:184–254`, `summable_of_lp` feeds `(lp.memℓp f).summable` into that equivalence, `linearIsometry` sets $hV.\mathrm{linearIsometry}(f)=\sum'_{i\in I}V_i(f_i)$ using `tsum_add` and `tsum_const_smul`, `hasSum_linearIsometry` calls `Summable.hasSum`, and `range_linearIsometry` closes the image at line 253 via `hV.linearIsometry.isometry.isUniformInducing.isComplete_range.isClosed`. In `l2Space.lean:429–515`, `lp.hasSum_single` (`lpSpace.lean:1174–1195`) establishes $\mathrm{HasSum}(i\mapsto\mathrm{single}_2(i,f_i),f)$ in $\ell^2(I,\mathbb K)$ from the tail identity $\lVert f-\sum_{i\in F}\mathrm{single}_2(i,f_i)\rVert_2^2=\sum'_{i\in I}\lvert f_i\rvert^2-\sum_{i\in F}\lvert f_i\rvert^2\to0$, `hasSum_repr_symm` (`:436`) applies `(b.repr.symm.toContinuousLinearEquiv : ℓ²(I, 𝕜) →L[𝕜] H).hasSum` from (3) and identifies $b.\mathrm{repr}.\mathrm{symm}(\mathrm{single}_2(i,f_i))=f_i b_i$, `hasSum_inner_mul_inner` (`:464`) applies `.mapL (innerSL 𝕜 x)` from (3) to `b.hasSum_repr y`, and `toSchauderBasis` (`:514`) applies `.mono_left SummationFilter.le_atTop`. $\square$

[Lean, read] [Cauchy.lean:78–86](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Cauchy.lean#L78-L86) · [Cauchy.lean:370–372](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Cauchy.lean#L370-L372) · [Cauchy.lean:424–435](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Cauchy.lean#L424-L435) · [Cauchy.lean:830–922](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Cauchy.lean#L830-L922) · [InfiniteSum/Group.lean:204–206](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Group.lean#L204-L206) · [InfiniteSum/Group.lean:259–262](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Group.lean#L259-L262) · [Normed/Group/InfiniteSum.lean:54–56](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/InfiniteSum.lean#L54-L56) · [Normed/Group/InfiniteSum.lean:111–151](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/InfiniteSum.lean#L111-L151) · [Normed/Group/InfiniteSum.lean:180–195](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/InfiniteSum.lean#L180-L195) · [InfiniteSum/Basic.lean:218–225](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean#L218-L225) · [InfiniteSum/Basic.lean:257–276](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean#L257-L276) · [InfiniteSum/Module.lean:122–152](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Module.lean#L122-L152) · [UniformEmbedding.lean:259–291](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/UniformEmbedding.lean#L259-L291) · [CompleteSeparated.lean:26–38](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/CompleteSeparated.lean#L26-L38) · [Subspace.lean:198–239](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Subspace.lean#L198-L239) · [l2Space.lean:184–254](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L184-L254) · [l2Space.lean:429–515](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L429-L515)

**Hand calculation A (an orthogonal family in $\ell^2(\mathbb N)$: unordered summable with divergent norm sum, versus ordered conditional convergence and finite-dimensional $\sqrt{d}$ blowup).** Work in the complete real Hilbert space $H=\ell^2(\mathbb N)$ with standard orthonormal basis $(e_n)_{n\ge0}$, and set
$$
 x_n=\frac{1}{n+1}\,e_n\qquad(n\in\mathbb N).
$$

1. *Norm summability fails (`Summable.of_norm` does not apply).* Since $\lVert x_n\rVert_2=(n+1)^{-1}$, partitioning $\mathbb N$ into dyadic blocks $B_k=\{2^k-1,\dots,2^{k+1}-2\}$ ($k\ge0$, of cardinality $2^k$) gives
$$
 \sum_{n\in B_k}\lVert x_n\rVert_2=\sum_{m=2^k}^{2^{k+1}-1}\frac{1}{m}\ge 2^k\cdot\frac{1}{2^{k+1}}=\frac{1}{2},
$$
so $\sum_{n=0}^{2^K-2}\lVert x_n\rVert_2\ge 1+\frac{K-1}{2}\to+\infty$ as $K\to\infty$ (already $H_8=\sum_{m=1}^{8}\frac{1}{m}=\frac{761}{280}>\frac{5}{2}$ and $H_{16}=\frac{2436559}{720720}>3$). Thus $n\mapsto\lVert x_n\rVert_2$ is not summable in $\mathbb R$, and `Summable.of_norm` cannot be invoked.

2. *Finite-tail Pythagoras check (`summable_iff_vanishing_norm` succeeds).* Given $\varepsilon>0$, pick an integer $N\ge1$ with $N>\varepsilon^{-2}$, and set $A_0=\{0,1,\dots,N-1\}\in\mathcal F(\mathbb N)$. Let $T\in\mathcal F(\mathbb N)$ be any finite set with $T\cap A_0=\emptyset$. If $T=\emptyset$, $\lVert S_x(T)\rVert_2=0<\varepsilon$. Otherwise let $M=\max T\ge N$; every $n\in T$ satisfies $N\le n\le M$, so $m=n+1$ satisfies $N+1\le m\le M+1$ with $m\ge2$. Because $(e_n)_{n\in T}$ are pairwise orthogonal, exact rational telescoping bounds the squared norm of $S_x(T)$ uniformly across all finite subsets $T$ avoiding $A_0$:
$$
 \Bigl\lVert\sum_{n\in T}x_n\Bigr\rVert_2^2=\sum_{n\in T}\frac{1}{(n+1)^2}\le\sum_{m=N+1}^{M+1}\frac{1}{m^2}<\sum_{m=N+1}^{M+1}\frac{1}{(m-1)m}=\frac{1}{N}-\frac{1}{M+1}<\frac{1}{N}<\varepsilon^2,
$$
whence $\lVert S_x(T)\rVert_2<\varepsilon$. Concretely, for $\varepsilon=1/2$, take $N=4$ and $A_0=\{0,1,2,3\}$, whose core energy is $\lVert S_x(A_0)\rVert_2^2=1+\frac14+\frac19+\frac{1}{16}=\frac{205}{144}$; on the disjoint five-element tail $T=\{4,5,6,7,8\}$,
$$
 \lVert S_x(T)\rVert_2^2=\frac{1}{25}+\frac{1}{36}+\frac{1}{49}+\frac{1}{64}+\frac{1}{81}=\frac{737641}{6350400}<\frac{1}{4}-\frac{1}{9}=\frac{5}{36}<\frac{1}{4},
$$
so $\lVert S_x(T)\rVert_2<1/2$ (and indeed the entire infinite tail $\frac{\pi^2}{6}-\frac{205}{144}\approx 0.22126<\frac14$). Because $\ell^2(\mathbb N)$ is complete (§1.2.2.8, Lemma 2), Theorem 3(1) produces the unordered sum $s=((n+1)^{-1})_{n\ge0}\in\ell^2(\mathbb N)$ with $\lVert s\rVert_2^2=\sum_{m=1}^\infty m^{-2}=\frac{\pi^2}{6}$, and Lemma 2(3) guarantees $\lim_{K\to\infty}\sum_{k=0}^{K-1}x_{\sigma(k)}=s$ in $\ell^2(\mathbb N)$ for **every** permutation $\sigma:\mathbb N\xrightarrow{\sim}\mathbb N$.

3. *Contrast with ordered conditional convergence on one coordinate axis.* Collapse the basis directions onto $e_0$ with alternating signs: $z_n=(-1)^n(n+1)^{-1}e_0$. Along `SummationFilter.conditional ℕ`, the alternating-series bound gives $\lVert S_z(\{0,\dots,M-1\})-S_z(\{0,\dots,N-1\})\rVert_2\le(N+1)^{-1}$ for $M\ge N$, so the ordered partial sums $S_{K}e_0=\bigl(\sum_{m=1}^{K}(-1)^{m-1}m^{-1}\bigr)e_0$ converge in $\ell^2(\mathbb N)$ to $(\log 2)e_0$. Yet $z$ fails Lemma 1(2): for **every** finite $A_0\subseteq\{0,\dots,N-1\}$, let $p=\max(1,\lceil N/2\rceil)$; the finite even-index set $T_+=\{2p,2p+2,\dots,8p-2\}$ is disjoint from $A_0$, carries exclusively positive signs $(-1)^{2j}=+1$, and satisfies
$$
 \lVert S_z(T_+)\rVert_2=\sum_{j=p}^{4p-1}\frac{1}{2j+1}>3p\cdot\frac{1}{8p}=\frac{3}{8}
$$
(even the six-element block $T_+=\{4,6,8,10,12,14\}$ outside $A_0=\{0,1,2,3\}$ already has $\lVert S_z(T_+)\rVert_2=\frac{1}{5}+\frac{1}{7}+\frac{1}{9}+\frac{1}{11}+\frac{1}{13}+\frac{1}{15}=\frac{31012}{45045}>\frac{1}{2}$). Correspondingly, Lemma 2(3) fails: taking two odd-denominator positive terms followed by one even-denominator negative term defines a bijection $\tau:\mathbb N\to\mathbb N$ whose $3m$-th partial sum $R_{3m}e_0$ satisfies the exact identity (using $H_{2m}-H_m=\sum_{k=1}^{2m}(-1)^{k-1}k^{-1}=S_{2m}$, where $H_r=\sum_{k=1}^r k^{-1}$)
$$
 R_{3m}=\sum_{j=1}^{2m}\frac{1}{2j-1}-\sum_{j=1}^{m}\frac{1}{2j}=\Bigl(\sum_{j=1}^{2m}\frac{1}{2j-1}-\sum_{j=1}^{2m}\frac{1}{2j}\Bigr)+\frac{1}{2}(H_{2m}-H_m)=S_{4m}+\frac{1}{2}S_{2m}
$$
(for $m=2$, $R_6=1+\frac13-\frac12+\frac15+\frac17-\frac14=\frac{389}{420}=\frac{533}{840}+\frac{1}{2}\cdot\frac{7}{12}=S_8+\frac12 S_4$), which converges to $\frac{3}{2}\log 2\,e_0\ne(\log 2)e_0$!

4. *Why §2.6.3.1's finite-dimensional converse does not contradict $(x_n)$.* In $\mathbb R^d$ with the Euclidean $\ell^2$ norm at $d=k^2$ ($k\ge1$), the $d$ orthogonal vectors $v_j=k^{-1}e_j$ ($0\le j<k^2$) satisfy $\lVert\sum_{j\in T}v_j\rVert_2=\sqrt{\lvert T\rvert/k^2}\le 1$ for **every** subset $T\subseteq\{0,\dots,k^2-1\}$, while $\sum_{j=0}^{k^2-1}\lVert v_j\rVert_2=k^2\cdot k^{-1}=k=\sqrt{d}$. In fixed finite dimension $d$, Cauchy–Schwarz bounds $\sum\lVert v_j\rVert_1\le\sqrt{d}\sum\lVert v_j\rVert_2$ and sign-quadrant splitting (§2.6.3.1) forces absolute convergence with dimensional loss $O(\sqrt{d})$; as $d=k^2\to\infty$ inside $\ell^2(\mathbb N)$, that factor $\sqrt{d}=k\to\infty$ diverges and allows $(x_n)$ to stay unconditionally summable while $\sum_n\lVert x_n\rVert_2=\infty$. [Expository]

**Hand calculation B (the same Cauchy family — and a norm-summable variant — in non-complete $c_{00}(\mathbb N)$: failure of `summable_iff_cauchySeq_finset`, failure of `Summable.of_norm`, and `tsum` non-commutation).** Now equip the finitely supported real sequence space $E_0=c_{00}(\mathbb N)$ (`ℕ →₀ ℝ`) with the $\ell^2$ norm $\lVert w\rVert_{E_0}=\bigl(\sum_{n\in\operatorname{supp}(w)}w_n^2\bigr)^{1/2}$ restricted from $\ell^2(\mathbb N)$. Every vector $x_n=(n+1)^{-1}e_n$ has singleton support $\{n\}$, hence belongs to $E_0$.

1. *The partial-sum net remains Cauchy in $E_0$.* Because $\lVert\cdot\rVert_{E_0}$ is the restriction of $\lVert\cdot\rVert_2$ to $E_0$, every finite sum $S_x(T)=\sum_{n\in T}x_n\in E_0$ has the exact same norm as in Hand calculation A(2): for $A_0=\{0,\dots,N-1\}$ and $T\cap A_0=\emptyset$, $\lVert S_x(T)\rVert_{E_0}<N^{-1/2}$. By Lemma 1(2) (which needed no completeness!), `CauchySeq (fun F : Finset ℕ => ∑ n ∈ F, x n)` **still holds in $E_0$**.

2. *No unordered limit exists in $E_0$ (`summable_iff_cauchySeq_finset` fails without `[CompleteSpace]`).* Let $w\in E_0$ be **any** candidate vector. Because $\operatorname{supp}(w)\subset\mathbb N$ is finite, choose $m\in\mathbb N\setminus\operatorname{supp}(w)$ (take $m=0$ if $w=0$, and $m=1+\max\operatorname{supp}(w)$ otherwise), so $w_m=0$, and set $\varepsilon_w=(m+1)^{-1}>0$. Given **any** proposed finite threshold $F_0\in\mathcal F(\mathbb N)$, form $F=F_0\cup\{m\}\in\mathcal F(\mathbb N)$. Then $F_0\subseteq F$ and $m\in F$, so $(S_x(F))_m=(m+1)^{-1}$ while $w_m=0$, giving
$$
 \lVert S_x(F)-w\rVert_{E_0}^2=\sum_{n=0}^{\infty}\bigl((S_x(F))_n-w_n\bigr)^2\ge\bigl((m+1)^{-1}-0\bigr)^2=\frac{1}{(m+1)^2}=\varepsilon_w^2.
$$
Hence $\lVert S_x(F)-w\rVert_{E_0}\ge\varepsilon_w$, refuting $\mathrm{HasSum}(x,w)$ for every $w\in E_0$. For instance, testing the four-term truncation $w^{(4)}=e_0+\frac12 e_1+\frac13 e_2+\frac14 e_3\in E_0$ ($\operatorname{supp}(w^{(4)})=\{0,1,2,3\}$) gives $m=4$ and $\varepsilon_{w^{(4)}}=1/5$; already at $F=\{0,1,2,3,4,5\}$, $\lVert S_x(F)-w^{(4)}\rVert_{E_0}^2=\frac{1}{25}+\frac{1}{36}=\frac{61}{900}>\frac{1}{25}=\varepsilon_{w^{(4)}}^2$. Thus $x$ is finset-Cauchy in $E_0$ yet **not** `Summable` in $E_0$.

3. *Deleting `[CompleteSpace]` also breaks `Summable.of_norm` and `map_tsum`.* Replace $x_n$ by $y_n=2^{-(n+1)}e_n\in E_0$. Now $y$ is **norm-summable**:
$$
 \sum_{n=0}^{\infty}\lVert y_n\rVert_{E_0}=\sum_{n=0}^{\infty}2^{-(n+1)}=1<\infty\quad\text{in }\mathbb R.
$$
Yet for any $w\in E_0$ and $m\in\mathbb N\setminus\operatorname{supp}(w)$, every $F=F_0\cup\{m\}\supseteq F_0$ satisfies $\lVert S_y(F)-w\rVert_{E_0}\ge 2^{-(m+1)}>0$ (for $w=\frac12 e_0+\frac14 e_1+\frac18 e_2+\frac{1}{16}e_3$, $m=4$ gives lower bound $1/32$, and at $F=\{0,1,2,3,4,5\}$, $\lVert S_y(F)-w\rVert_{E_0}^2=2^{-10}+2^{-12}=\frac{5}{4096}>\frac{1}{1024}=(1/32)^2$). Thus $\neg\mathrm{Summable}(y)$ in $E_0$, and Lean's total `tsum` assigns $\sum'_{n\in\mathbb N}y_n=0\in E_0$ (`tsum_eq_zero_of_not_summable`, satisfying `norm_tsum_le_tsum_norm` via $0\le 1$). Now apply two continuous linear maps out of $E_0$:
   - Define the bounded linear functional $\Lambda:E_0\to\mathbb R$, $\Lambda(w)=\sum_{n\in\operatorname{supp}(w)}2^{-(n+1)}w_n$ (by Cauchy–Schwarz, $\lvert\Lambda(w)\rvert^2\le\bigl(\sum_{n\ge0}4^{-(n+1)}\bigr)\lVert w\rVert_{E_0}^2=\frac{1}{3}\lVert w\rVert_{E_0}^2$, so $\lVert\Lambda\rVert\le 1/\sqrt3$). In $E_0$, $\Lambda\bigl(\sum'_{n\in\mathbb N}y_n\bigr)=\Lambda(0)=0$; in the **complete** target $\mathbb R$, however, $\Lambda(y_n)=4^{-(n+1)}$ is summable with $\sum'_{n\in\mathbb N}\Lambda(y_n)=\sum_{n=0}^\infty 4^{-(n+1)}=\frac{1}{3}\ne0$! This is why `ContinuousLinearMap.map_tsum` in Theorem 3(3) requires the explicit hypothesis `Summable y`.
   - Likewise, for the linear isometry $\iota:E_0\hookrightarrow\ell^2(\mathbb N)$ (whose image $c_{00}(\mathbb N)$ is dense and **not closed** in $\ell^2(\mathbb N)$ because $E_0$ is incomplete), $\iota\bigl(\sum'_{n\in\mathbb N}y_n\bigr)=\iota(0)=0\ne(2^{-(n+1)})_{n\ge0}=\sum'_{n\in\mathbb N}\iota(y_n)$, isolating why `IsClosedEmbedding.map_tsum` in Theorem 3(3) requires closed range — and why `l2Space.lean:253` uses `[CompleteSpace]` on $\ell^2(I,\mathbb K)$ to close the range of `linearIsometry`! [Expository]

**Hypothesis-deletion counterexamples for Lemma 2 (sharpness of `[FirstCountableTopology G]`, `[T1Space G]`, and support containment).** Each hypothesis in Lemma 2(1)–(2) is sharp:

1. *Deleting `[FirstCountableTopology G]` while keeping Hausdorff (`[T2Space G]`) and `[CompleteSpace G]`.* Let $G=\mathbb R^{\mathbb R}$ be the uncountable Cartesian product of copies of $\mathbb R$ equipped with the product topology and product uniformity. Then $G$ is a Hausdorff, complete topological additive group, but not first-countable at $0$. For each $r\in\mathbb R$, define the coordinate indicator $e_r\in G$ by $e_r(t)=1$ if $t=r$ and $0$ otherwise, and let $\mathbf 1\in G$ be the constant function $\mathbf 1(t)=1$. Any basic neighborhood of $\mathbf 1$ in the product topology has the form $U_{K,\varepsilon}=\{f\in G:\forall t\in K,\;\lvert f(t)-1\rvert<\varepsilon\}$ for a **finite** subset $K\in\mathcal F(\mathbb R)$ and $\varepsilon>0$. Choosing $A_0=K\in\mathcal F(\mathbb R)$, every finite $F\supseteq K$ satisfies $(S_e(F))(t)=\sum_{r\in F}e_r(t)=1$ for all $t\in K$, so $S_e(F)\in U_{K,\varepsilon}$. Thus $\mathrm{HasSum}(e,\mathbf 1)$ holds in $G$, yet $\operatorname{supp}(e)=\mathbb R$ is uncountable.
2. *Deleting `[T1Space G]` while keeping `[SeminormedAddCommGroup G]`, `[FirstCountableTopology G]`, and `[CompleteSpace G]`.* Equip $G=\mathbb R$ with the identically zero seminorm $\lVert v\rVert_0=0$. Its topology is indiscrete (first-countable with basis $\{G\}$, complete because every point is a limit, and not $T_1$ because $\bigcap_{U\in\mathcal N(0)}U=G\ne\{0\}$). The constant nonzero family $x_r=1$ ($r\in\mathbb R$) satisfies $\lVert S_x(F)-0\rVert_0=0<\varepsilon$ for every $\varepsilon>0$ and every $F\in\mathcal F(\mathbb R)$, so $\mathrm{HasSum}(x,0)$ holds with uncountable support $\operatorname{supp}(x)=\mathbb R$.
3. *Deleting $\operatorname{supp}(x)\subseteq\operatorname{range}(g)$ in Lemma 2(1).* Take $I=\{0,1\}$, $J=\{0\}$, the injection $g:J\to I$ with $g(0)=0$, and $x=(1,2):I\to\mathbb R$. Then $\mathrm{HasSum}(x\circ g,1)$ holds on $J$, whereas $\mathrm{HasSum}(x,3)$ holds on $I$ ($1\ne3$) because the nonzero index $1\in\operatorname{supp}(x)$ lies outside $\operatorname{range}(g)$. [Expository]

**Remarks.**

1. *Bourbaki's unordered nets, Carneiro's `df-tsms`, and Loeffler's `SummationFilter`.* Mathlib's `InfiniteSum/Defs.lean` (`:49`, `:96`) explicitly models unordered infinite sums over an arbitrary index type $I$ without any linear order after Bourbaki's *General Topology*, Ch. III, §5 (`[BourbakiGT1]`) and Mario Carneiro's Metamath definition `df-tsms` (`[CarneiroMetamath]`, which defines the set of all net limits along directed finite-subset inclusion, whereas Mathlib's `tsum` adds a classical-choice default to $0$ outside its convergence domain). David Loeffler's `SummationFilter` abstraction (`SummationFilter.lean`, 2025) then parameterizes `HasSum f a L` by $L$ so that unordered convergence (`unconditional I`, the default) and ordered Schauder-basis or conditionally convergent series (`conditional ℕ`, `l2Space.lean:510–515`) share one library without duplicating linearity or continuity lemmas.
2. *Finite-dimensional equivalence versus Dvoretzky–Rogers (1950).* In $\mathbb C$ ([Chapter 2, §2.6](02-functional-equations-and-primitive-characters.md#26-lean-counterpart-for-this-chapter), §2.6.3.1) and in every finite-dimensional normed space (`[DvoretzkyRogers1950]`, p. 192; cf. Lebl `[LeblBasicAnalysis]`, §2.6 for one real dimension), splitting coordinates into signed quadrants upgrades unordered `HasSum` to norm summability $\sum_i\lVert x_i\rVert<\infty$. Hand calculation A shows why this converse fails in $\ell^2(\mathbb N)$, and the Dvoretzky–Rogers theorem (`[DvoretzkyRogers1950]`, Theorem 1, pp. 192–193) proves that **every** infinite-dimensional Banach space contains a sequence $(x_n)$ that is unconditionally summable yet satisfies $\sum_{n=0}^\infty\lVert x_n\rVert=\infty$. In Lean, `summable_iff_cauchySeq_finset` (`Group.lean:204–206`) captures exact unconditional summability across all dimensions, while `Summable.of_norm` (`Normed/Group/InfiniteSum.lean:194–195`) is the one-way sufficiency gate used when absolute majorants are available.
3. *No separability required for countable support.* Lemma 2(2) (`Summable.countable_support`, `Group.lean:388–390`) assumes neither countable $I$ nor separability of $E$: even in a non-separable Hilbert space $\ell^2(\mathbb R)$ or Banach space $\ell^\infty(\mathbb N)$, every unconditionally summable family $x:I\to E$ vanishes outside a countable subset of $I$. In archive A2, this lemma is called directly to certify countability of discrete spectral and lattice index sets without constructing explicit enumerations by hand (table below).

| Declaration read at R3 here | Direct consumers in pinned Mathlib / archive A2 | Role in the book |
|---|---|---|
| `summable_iff_cauchySeq_finset`, `cauchySeq_finset_iff_sum_vanishing`, `cauchySeq_finset_iff_vanishing_norm`, `summable_iff_vanishing_norm` ([Group.lean:204–262](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Group.lean#L204-L262), [Normed/Group/InfiniteSum.lean:46–56](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/InfiniteSum.lean#L46-L56)) | `OrthogonalFamily.summable_iff_norm_sq_summable` ([Subspace.lean:201](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Subspace.lean#L201)) $\to$ `OrthogonalFamily.linearIsometry` ([l2Space.lean:186–216](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L186-L216)); archive `ConstEqZero.lean:104` (`summable_iff_vanishing_norm.mp`) | Lemma 1(1)–(2), Theorem 3(1),(4), and [§1.2.2.8](#1228-hilbert-expansion-and-the-norm-behind-poisson-summation) synthesis |
| `Summable.of_norm_bounded`, `Summable.of_norm_bounded_eventually`, `Summable.of_norm`, `norm_tsum_le_tsum_norm` ([Normed/Group/InfiniteSum.lean:111–195](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/InfiniteSum.lean#L111-L195)) | `ContinuousMap.summable_of_locally_summable_norm` ([Compact.lean:473](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/Compact.lean#L473)); `hasSum_fourier_series_of_summable` ([AddCircle.lean:498](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L498)); `lp.summable_inner` ([l2Space.lean:115](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L115)); `summable_mul_of_summable_norm` ([Normed/Ring/InfiniteSum.lean:47](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Ring/InfiniteSum.lean#L47)); archive `PoissonSummationDecay.lean:48, 112` and `UnfoldPoincareSeriesLatticeFourier.lean:143` | Lemma 1(3), Theorem 3(2), [§1.2.2.7](#1227-from-poisson-summation-to-theta-inversion) Tier I & periodization, and [Chapter 2, §2.6](02-functional-equations-and-primitive-characters.md#26-lean-counterpart-for-this-chapter) (§2.6.3.1) Banach Cauchy products |
| `Function.Injective.hasSum_iff`, `Equiv.hasSum_iff_of_support`, `Summable.countable_support`, `HasSum.tendsto_sum_nat` ([Defs.lean:221–244](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean#L221-L244), [Basic.lean:183–215](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean#L183-L215), [Group.lean:388–390](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Group.lean#L388-L390), [NatInt.lean:48–50](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean#L48-L50)) | `ContinuousMap.periodic_tsum_comp_add_zsmul` ([Periodic.lean:33](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/ContinuousMap/Periodic.lean#L33)); archive `IntegrableOfContinuousCircleMeasure.lean:2913–2918` (`Countable T.La`), `SchurFunctionWhittakerEquivariant.lean:154–162` (`Countable s`), and `UnfoldPoincareSeriesLatticeFourier.lean:143` (`ha.of_norm.countable_support`) | Lemma 2(1)–(3) and [§1.2.2.8](#1228-hilbert-expansion-and-the-norm-behind-poisson-summation) enumeration remark |
| `ContinuousLinearMap.hasSum` (`HasSum.mapL`), `IsClosedEmbedding.map_tsum`, `IsUniformInducing.isComplete_range`, `IsComplete.isClosed` ([Module.lean:122–152](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Module.lean#L122-L152), [Basic.lean:257–276](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean#L257-L276), [UniformEmbedding.lean:288–291](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/UniformEmbedding.lean#L288-L291), [CompleteSeparated.lean:26–38](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/CompleteSeparated.lean#L26-L38)) | `OrthogonalFamily.range_linearIsometry` ([l2Space.lean:253](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/l2Space.lean#L253)), `HilbertBasis.hasSum_repr_symm` (`:436`), `hasSum_inner_mul_inner` (`:464`); `has_pointwise_sum_fourier_series_of_summable` ([AddCircle.lean:506](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/AddCircle.lean#L506)) | Theorem 3(3)–(4), [§1.2.2.7](#1227-from-poisson-summation-to-theta-inversion) pointwise Poisson step, and [§1.2.2.8](#1228-hilbert-expansion-and-the-norm-behind-poisson-summation) reconstruction |

**Source note.** The reading is local R3 for `SummationFilter.lean:32–48, 142–190, 215–254`, `InfiniteSum/Defs.lean:106–147, 201–202, 221–244, 308–349`, `InfiniteSum/Basic.lean:125–126, 183–225, 257–276, 323–332, 717–720`, `InfiniteSum/Group.lean:204–262, 301–303, 330–390`, `InfiniteSum/Module.lean:24–35, 122–152`, and `InfiniteSum/NatInt.lean:48–59`; for `Normed/Group/InfiniteSum.lean:46–91, 111–151, 180–195` (with lines `93–107` inherited from [Chapter 9, §9.4](09-heights-slopes-and-near-orthogonality.md#94-lemmas-and-proofs), §9.4.10); for the uniform-completeness and countable-support suppliers `UniformSpace/Cauchy.lean:31–86, 186–187, 370–372, 424–435, 830–922`, `UniformEmbedding.lean:259–291`, `CompleteSeparated.lean:26–38`, `IsUniformGroup/Defs.lean:143–145`, `Group/Basic.lean:785–791`, `Normed/Group/Uniform.lean:382–384`, `Filter/Cofinite.lean:138–147`, `Filter/CountablyGenerated.lean:138–141`, and `Separation/Basic.lean:633–634`; and for the consumer bodies `InnerProductSpace/Subspace.lean:198–239`, `InnerProductSpace/l2Space.lean:109–116, 184–254, 429–475, 496–515`, `Lp/lpSpace.lean:1174–1195`, `AddCircle.lean:494–507`, `Compact.lean:463–474`, `Normed/Ring/InfiniteSum.lean:45–48`, and archive A2 callers `IntegrableOfContinuousCircleMeasure.lean:2913–2918`, `SchurFunctionWhittakerEquivariant.lean:154–162`, `UnfoldPoincareSeriesLatticeFourier.lean:139–145`, `ConstEqZero.lean:104`, and `PoissonSummationDecay.lean:48, 112`. Inherited without re-proving are the circle Poisson tiers ([§1.2.2.7](#1227-from-poisson-summation-to-theta-inversion) and [Chapter 14, §§14.4.2–14.4.2.3](14-masullos-trace-formula-route.md#1442-poisson-summation-and-jumps-on-the-local-logarithmic-lattice)), the Hilbert-basis projection minimizer, Bessel inequality, and $\ell^2$ coordinate completeness ([§1.2.2.8](#1228-hilbert-expansion-and-the-norm-behind-poisson-summation)), the scalar complex tail bound, quadrant converse, and Cauchy-product regrouping ([Chapter 2, §2.6](02-functional-equations-and-primitive-characters.md#26-lean-counterpart-for-this-chapter), §2.6.3.1), and the seminormed subsequence bridge ([Chapter 9, §9.4](09-heights-slopes-and-near-orthogonality.md#94-lemmas-and-proofs), §9.4.10). Inputs retained at `[Lean]` interface level here are sequential completeness of $\mathbb R$ (`Real.instCompleteSpace`, proved from the rational Cauchy quotient in [§1.2.2.10](#12210-rational-cauchy-completion-dedekind-suprema-and-realinstcompletespace)), finite-set induction and disjoint-union identities (`Finset.sum_union`, `Finset.sum_sdiff`), set-theoretic countable-union closure (`Set.Countable.biUnion`), and the metric neighborhood-basis equivalence (`Metric.nhds_basis_ball`, `Metric.mem_uniformity_dist`). The classical references and their scopes are recorded in the [source ledger](../sources/SOURCES.md#chapter-1-1229-unordered-summation-and-banach-completeness). The [proof map](../notes/proof-map.md#p1-chapter-1-unordered-summation-and-banach-completeness) lists pinned paths and lines. Hand calculations A and B, the $R_{3m}=S_{4m}+\tfrac12 S_{2m}$ rearrangement identity, the $c_{00}(\mathbb N)$ counterexamples, and the hypothesis-deletion counterexamples are ours; exact rational assertions (`verify_sum_completeness.py`) check arithmetic and source pins only, do not constitute Lean kernel verification, and do not audit the archive's transitive dependency cone.

#### 1.2.2.10 Rational Cauchy completion, Dedekind suprema, and `Real.instCompleteSpace`

**Motivation.** Every Banach-space majorant argument in [§1.2.2.9](#1229-unordered-summation-finite-tail-cauchy-criteria-and-banach-completeness) — from cofinite comparison (`cauchySeq_finset_of_norm_bounded_eventually`) and absolute summability (`Summable.of_norm_bounded`, `Summable.of_norm`) to the Pythagorean equivalence $\mathrm{Summable}(i\mapsto V_i(f_i))\iff\mathrm{Summable}(i\mapsto\lVert f_i\rVert^2)$ in [§1.2.2.8](#1228-hilbert-expansion-and-the-norm-behind-poisson-summation) (`Subspace.lean:201`) — rests on a single foundational instance left at `[Lean]` in §1.2.2.9: the uniform completeness of the real line, `Real.instCompleteSpace : CompleteSpace ℝ` (`Topology/UniformSpace/Real.lean:26`).

Opening that instance in the pinned Mathlib source (`0df444a360eaa60ab8c11dca51a86af692955474`) exposes two design choices that a textbook must separate sharply rather than guess from convention:

1. *Definitional model versus Dedekind cuts.* Mathlib does **not** define $\mathbb R$ by Dedekind cuts, nor can it invoke `UniformSpace.Completion ℚ` before $\mathbb R$ exists (since `PseudoMetricSpace` distances take values in $\mathbb R$, and `Data/Real/Basic.lean:31` explicitly enforces `assert_not_exists Finset Module Submonoid FloorRing`). Instead, following Cantor's 1872 construction (`[Cantor1872]`, §1), `Data/Real/Basic.lean:36–38` defines `Real` as the quotient `CauSeq.Completion.Cauchy (abs : ℚ → ℚ)` of rational Cauchy sequences modulo zero-limit differences, so that the commutative ring axioms lift directly from $\mathbb Q$ (`[Mathlib2020]`, §3).
2. *Order-supremum detour inside sequential completeness.* When proving that every **real-valued** Cauchy sequence $f\in\mathrm{CauSeq}(\mathbb R,\lvert\cdot\rvert)$ converges (`Real.cauSeq_converges`, `Algebra/Order/Archimedean/Real/Basic.lean:324–344`), Mathlib does **not** diagonalize chosen rational representatives of the classes $f(n)$. Instead, it first proves `Archimedean ℝ` (`:31–35`) and **Dedekind conditional order completeness** (`Real.exists_isLUB`, `:59–109`) by building an explicit rational Cauchy sequence $g(n)=f_{\mathrm{grid}}(n)/n$ of scaled integer maxima, and then obtains the limit of any $f\in\mathrm{CauSeq}(\mathbb R,\lvert\cdot\rvert)$ as the least upper bound $x^*=\operatorname{sSup}\{x\in\mathbb R:\mathrm{const}(x)<f\}$ of its strict eventual lower bounds. Conversely, `Real.of_near` (`:47–53`) reconnects any real limit to rational Cauchy representatives, and `ConditionallyCompleteLinearOrderedField.inducedOrderRingIso` (`Algebra/Order/CompleteField.lean:284–318`) recovers Dedekind's lower-cut characterization as a canonical unique isomorphism theorem.

From `CauSeq.IsComplete ℝ abs`, `Real.instCompleteSpace` (`Topology/UniformSpace/Real.lean:26–34`) crosses from one-anchor `IsCauSeq` sequences to metric `CauchySeq` filters and invokes the sequential-to-filter bridge `complete_of_cauchySeq_tendsto` already read in §1.2.2.9 Theorem 3(1). Both uniform completeness (`summable_iff_cauchySeq_finset`, `summable_abs_iff`) and Dedekind order suprema (`summable_of_sum_le`, `Summable.of_nonneg_of_le`, `cauchySeq_of_dist_le_of_summable`, `dist_le_tsum_of_dist_le_of_tendsto`) then supply the real majorants consumed across Chapters 1–2 and archive A2, while preserving the §1.2.2.9 post-audit separation boundary (`[T2Space]` for uniqueness of finite-support and infinite-sum limits, automatic on $\mathbb R$ and $\mathbb Q$).

**Examples (rational Cauchy models, tail control, and the $\mathbb Q$ versus $\mathbb R$ boundary).** Fix the target equation $x^2=2$ ($x>0$) alongside telescoping rational series:

| Construction on $\mathbb N$ | Ambient space | `IsCauSeq` / `CauchySeq`? | Supremum / `HasSum` witness | Quantitative tail bound at step $N$ |
|---|---|---|---|---|
| Heron iterates $r_0=\frac32$, $r_{n+1}=\frac12(r_n+\frac{2}{r_n})$ | $\mathbb R$ (`CompleteSpace`) | Yes ($0<r_n-r_{n+1}<\frac18\cdot 32^{-n}$) | $\mathrm{Real.mk}\,r=\sqrt{2}$ (`Real.of_near`) | $0<r_N-\sqrt{2}\le\frac{4}{31}\cdot 32^{-N}$ (and $<r_N-\frac{2}{r_N}$) |
| Integer-grid sequence $g(n)=\frac{\max\{m\in\mathbb Z:m^2<2n^2\}}{n}$ ($n\ge1$) | $\mathbb R$ (`CompleteSpace`) | Yes ($\lvert g(j)-g(k)\rvert<\max(j^{-1},k^{-1})$) | $\mathrm{Real.mk}\,g=\sup\{x\in\mathbb R:x\le0\vee x^2<2\}=\sqrt{2}$, $g\approx r$ | $0<\sqrt{2}-g(N)<\frac{1}{N}$ ($N\ge1$) |
| Telescoping weights $w_n=\frac{1}{(n+1)(n+2)}\ge0$ | $\mathbb R$ (`ConditionallyCompleteLinearOrder`) | Partial sums $\le 1$, Cauchy | $\mathrm{HasSum}(w,1)$ via `summable_of_sum_le` | $\sum'_{m\ge0}w_{N+m}=\frac{1}{N+1}$ |
| Same Heron sequence $(r_n)$ or increments $v_0=\frac32$, $v_{n+1}=r_{n+1}-r_n$ | $\mathbb Q$ (induced metric/norm) | **Yes** (`CauchySeq r`, $\sum_{n\ge0}\lVert v_n\rVert=3-\sqrt{2}<\frac{13}{8}$) | **None in $\mathbb Q$** (`tsum` of $v$ defaults to $0\in\mathbb Q$) | $\forall\frac{a}{b}\in\mathbb Q,\;\forall n\ge N_b,\;\lvert r_n-\frac{a}{b}\rvert\ge\min\bigl(\frac12,\frac{1}{7b^2}\bigr)>0$ |

Although $(r_n)$ and $(g(n))$ are distinct rational sequences ($r_1=\frac{17}{12}$ whereas $g(1)=1$), their difference tends to $0$, so they inhabit the **same** equivalence class in `Real`. Restricting the codomain back to $\mathbb Q$ keeps every Cauchy and real norm-summability hypothesis intact while destroying both the sequential limit and `Summable.of_norm`. [Expository]

**Definitions (the Cauchy-quotient model of $\mathbb R$, order completeness, and filter completeness).**

1. *Absolute-value Cauchy sequences, equivalence, and positivity (`IsCauSeq`, `CauSeq`, `LimZero`, `CauSeq.equiv`, `CauSeq.Pos`).* Let $\alpha$ be a linearly ordered field (`[Field α] [LinearOrder α] [IsStrictOrderedRing α]`) and $\beta$ a ring equipped with an absolute value $\mathrm{abv}:\beta\to\alpha$ (`[IsAbsoluteValue abv]`, so $\mathrm{abv}(x)\ge0$, $\mathrm{abv}(x)=0\iff x=0$, $\mathrm{abv}(xy)=\mathrm{abv}(x)\mathrm{abv}(y)$, and $\mathrm{abv}(x+y)\le\mathrm{abv}(x)+\mathrm{abv}(y)$).
   - A sequence $f:\mathbb N\to\beta$ satisfies `IsCauSeq abv f` if it obeys the **one-anchor** Cauchy condition
     $$
      \forall\varepsilon\in\alpha,\quad\varepsilon>0\implies\exists i\in\mathbb N,\quad\forall j\ge i,\quad\mathrm{abv}(f_j-f_i)<\varepsilon.
     $$
     The subtype of such sequences is `CauSeq β abv = { f : ℕ → β // IsCauSeq abv f }`, with constant embedding `const abv x` ($n\mapsto x$) and pointwise ring operations $+,-,\cdot$.
   - For $f\in\mathrm{CauSeq}(\beta,\mathrm{abv})$, `LimZero f` means $\forall\varepsilon>0,\;\exists i,\;\forall j\ge i,\;\mathrm{abv}(f_j)<\varepsilon$. The setoid `CauSeq.equiv` sets
     $$
      f\approx g\iff\mathrm{LimZero}(f-g).
     $$
   - When $\beta=\alpha$ and $\mathrm{abv}=\lvert\cdot\rvert$, `Pos f` means $\exists K\in\alpha,\;K>0\;\wedge\;\exists i\in\mathbb N,\;\forall j\ge i,\;K\le f_j$. Setting $f<g\iff\mathrm{Pos}(g-f)$ and $f\le g\iff(f<g\;\vee\;f\approx g)$ equips `CauSeq α abs` with a `Preorder` (not a `PartialOrder`, since antisymmetry holds only up to $\approx$).
2. *Definitional model of the real numbers (`CauSeq.Completion.Cauchy`, `Real`, `Real.mk`).* The **Cauchy completion** of $(\beta,\mathrm{abv})$ is the quotient type `CauSeq.Completion.Cauchy abv = Quotient (CauSeq.equiv)` with projection `CauSeq.Completion.mk : CauSeq β abv → Cauchy abv` ($f\mapsto\llbracket f\rrbracket$) and ring embedding `ofRat x = mk (const abv x)`. In `Data/Real/Basic.lean:36–38`, the real numbers are defined as the single-field structure
   $$
    \mathrm{Real}\;(\mathbb R)\;:\equiv\;\bigl\{\,\mathrm{ofCauchy}(c)\;\big\vert\;c:\mathrm{CauSeq.Completion.Cauchy}(\lvert\cdot\rvert:\mathbb Q\to\mathbb Q)\,\bigr\},
   $$
   with constructor wrapper $\mathrm{Real.mk}(f)=\mathrm{ofCauchy}(\llbracket f\rrbracket)$ for $f\in\mathrm{CauSeq}(\mathbb Q,\lvert\cdot\rvert)$ and exact quotient equality $\mathrm{Real.mk}(f)=\mathrm{Real.mk}(g)\iff f\approx g$ (`Real.mk_eq`). Ring operations $+,-,\cdot$ lift componentwise; reciprocal `inv'` sends $\llbracket f\rrbracket$ (by classical `by_cases` on `LimZero f`) to $0$ if $\mathrm{LimZero}(f)$, and otherwise to $\llbracket\mathrm{CauSeq.inv}(f,hf)\rrbracket$ where $(\mathrm{inv}(f,hf))_n=(f_n)^{-1}$ in $\mathbb Q$ (using $0^{-1}=0$ on any finite prefix where $f_n=0$). Strict order is lifted by $\mathrm{Real.mk}(f)<\mathrm{Real.mk}(g)\iff\mathrm{Pos}(g-f)$ (`Real.mk_lt`), and $x\le y\iff x<y\vee x=y$.
3. *Sequential `CauSeq` completeness, Dedekind `sSup` completeness, and uniform filter completeness.*
   - `CauSeq.IsComplete β abv` (`Completion.lean:288–290`) is the proposition $\forall s\in\mathrm{CauSeq}(\beta,\mathrm{abv}),\;\exists b\in\beta,\;s\approx\mathrm{const}(\mathrm{abv},b)$; when it holds, `CauSeq.lim s := Classical.choose (complete s)` selects a limit witness satisfying `equiv_lim s : s ≈ const abv (lim s)`.
   - On $\mathbb R$, `IsLUB s x` means $x\in\mathrm{upperBounds}(s)$ and $x\in\mathrm{lowerBounds}(\mathrm{upperBounds}(s))$. `SupSet ℝ` (`Archimedean/Real/Basic.lean:119–125`) defines $\operatorname{sSup}s$ via `Classical.choose (exists_isLUB h.1 h.2)` if $s$ is nonempty and bounded above (`BddAbove s`), and **defaults to $0\in\mathbb R$** if $s=\emptyset$ or $\neg\mathrm{BddAbove}(s)$ (`sSup_empty`, `sSup_of_not_bddAbove`), with $\operatorname{sInf}s=-\operatorname{sSup}(-s)$.
   - `Real.pseudoMetricSpace` (`Pseudo/Defs.lean:1125`) and `Real.metricSpace` (`MetricSpace/Basic.lean:122`) set $\operatorname{dist}(x,y)=\lvert x-y\rvert$, inducing the uniform structure $\mathcal U_{\mathbb R}$, the metric topology (which coincides with `Preorder.topology ℝ` via `OrderTopology ℝ`, `Pseudo/Lemmas.lean:23`), and `Real.normedAddCommGroup` ($\lVert r\rVert=\lvert r\rvert$, `Normed/Group/Real.lean:55`). As in §1.2.2.9 Definitions (3), `CompleteSpace ℝ` asserts that every proper Cauchy filter $\mathcal G$ on $\mathbb R$ satisfies $\mathcal G\le\mathcal N(a)$ for some $a\in\mathbb R$. [Lean, read] [CauSeq/Basic.lean:84–88](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Basic.lean#L84-L88) · [CauSeq/Basic.lean:152–154](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Basic.lean#L152-L154) · [CauSeq/Basic.lean:361–410](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Basic.lean#L361-L410) · [CauSeq/Basic.lean:567–626](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Basic.lean#L567-L626) · [CauSeq/Completion.lean:33–72](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Completion.lean#L33-L72) · [CauSeq/Completion.lean:192–205](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Completion.lean#L192-L205) · [CauSeq/Completion.lean:288–308](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Completion.lean#L288-L308) · [Data/Real/Basic.lean:36–126](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Real/Basic.lean#L36-L126) · [Data/Real/Basic.lean:263–321](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Real/Basic.lean#L263-L321) · [Archimedean/Real/Basic.lean:119–146](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean#L119-L146) · [Pseudo/Defs.lean:1125–1131](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L1125-L1131) · [MetricSpace/Basic.lean:122](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/MetricSpace/Basic.lean#L122) · [Pseudo/Lemmas.lean:23–25](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean#L23-L25) · [Normed/Group/Real.lean:49–56](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/Real.lean#L49-L56)

**Lemma 1 (quotient field structure, uniform separation from zero, trichotomy, Archimedean bound, and rational recognition).**

1. *Two-index Cauchyness, boundedness, separation from zero, and field inversion (`cauchy₂`, `bounded`, `abv_pos_of_not_limZero`, `inv_aux`, `Real.instField`).* For any $(\alpha,\beta,\mathrm{abv})$ as above:
   - Every $f\in\mathrm{CauSeq}(\beta,\mathrm{abv})$ satisfies the two-index bound $\forall\varepsilon>0,\;\exists i,\;\forall j,k\ge i,\;\mathrm{abv}(f_j-f_k)<\varepsilon$ (`cauchy₂`) and is uniformly bounded: $\exists r\in\alpha,\;\forall n\in\mathbb N,\;\mathrm{abv}(f_n)<r$ (`bounded`).
   - Pointwise $+,-,\cdot$ preserve `IsCauSeq` and respect $\approx$ (`add_equiv_add`, `mul_equiv_mul`). If $\beta$ is a division ring and $f\in\mathrm{CauSeq}(\beta,\mathrm{abv})$ satisfies $\neg\mathrm{LimZero}(f)$, then $f$ is **uniformly bounded away from zero** on a tail:
     $$
      \exists K\in\alpha,\quad K>0\;\wedge\;\exists i\in\mathbb N,\quad\forall j\ge i,\quad K\le\mathrm{abv}(f_j).
     $$
     Consequently $n\mapsto(f_n)^{-1}$ satisfies `IsCauSeq`, $\mathrm{inv}(f,hf)\cdot f\approx 1$, and `Real` is a `Field` (`Real.instField`) into which $\mathrm{Rat.cast}:\mathbb Q\hookrightarrow\mathbb R$ embeds as an injective ring homomorphism.
2. *Trichotomy and strict ordered field (`CauSeq.trichotomy`, `Real.linearOrder`, `Real.instIsStrictOrderedRing`).* Every $f\in\mathrm{CauSeq}(\alpha,\lvert\cdot\rvert)$ satisfies **exactly one** of `Pos f`, `LimZero f`, or `Pos (-f)`. Consequently $<$ and $\le$ descend to $\mathbb R$, making $\mathbb R$ a `LinearOrder` and an `IsStrictOrderedRing` in which $\mathrm{Rat.cast}$ is strictly order-preserving (`Real.ratCast_lt`).
3. *Rational-tail order comparison, Archimedean property, and recognition (`le_mk_of_forall_le`, `mk_le_of_forall_le`, `Real.instArchimedean`, `Real.of_near`).* Let $f\in\mathrm{CauSeq}(\mathbb Q,\lvert\cdot\rvert)$ and $x\in\mathbb R$.
   - If $\exists i,\;\forall j\ge i,\;x\le(f_j:\mathbb R)$, then $x\le\mathrm{Real.mk}(f)$; symmetrically, if $\exists i,\;\forall j\ge i,\;(f_j:\mathbb R)\le x$, then $\mathrm{Real.mk}(f)\le x$; hence if $\exists i,\;\forall j\ge i,\;\lvert(f_j:\mathbb R)-x\rvert\le\varepsilon$, then $\lvert\mathrm{Real.mk}(f)-x\rvert\le\varepsilon$ (`mk_near_of_forall_near`).
   - $\mathbb R$ is **Archimedean** (`Real.instArchimedean`): for every $x\in\mathbb R$ there exists $M\in\mathbb Q$ (hence $N\in\mathbb N$) with $x\le M\le N$, equipping $\mathbb R$ with an integer floor $\lfloor x\rfloor\in\mathbb Z$ (`FloorRing ℝ`) and dense rational intervals (`exists_rat_btwn`).
   - Conversely (`Real.of_near`), if an unbundled rational sequence $f:\mathbb N\to\mathbb Q$ satisfies $\forall\varepsilon\in\mathbb R,\;\varepsilon>0\implies\exists i,\;\forall j\ge i,\;\lvert(f_j:\mathbb R)-x\rvert<\varepsilon$, then $h':\mathrm{IsCauSeq}(\lvert\cdot\rvert,f)$ holds in $\mathbb Q$ and $\mathrm{Real.mk}\,\langle f,h'\rangle=x$.

**Proof.** (1) Given $\varepsilon>0$, `f.cauchy` at $\varepsilon/2>0$ yields $i$ with $\mathrm{abv}(f_j-f_i)<\varepsilon/2$ for all $j\ge i$; for $j,k\ge i$, the triangle inequality and symmetry $\mathrm{abv}(f_i-f_k)=\mathrm{abv}(f_k-f_i)$ give $\mathrm{abv}(f_j-f_k)\le\mathrm{abv}(f_j-f_i)+\mathrm{abv}(f_i-f_k)<\varepsilon/2+\varepsilon/2=\varepsilon$ (`cauchy₂`, whose $j\le k$ specialization is `cauchy₃`). Taking $\varepsilon=1$ gives $i_1$ with $\mathrm{abv}(f_j-f_{i_1})<1$ for $j\ge i_1$; defining $R_{i_1}=\max_{0\le m\le i_1}\mathrm{abv}(f_m)$ recursively (`CauSeq/Basic.lean:108–118`), every $j\le i_1$ satisfies $\mathrm{abv}(f_j)<R_{i_1}+1$, while every $j\ge i_1$ satisfies $\mathrm{abv}(f_j)\le\mathrm{abv}(f_{i_1})+\mathrm{abv}(f_j-f_{i_1})<R_{i_1}+1$ (`bounded`; `bounded' x` replaces $r$ by $\max(r,x+1)>x$).

For products, let $\mathrm{abv}(f_n)<K_1$ and $\mathrm{abv}(g_n)<K_2$ with $M=\max(1,\max(K_1,K_2))>0$; splitting $a_1a_2-b_1b_2=(a_1-b_1)b_2+a_1(a_2-b_2)$ bounds $\mathrm{abv}(a_1a_2-b_1b_2)<\delta M+M\delta=\varepsilon$ when $\delta=\frac{\varepsilon}{2M}$ (`rat_mul_continuous_lemma`, `:55–68`), proving `IsCauSeq.mul`; similarly `mul_limZero_left` and `mul_limZero_right` (`:370–383`) combine with $f_1g_1-f_2g_2=(f_1-f_2)g_1+f_2(g_1-g_2)$ to prove `mul_equiv_mul` (`:487–490`).

Now suppose $\neg\mathrm{LimZero}(f)$ (`abv_pos_of_not_limZero`, `:430–439`). Assume for contradiction that for every $K>0$ and every $i\in\mathbb N$ there exists $j\ge i$ with $\mathrm{abv}(f_j)<K$. Given any $\varepsilon>0$, `f.cauchy₃` at $\varepsilon/2$ supplies $i$ such that $\mathrm{abv}(f_k-f_j)<\varepsilon/2$ whenever $i\le j\le k$, and our assumption at $(K,i)=(\varepsilon/2,i)$ supplies $j\ge i$ with $\mathrm{abv}(f_j)<\varepsilon/2$. Then for all $k\ge j$, $\mathrm{abv}(f_k)\le\mathrm{abv}(f_k-f_j)+\mathrm{abv}(f_j)<\varepsilon/2+\varepsilon/2=\varepsilon$, proving `LimZero f`, a contradiction! Hence some $K>0$ and $i_0\in\mathbb N$ satisfy $\mathrm{abv}(f_j)\ge K>0$ for all $j\ge i_0$. In a division ring, whenever $\mathrm{abv}(a)\ge K$ and $\mathrm{abv}(b)\ge K$, both $a,b$ are nonzero and $a^{-1}-b^{-1}=a^{-1}(b-a)b^{-1}$, so $\mathrm{abv}(a-b)<K\varepsilon K\implies\mathrm{abv}(a^{-1}-b^{-1})<K^{-1}(K\varepsilon K)K^{-1}=\varepsilon$ (`rat_inv_continuous_lemma`, `:69–79`). Combining $(K,i_0)$ with `f.cauchy₃ (K * ε * K)` proves `inv_aux` (`:524–533`); for $j\ge i_0$, $f_j\ne0$ gives $(f_j)^{-1}f_j-1=0$, so $\mathrm{inv}(f,hf)\cdot f\approx 1$ (`:547–554`). Well-definedness on $\mathrm{Cauchy}\,\mathrm{abv}$ (`Completion.lean:192–205`) follows from ring associativity $\llbracket\mathrm{inv}\,f\rrbracket=\llbracket\mathrm{inv}\,f\rrbracket(\llbracket g\rrbracket\llbracket\mathrm{inv}\,g\rrbracket)=(\llbracket\mathrm{inv}\,f\rrbracket\llbracket f\rrbracket)\llbracket\mathrm{inv}\,g\rrbracket=\llbracket\mathrm{inv}\,g\rrbracket$ when $f\approx g$, establishing `Real.instField` (`Data/Real/Basic.lean:500–516`). Injectivity of $\mathrm{ofRat}$ (`Completion.lean:141–142`) comes from `const_limZero`: if $\mathrm{const}(x)\approx\mathrm{const}(y)$, then $\mathrm{abv}(x-y)<\varepsilon$ for all $\varepsilon>0$, forcing $\mathrm{abv}(x-y)=0$ and $x=y$.

(2) Let $f\in\mathrm{CauSeq}(\alpha,\lvert\cdot\rvert)$ (`trichotomy`, `CauSeq/Basic.lean:601–620`). First, `Pos f` and `LimZero f` exclude each other (`not_limZero_of_pos`, `:570–574`): if $f_j\ge K>0$ for $j\ge i_1$ and $\lvert f_j\rvert<K$ for $j\ge i_2$, evaluating at $\max(i_1,i_2)$ yields $K\le f_j\le\lvert f_j\rvert<K$, impossible; similarly `Pos f` and `Pos (-f)` cannot both hold because `add_pos` would make $0=f+(-f)$ satisfy `Pos 0`, contradicting `zero_limZero`. If $\neg\mathrm{LimZero}(f)$, part (1) (`abv_pos_of_not_limZero`) gives $K>0$ and $i_1$ with $\lvert f_j\rvert\ge K$ for $j\ge i_1$, while `f.cauchy₃ K` gives $i_2$ with $\lvert f_j-f_i\rvert<K$ for $j\ge i\ge i_2$. Put $i=\max(i_1,i_2)$, so $\lvert f_i\rvert\ge K$ and $-K<f_j-f_i<K$ for all $j\ge i$. If $f_i\ge0$, then $f_i=\lvert f_i\rvert\ge K$; for any $j\ge i$, $f_j=f_i+(f_j-f_i)>K-K=0$, so $f_j\ge0$ and $f_j=\lvert f_j\rvert\ge K$, proving `Pos f`. If $f_i\le0$, then $-f_i=\lvert f_i\rvert\ge K$; for any $j\ge i$, $f_j< -K+K=0$, so $-f_j=\lvert f_j\rvert\ge K$, proving `Pos (-f)`. Adding a `LimZero` sequence to a `Pos` sequence with lower bound $F>0$ preserves positivity with lower bound $F/2>0$ (`pos_add_limZero`, `:586–592`), so $f<g\iff\mathrm{Pos}(g-f)$ is invariant under $\approx$, transitive (`add_pos`), total (`lt_total`, `:667–670`), and closed under multiplication (`CauSeq.mul_pos`, `:594–600`), giving `Real.linearOrder` and `Real.instIsStrictOrderedRing`.

(3) Write $x=\mathrm{Real.mk}(g)$ with $g\in\mathrm{CauSeq}(\mathbb Q,\lvert\cdot\rvert)$, and assume $x\le(f_j:\mathbb R)$ for all $j\ge i_0$ (`le_mk_of_forall_le`, `Data/Real/Basic.lean:534–545`). Suppose for contradiction that $\mathrm{Real.mk}(f)<x=\mathrm{Real.mk}(g)$, i.e. $\mathrm{Pos}(g-f)$: there exist $K\in\mathbb Q$ with $K>0$ and $i_1$ such that $g_j-f_j\ge K$ for all $j\ge i_1$. Choose $i_2$ from `f.cauchy₃ (K / 2)` so that $\lvert f_j-f_i\rvert<K/2$ for $j\ge i\ge i_2$, and set $i=\max(i_0,i_1,i_2)$. On one hand, $i\ge i_0$ gives $\mathrm{Real.mk}(g)=x\le(f_i:\mathbb R)=\mathrm{Real.mk}(\mathrm{const}\,f_i)$. On the other hand, for every $j\ge i$, $g_j-f_j\ge K$ and $f_j-f_i>-K/2$, so adding gives $g_j-f_i=(g_j-f_j)+(f_j-f_i)>K-K/2=K/2>0$; thus $g_j-f_i\ge K/2$ for all $j\ge i$, witnessing $\mathrm{Pos}(g-\mathrm{const}\,f_i)$, i.e. $(f_i:\mathbb R)<\mathrm{Real.mk}(g)$, contradicting $\mathrm{Real.mk}(g)\le(f_i:\mathbb R)$! Negating gives `mk_le_of_forall_le` (`:547–551`) and `mk_near_of_forall_near` (`:553–560`).

For `Real.instArchimedean` (`Archimedean/Real/Basic.lean:31–35`), given $x=\mathrm{Real.mk}(f)$, part (1) (`f.bounded' 0`) yields $M\in\mathbb Q$ with $M>0$ and $\lvert f_j\rvert<M$ for all $j\in\mathbb N$; hence $(f_j:\mathbb R)\le(M:\mathbb R)$ for all $j\ge0$, and `mk_le_of_forall_le` gives $x\le(M:\mathbb R)$ (`archimedean_iff_rat_le`). Finally, if $f:\mathbb N\to\mathbb Q$ satisfies $\lvert(f_j:\mathbb R)-x\rvert<\varepsilon$ eventually for every real $\varepsilon>0$ (`Real.of_near`, `:47–53`), then $(f_j:\mathbb R)$ is within $\varepsilon/4$ of $\mathrm{const}(x)$, so `CauSeq.of_near` (`CauSeq/Basic.lean:441–450`) proves `IsCauSeq abs (fun j => (f j : ℝ))`, restricting along `Rat.cast_pos` to `h' : IsCauSeq abs f` (`isCauSeq_iff_lift`, `:40–45`). For every $\varepsilon>0$, `mk_near_of_forall_near` then gives $\lvert\mathrm{Real.mk}\,\langle f,h'\rangle-x\rvert\le\varepsilon$, forcing $\mathrm{Real.mk}\,\langle f,h'\rangle=x$ because $\mathbb R$ is densely ordered. $\square$

[Lean, read] [CauSeq/Basic.lean:49–79](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Basic.lean#L49-L79) · [CauSeq/Basic.lean:94–142](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Basic.lean#L94-L142) · [CauSeq/Basic.lean:370–490](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Basic.lean#L370-L490) · [CauSeq/Basic.lean:524–696](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Basic.lean#L524-L696) · [CauSeq/Completion.lean:141–273](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Completion.lean#L141-L273) · [Data/Real/Basic.lean:187–217](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Real/Basic.lean#L187-L217) · [Data/Real/Basic.lean:328–560](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Real/Basic.lean#L328-L560) · [Archimedean/Real/Basic.lean:31–53](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean#L31-L53)

**Lemma 2 (integer-grid Dedekind suprema `Real.exists_isLUB`, sequential Cauchy completeness `Real.cauSeq_converges`, choice-independence, and Dedekind-cut equivalence).**

1. *Dedekind suprema from scaled integer grids (`Real.exists_isLUB`, `ConditionallyCompleteLinearOrder ℝ`).* For every nonempty bounded-above subset $s\subseteq\mathbb R$, there exists $x^*\in\mathbb R$ such that $\mathrm{IsLUB}(s,x^*)$ (dually, every nonempty bounded-below $s\subseteq\mathbb R$ has an `IsGLB`). Specifically, for each $d\in\mathbb N$, the set $\{m\in\mathbb Z:\exists y\in s,\;(m:\mathbb R)\le y\cdot d\}$ has a greatest integer $f_{\mathrm{grid}}(d)\in\mathbb Z$, the rational sequence $g(n)=f_{\mathrm{grid}}(n)/n$ satisfies `IsCauSeq abs g` with $\lvert g(j)-g(k)\rvert<1/\min(j,k)$ for $j,k\ge1$, and $x^*=\mathrm{Real.mk}(g)$ is the least upper bound of $s$.
2. *Sequential completeness of $\mathbb R$ (`Real.cauSeq_converges`, `CauSeq.IsComplete ℝ abs`).* For **every** real-valued Cauchy sequence $f\in\mathrm{CauSeq}(\mathbb R,\lvert\cdot\rvert)$, the set of strict eventual lower bounds
   $$
    s_f=\{x\in\mathbb R:\mathrm{const}(\lvert\cdot\rvert,x)<f\}
   $$
   is nonempty and bounded above in $\mathbb R$, and $x^*=\operatorname{sSup}s_f\in\mathbb R$ satisfies $f\approx\mathrm{const}(\lvert\cdot\rvert,x^*)$. Moreover, any rational sequence $(q_n)_{n\in\mathbb N}$ satisfying $\lvert(q_n:\mathbb R)-f_n\rvert<(n+1)^{-1}$ belongs to $\mathrm{CauSeq}(\mathbb Q,\lvert\cdot\rvert)$ and represents $x^*=\mathrm{Real.mk}(q)$.
3. *Choice-independence of limits and categorical equivalence with Dedekind cuts (`lim_eq_of_equiv_const`, `lim_eq_lim_of_equiv`, `tendsto_nhds_unique`, `inducedOrderRingIso`).*
   - Although `sSup`, `CauSeq.lim`, `CompleteSpace.complete`, and `tsum` invoke `Classical.choose` to extract an element of $\mathbb R$ from a propositional witness `∃ x : ℝ, ...`, the resulting real number is **strictly independent of the choice function** whenever the domain condition holds:
     1. if $\mathrm{IsLUB}(s,x_1)$ and $\mathrm{IsLUB}(s,x_2)$, antisymmetry of $\le$ gives $x_1=x_2$, so $\operatorname{sSup}s=x_1$;
     2. if $f\approx\mathrm{const}(x_1)$ and $f\approx\mathrm{const}(x_2)$ in `CauSeq ℝ abs`, then $x_1=\mathrm{CauSeq.lim}(f)=x_2$, and $f\approx g\implies\mathrm{lim}(f)=\mathrm{lim}(g)$;
     3. in the metric topology on $\mathbb R$ (which is $T_2$), any proper filter $\mathcal G$ admits at most one limit (`tendsto_nhds_unique`), so any convergent sequence or summable series has a unique limit independent of `Classical.choose`.
   - For any field $\beta$ carrying `[ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]` (the Dedekind-complete ordered field axioms), $\beta$ is automatically Archimedean (`to_archimedean`) and the **rational Dedekind lower-cut map**
     $$
      \Phi:\mathbb R\longrightarrow\beta,\qquad\Phi(x)=\operatorname{sSup}\bigl\{(q:\beta)\;\big\vert\;q\in\mathbb Q,\;(q:\mathbb R)<x\bigr\},
     $$
     is the **unique** ordered-ring isomorphism $\mathbb R\simeq_{+\cdot\le}\beta$ (`inducedOrderRingIso`, `uniqueOrderRingIso`).

**Proof.** (1) Follow `Archimedean/Real/Basic.lean:59–109` step by step. Fix $L\in s$ (from `s.Nonempty`) and an upper bound $U\in\mathrm{upperBounds}(s)$ (from `BddAbove s`). By Lemma 1(3) (`exists_int_gt U`), pick $k\in\mathbb Z$ with $U<(k:\mathbb R)$. For each $d\in\mathbb N$, consider
$$
 Z_d=\bigl\{m\in\mathbb Z:\exists y\in s,\;(m:\mathbb R)\le y\cdot d\bigr\}.
$$
Every $m\in Z_d$ satisfies $(m:\mathbb R)\le yd\le Ud\le kd$ (`d ≥ 0`), so $m\le k\cdot d$ in $\mathbb Z$; meanwhile $\lfloor L\cdot d\rfloor\in Z_d$ witnessed by $L\in s$ (`Int.floor_le`). Because every nonempty bounded-above subset of $\mathbb Z$ has a maximum (`Int.exists_greatest_of_bdd`), let $f_{\mathrm{grid}}(d)=\max Z_d\in\mathbb Z$. Then for every integer $n\ge1$ ($n>0$ in $\mathbb R$):
- **(hf₁)** Since $f_{\mathrm{grid}}(n)\in Z_n$, there exists $y\in s$ with $(f_{\mathrm{grid}}(n):\mathbb R)\le yn$, i.e. $\bigl(\frac{f_{\mathrm{grid}}(n)}{n}:\mathbb R\bigr)\le y$.
- **(hf₂)** For **every** $y\in s$, $\lfloor yn\rfloor\in Z_n$, so maximality gives $\lfloor yn\rfloor\le f_{\mathrm{grid}}(n)$. Combining with $yn-1<\lfloor yn\rfloor$ (`Int.sub_one_lt_floor`) and dividing by $n>0$ gives
  $$
   y-\frac{1}{n}<\Bigl(\frac{f_{\mathrm{grid}}(n)}{n}:\mathbb R\Bigr).
  $$

Now check `IsCauSeq abs g` for $g(n)=\frac{f_{\mathrm{grid}}(n)}{n}\in\mathbb Q$ (`:80–94`). Given rational $\varepsilon>0$, put $N_0=\lceil\varepsilon^{-1}\rceil_+\in\mathbb N$. For any $j,k\ge N_0$, we have $j,k\ge\varepsilon^{-1}>0$ (so $j,k\ge1$ and $\frac{1}{k}\le\varepsilon$). Pick $y\in s$ from **(hf₁)** at $j$, so $g(j)\le y$ in $\mathbb R$, while **(hf₂)** at $k$ for that **same** $y\in s$ gives $y-\frac{1}{k}<g(k)$, i.e. $y<g(k)+\frac{1}{k}$. Chaining the two inequalities in $\mathbb R$ and pulling back along `Rat.cast_lt` yields
$$
 g(j)-g(k)\le y-g(k)<\frac{1}{k}\le\varepsilon.
$$
Exchanging the roles of $j$ and $k$ (since both are $\ge N_0$) gives $g(k)-g(j)<\varepsilon$, hence $\lvert g(j)-g(k)\rvert<\varepsilon$; specializing $k=N_0$ proves `IsCauSeq abs g`. Set $x^*=\mathrm{Real.mk}(g)\in\mathbb R$ (`:95–109`):
- *Upper bound*: Let $x\in s$. To show $x\le x^*$ in the densely ordered line $\mathbb R$, let $z<x$ (`le_of_forall_lt_imp_le_of_dense`). By the Archimedean property (`exists_nat_gt`), choose $K\in\mathbb N$ with $(x-z)^{-1}<K$. For every $n\ge K$, $n\ge K>(x-z)^{-1}>0$, so $n\ge1$ and $\frac{1}{n}\le x-z$, i.e. $z\le x-\frac{1}{n}<\bigl(g(n):\mathbb R\bigr)$ by **(hf₂)**. Lemma 1(3) (`le_mk_of_forall_le`) gives $z\le\mathrm{Real.mk}(g)=x^*$ for all $z<x$, whence $x\le x^*$.
- *Least upper bound*: Let $y\in\mathrm{upperBounds}(s)$. For every $n\ge1$, **(hf₁)** supplies $x_n\in s$ with $\bigl(g(n):\mathbb R\bigr)\le x_n\le y$; Lemma 1(3) (`mk_le_of_forall_le` from $i=1$) gives $x^*=\mathrm{Real.mk}(g)\le y$.

(2) Let $f\in\mathrm{CauSeq}(\mathbb R,\lvert\cdot\rvert)$ (`Real.cauSeq_converges`, `:324–344`), and set $s_f=\{x\in\mathbb R:\mathrm{const}(x)<f\}$. By Lemma 1(1), $\lvert f_n\rvert<K$ for all $n$, so $f_n-(-K-1)>1$ (`exists_lt`, `CauSeq/Basic.lean:694–696`) gives $-K-1\in s_f$ (`s_f` nonempty), and $K+1-f_n>1$ (`exists_gt`, `:688–692`) gives $f<\mathrm{const}(K+1)$. Whenever $f<\mathrm{const}(u)$ and $y\in s_f$, transitivity $\mathrm{const}(y)<f<\mathrm{const}(u)$ (`CauSeq.lt_trans`) and `const_lt` force $y<u$, hence $y\le u$; thus $K+1$ bounds $s_f$ above. By part (1), $x^*=\operatorname{sSup}s_f\in\mathbb R$ satisfies $\mathrm{IsLUB}(s_f,x^*)$.

By Lemma 1(2) (`CauSeq.lt_total`), either $f<\mathrm{const}(x^*)$, or $f\approx\mathrm{const}(x^*)$, or $\mathrm{const}(x^*)<f$. Rule out both strict cases:
- Suppose $f<\mathrm{const}(x^*)$, i.e. $\mathrm{Pos}(\mathrm{const}(x^*)-f)$: there exist $\varepsilon>0$ and $i\in\mathbb N$ such that $x^*-f_j\ge\varepsilon$ for all $j\ge i$. Rewriting $x^*-f_j\ge\varepsilon=\frac{\varepsilon}{2}+\frac{\varepsilon}{2}$ as $(x^*-\frac{\varepsilon}{2})-f_j\ge\frac{\varepsilon}{2}>0$ for all $j\ge i$ shows $f<\mathrm{const}(x^*-\frac{\varepsilon}{2})$! By the upper-bound observation above, $x^*-\frac{\varepsilon}{2}$ is then an upper bound for $s_f$, so $x^*=\operatorname{sSup}s_f\le x^*-\frac{\varepsilon}{2}$, contradicting $\varepsilon/2>0$.
- Suppose $\mathrm{const}(x^*)<f$, i.e. $\mathrm{Pos}(f-\mathrm{const}(x^*))$: there exist $\varepsilon>0$ and $i\in\mathbb N$ such that $f_j-x^*\ge\varepsilon$ for all $j\ge i$. Then $f_j-(x^*+\frac{\varepsilon}{2})\ge\frac{\varepsilon}{2}>0$ for all $j\ge i$, meaning $x^*+\frac{\varepsilon}{2}\in s_f$! Since $x^*$ bounds $s_f$ above, $x^*+\frac{\varepsilon}{2}\le x^*$, again contradicting $\varepsilon/2>0$.

Only $f\approx\mathrm{const}(x^*)$ remains, proving `CauSeq.IsComplete ℝ abs`. Furthermore, if $q_n\in\mathbb Q$ satisfies $\lvert(q_n:\mathbb R)-f_n\rvert<(n+1)^{-1}$ (chosen by `exists_rat_btwn`), then for any $\varepsilon>0$, combining $\lvert f_n-x^*\rvert<\varepsilon/2$ (`n ≥ N_1`) with $(n+1)^{-1}\le\varepsilon/2$ (`n ≥ N_2`) gives $\lvert(q_n:\mathbb R)-x^*\rvert<\varepsilon$ for $n\ge\max(N_1,N_2)$, so Lemma 1(3) (`Real.of_near`) yields $q\in\mathrm{CauSeq}(\mathbb Q,\lvert\cdot\rvert)$ and $\mathrm{Real.mk}(q)=x^*$.

(3) For choice-independence: if $\mathrm{IsLUB}(s,x_1)$ and $\mathrm{IsLUB}(s,x_2)$, then $x_1\le x_2$ and $x_2\le x_1$, so $x_1=x_2$ in `Real.partialOrder`. If $f\approx\mathrm{const}(x)$ in `CauSeq ℝ abs` (`lim_eq_of_equiv_const`, `Completion.lean:312–313`), symmetry and transitivity with `equiv_lim f : f ≈ const (lim f)` give $\mathrm{const}(x)\approx\mathrm{const}(\mathrm{lim}\,f)$, which by `const_equiv` (`CauSeq/Basic.lean:484–485`) forces $x=\mathrm{lim}\,f$; if $f\approx g$, then $f\approx\mathrm{const}(\mathrm{lim}\,g)$ gives $\mathrm{lim}\,f=\mathrm{lim}\,g$ (`lim_eq_lim_of_equiv`, `:315–316`). And since `Real.metricSpace` is a `MetricSpace`, distinct points $x\ne y$ have $\delta=\lvert x-y\rvert>0$ and disjoint balls $B(x,\delta/2)\cap B(y,\delta/2)=\emptyset$, so $\mathbb R$ is $T_2$ and `tendsto_nhds_unique` forces uniqueness of every proper filter limit.

Finally, let $\beta$ be any conditionally complete strictly ordered field (`Algebra/Order/CompleteField.lean:63–318`). First, $\beta$ is Archimedean (`to_archimedean`, `:63–70`): if $\mathbb N\cdot 1\subseteq\beta$ were bounded above by $x$, let $s^*=\operatorname{sSup}\{(m:\beta):m\in\mathbb N\}$; for every $m\in\mathbb N$, $(m+1:\beta)\le s^*$ gives $(m:\beta)\le s^*-1$, so $s^*\le s^*-1$, impossible. Thus for every $a\in\mathbb R$, the rational lower cut $C_\beta(a)=\{(q:\beta):q\in\mathbb Q,\;(q:\mathbb R)<a\}$ (`cutMap β a`, `:93–94`) is nonempty (`exists_rat_lt a`) and bounded above (`exists_rat_gt a`), so $\Phi(a)=\operatorname{sSup}C_\beta(a)\in\beta$ (`inducedMap ℝ β a`, `:165–166`) is well-defined, monotone, fixes $\mathbb Q$ (`inducedMap_rat`, `:173–181`), satisfies $(q:\beta)<\Phi(a)\iff(q:\mathbb R)<a$ (`coe_lt_inducedMap_iff`, `:194–201`), preserves addition because $C_\beta(a+b)=C_\beta(a)+C_\beta(b)$ by rational density (`cutMap_add`, `:127–140`, plus `csSup_add`), and preserves squares on $a>0$ (`:229–279`, hence all products via $(x+y)^2-x^2-y^2=2xy$ since $2\ne0$). Defining $\Psi:\beta\to\mathbb R$ by the reverse rational lower cut gives $\Psi(\Phi(a))=a$ and $\Phi(\Psi(b))=b$ (`inducedMap_inv_self`, `:217–218`) because both composites preserve all rational strict inequalities, and any ordered ring homomorphism $\Theta:\mathbb R\to\beta$ must agree with $\Phi$ because $\Theta(q)=q$ on $\mathbb Q$ and $(q:\mathbb R)<a\implies(q:\beta)=\Theta(q)\le\Theta(a)$ (`uniqueOrderRingHom`, `:311–317`). $\square$

[Lean, read] [Archimedean/Real/Basic.lean:59–146](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean#L59-L146) · [Archimedean/Real/Basic.lean:324–344](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean#L324-L344) · [CauSeq/Completion.lean:299–354](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Completion.lean#L299-L354) · [CompleteField.lean:63–318](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CompleteField.lean#L63-L318)

**Theorem 3 (`Real.instCompleteSpace`, the two-channel real majorant supply to §1.2.2.9, and quantitative series tail bounds).** Let $I$ be any index set.

1. *Filter completeness of $\mathbb R$ (`Metric.cauchySeq_iff'`, `isCauSeq_iff_cauchySeq`, `Real.instCompleteSpace`).*
   - For every sequence $u:\mathbb N\to\mathbb R$, the uniform filter condition `CauchySeq u` ($\mathrm{Cauchy}(\mathrm{map}(u,\mathrm{atTop}))$) is equivalent to the one-anchor condition `IsCauSeq abs u`, and if `CauchySeq u` holds then $c=\langle u,\dots\rangle\in\mathrm{CauSeq}(\mathbb R,\lvert\cdot\rvert)$ satisfies $\mathrm{Tendsto}(u,\mathrm{atTop},\mathcal N(c.\mathrm{lim}))$.
   - Upgrading sequential completeness via `Metric.complete_of_cauchySeq_tendsto` (§1.2.2.9 Theorem 3(1)) inhabits `Real.instCompleteSpace : CompleteSpace ℝ` (and on the closed ray $[0,\infty)$, `CompleteSpace ℝ≥0`).
2. *Supply to real majorant series and to §1.2.2.9 (`summable_iff_vanishing_norm` on $\mathbb R$, `summable_abs_iff`, `summable_of_sum_le`, `summable_of_sum_range_le`, `Summable.of_nonneg_of_le`, `hasSum_geometric_of_lt_one`).*
   - *Uniform-filter channel (`Real.instCompleteSpace`).* Instantiating §1.2.2.9 Theorem 3(1) at $E=\mathbb R$ yields
     $$
      \mathrm{Summable}(g)\iff\forall\varepsilon>0,\;\exists A_0\in\mathcal F(I),\;\forall T\in\mathcal F(I),\;T\cap A_0=\emptyset\implies\Bigl\lvert\sum_{i\in T}g(i)\Bigr\rvert<\varepsilon,
     $$
     and in one real dimension **unconditional summability coincides with absolute summability**: $\mathrm{Summable}(\lvert g\rvert)\iff\mathrm{Summable}(g)$ (`summable_abs_iff`).
   - *Order-supremum channel (`ConditionallyCompleteLinearOrder ℝ` + `OrderTopology ℝ`).* If $g:I\to\mathbb R$ satisfies $g(i)\ge0$ for all $i\in I$ and $\sum_{i\in u}g(i)\le c$ for every $u\in\mathcal F(I)$, then $g$ is unconditionally summable in $\mathbb R$ with
     $$
      \mathrm{HasSum}\Bigl(g,\;\sup_{u\in\mathcal F(I)}\sum_{i\in u}g(i)\Bigr)\qquad\text{and}\qquad\sum'_{i\in I}g(i)\le c
     $$
     (`summable_of_sum_le`, `Real.tsum_le_of_sum_le`; for $I=\mathbb N$, bounding initial segments $\sum_{k=0}^{n-1}g(k)\le c$ already suffices via `summable_of_sum_range_le` and `Real.tsum_le_of_sum_range_le`). Consequently, if $0\le g(i)\le f(i)$ for all $i\in I$ and $\mathrm{Summable}(f)$, then $\mathrm{Summable}(g)$ (`Summable.of_nonneg_of_le`), and for $0\le r<1$, $\mathrm{HasSum}(n\mapsto r^n,(1-r)^{-1})$ (`hasSum_geometric_of_lt_one`). Feeding any such summable $g:I\to\mathbb R$ into §1.2.2.9 Lemma 1(3) and Theorem 3(2) discharges the real majorant premise of `Summable.of_norm_bounded_eventually`, `Summable.of_norm_bounded`, and `Summable.of_norm` in every Banach space $E$.
3. *Summable step increments, tail error bounds, and the Bergh–Löfström completeness equivalence (`cauchySeq_of_dist_le_of_summable`, `dist_le_tsum_of_dist_le_of_tendsto`, `NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace`).*
   - Let $(X,\operatorname{dist})$ be any pseudometric space (`[PseudoMetricSpace X]`), $f:\mathbb N\to X$, and $d:\mathbb N\to\mathbb R$. If $\operatorname{dist}(f_n,f_{n+1})\le d_n$ for all $n\in\mathbb N$ and $\mathrm{Summable}(d)$ holds in $\mathbb R$, then `CauchySeq f` holds in $X$, and for any limit $a\in X$ with $\mathrm{Tendsto}(f,\mathrm{atTop},\mathcal N(a))$ and every $n\in\mathbb N$,
     $$
      \operatorname{dist}(f_n,a)\le\sum'_{m\in\mathbb N}d_{n+m}
     $$
     (specializing when $\operatorname{dist}(f_n,f_{n+1})\le C r^n$ with $r<1$ to $\operatorname{dist}(f_n,a)\le\frac{Cr^n}{1-r}$, `dist_le_of_le_geometric_of_tendsto`).
   - For any normed additive commutative group $E$ (`[NormedAddCommGroup E]`), `CompleteSpace E` holds **if and only if** every norm-summable sequence $u:\mathbb N\to E$ (meaning $\mathrm{Summable}(n\mapsto\lVert u_n\rVert)$ in $\mathbb R$) has convergent ordered partial sums $N\mapsto\sum_{k=0}^{N-1}u_k$ in $E$.

**Proof.** (1) In `PseudoMetricSpace ℝ` ($\operatorname{dist}(x,y)=\lvert x-y\rvert$), the metric entourages $\{(x,y):\lvert x-y\rvert<\varepsilon\}$ ($\varepsilon>0$) form a basis of $\mathcal U_{\mathbb R}$. Unfolding `CauchySeq u` against this basis (`Metric.cauchySeq_iff`, `MetricSpace/Cauchy.lean:59–61`) says $\forall\varepsilon>0,\;\exists N,\;\forall m,n\ge N,\;\lvert u_m-u_n\rvert<\varepsilon$, which implies the one-anchor form $\forall\varepsilon>0,\;\exists N,\;\forall n\ge N,\;\lvert u_n-u_N\rvert<\varepsilon$ (`Metric.cauchySeq_iff'`, `:64–66`, and conversely by `cauchy₂` in Lemma 1(1); cf. `isCauSeq_iff_cauchySeq`, `CauSeqFilter.lean:82–84`). Now read `Real.instCompleteSpace` (`UniformSpace/Real.lean:26–34`) line by line: given `hu : CauchySeq u`, `Metric.cauchySeq_iff'.1 hu` is literally `IsCauSeq abs u`, so `c = ⟨u, Metric.cauchySeq_iff'.1 hu⟩` has type `CauSeq ℝ abs`. Lemma 2(2) (`CauSeq.IsComplete ℝ abs`) supplies $c.\mathrm{lim}\in\mathbb R$ with `c.equiv_lim : LimZero (c - const abs c.lim)`. Given any neighborhood $s\in\mathcal N(c.\mathrm{lim})$, `Metric.mem_nhds_iff` supplies $\varepsilon>0$ with $B(c.\mathrm{lim},\varepsilon)\subseteq s$, and `c.equiv_lim ε ε0` supplies $N\in\mathbb N$ such that $\lvert u_n-c.\mathrm{lim}\rvert<\varepsilon$, hence $u_n\in B(c.\mathrm{lim},\varepsilon)\subseteq s$, for all $n\ge N$. Thus $\mathrm{Tendsto}(u,\mathrm{atTop},\mathcal N(c.\mathrm{lim}))$. Applying `Metric.complete_of_cauchySeq_tendsto` (`MetricSpace/Cauchy.lean:49–51`, which delegates via `EMetric.complete_of_cauchySeq_tendsto` to `UniformSpace.complete_of_cauchySeq_tendsto`, proved in §1.2.2.9 Theorem 3(1)) concludes `CompleteSpace ℝ`. Because $[0,\infty)=\mathrm{Ici}(0)$ is closed in $\mathbb R$, `isClosed_Ici.completeSpace_coe` (`UniformSpace/Real.lean:45–46`) immediately gives `CompleteSpace ℝ≥0`.

(2) With `Real.normedAddCommGroup` and `Real.instCompleteSpace` in place, §1.2.2.9 Theorem 3(1) applies at $E=\mathbb R$ to give `summable_iff_cauchySeq_finset` and `summable_iff_vanishing_norm`. For `summable_abs_iff` (`InfiniteSum/Order.lean:323–336`), set $I_+=\{i\in I:0\le g(i)\}$. In any complete uniform additive group, a family is summable on $I$ if and only if its restrictions to $I_+$ and $I_+^c$ are both summable (`summable_subtype_and_compl`, `InfiniteSum/Group.lean:301`, since restricting to a subset shrinks disjoint finite tails in Lemma 1(1) of §1.2.2.9, while conversely $S_g(F)=S_{g\vert_{I_+}}(F\cap I_+)+S_{g\vert_{I_+^c}}(F\setminus I_+)$). On $I_+$, $\lvert g(i)\rvert=g(i)$, while on $I_+^c$, $\lvert g(i)\rvert=-g(i)$ and negation is a topological group automorphism (`summable_neg_iff`); hence $\mathrm{Summable}(\lvert g\rvert)\iff\mathrm{Summable}(g\vert_{I_+})\wedge\mathrm{Summable}(-g\vert_{I_+^c})\iff\mathrm{Summable}(g)$.

For the order-supremum channel, suppose $g(i)\ge0$ for all $i\in I$ and $S_g(u)=\sum_{i\in u}g(i)\le c$ for all $u\in\mathcal F(I)$ (`summable_of_sum_le`, `InfiniteSum/Real.lean:84–88`). Nonnegativity makes $u\mapsto S_g(u)$ monotone on $(\mathcal F(I),\subseteq)$ (`Finset.sum_mono_set_of_nonneg`): if $u\subseteq v$, $S_g(v)-S_g(u)=\sum_{i\in v\setminus u}g(i)\ge0$. By Lemma 2(1) (`ConditionallyCompleteLinearOrder ℝ`), the nonempty bounded-above range $\{S_g(u):u\in\mathcal F(I)\}$ has least upper bound $S^*=\sup_{u\in\mathcal F(I)}S_g(u)\le c$. Because $\mathbb R$ carries `OrderTopology ℝ`, `tendsto_atTop_ciSup` (`MonotoneConvergence.lean:68–75, 116–123`) proves $S_g\to S^*$ along `atTop`: for every $b<S^*$ there exists $u_0\in\mathcal F(I)$ with $b<S_g(u_0)\le S_g(u)$ for all $u\supseteq u_0$, while for every $b'>S^*$ every $u\in\mathcal F(I)$ satisfies $S_g(u)\le S^*<b'$. Thus $\mathrm{HasSum}(g,S^*)$ and $\sum'_{i\in I}g(i)=S^*\le c$ (`Real.tsum_le_of_sum_le`, `:95–97`). When $I=\mathbb N$ and $\sum_{k=0}^{n-1}g(k)\le c$ for all $n\in\mathbb N$, either every finite set $u\subset\mathbb N$ lies inside $\{0,\dots,N-1\}$ for $N=1+\max u$ (giving $S_g(u)\le S_g(\mathrm{range}\,N)\le c$ directly), or as in `summable_of_sum_range_le` (`:89–94` via `NNReal.not_summable_iff_tendsto_nat_atTop`, `ENNReal.lean:389–406`), non-summability of a monotone partial-sum sequence would force $\sum_{k<n}g(k)\to+\infty$, contradicting $\sum_{k<n}g(k)\le c$. For `Summable.of_nonneg_of_le` (`ENNReal.lean:530–536`), Mathlib lifts $0\le g\le f$ to $\mathbb R_{\ge0}$ (`NNReal.summable_coe`), pushes into the complete lattice $\mathbb R_{\ge0\infty}$ where $\sum'_i(g_i:\mathbb R_{\ge0\infty})\le\sum'_i(f_i:\mathbb R_{\ge0\infty})<\infty$ (`NNReal.exists_le_hasSum_of_le`, `:362–375`), and pulls back to $\mathbb R$ (equivalently on $\mathbb R$, every finite sum satisfies $S_g(u)\le S_f(u)\le\sum'_i f_i$, so `summable_of_sum_le` applies directly). For the geometric series (`hasSum_geometric_of_lt_one`, `SpecificLimits/Basic.lean:316–323`), first take $r=0$. The term at $n=0$ is $1$, and every later term is zero, so the unordered sum is $1$.

For $0<r<1$, set $a=1/r-1>0$. Bernoulli's inequality gives $(1+a)^n\ge 1+na$ for every $n\in\mathbb N$. Consequently,
$$
0\le r^n\le\frac{1}{1+n(1/r-1)}\longrightarrow 0.
$$
The finite geometric identity $\sum_{k=0}^{n-1}r^k=(1-r^n)(1-r)^{-1}$ gives $\sum_{k=0}^{n-1}r^k\to(1-r)^{-1}$. By nonnegativity, `hasSum_iff_tendsto_nat_of_nonneg` (`ENNReal.lean:558–563`, or §9.4.10's `hasSum_iff_tendsto_nat_of_summable_norm`) upgrades this to unconditional `HasSum`.

(3) Suppose $\operatorname{dist}(f_n,f_{n+1})\le d_n$ for all $n\in\mathbb N$ with `hd : Summable d` in $\mathbb R$ (`cauchySeq_of_dist_le_of_summable`, `InfiniteSum/Real.lean:27–33` and `ENNReal.lean:588–605`). Note $0\le\operatorname{dist}(f_n,f_{n+1})\le d_n$ forces $d_n\ge0$. By induction on $m\ge n$ (`edist_le_Ico_sum_of_edist_le`, `EMetricSpace/Basic.lean:36–58`), the polygon triangle inequality gives
$$
 \operatorname{dist}(f_n,f_m)\le\sum_{k=n}^{m-1}\operatorname{dist}(f_k,f_{k+1})\le\sum_{k=n}^{m-1}d_k=\sum_{k=0}^{m-1}d_k-\sum_{k=0}^{n-1}d_k.
$$
Because `hd` holds, Lemma 2(3) of §1.2.2.9 (`HasSum.tendsto_sum_nat`) makes the ordered partial sums $D_m=\sum_{k=0}^{m-1}d_k$ converge in $\mathbb R$, hence form a Cauchy sequence in $\mathbb R$: for every $\varepsilon>0$ there exists $N$ such that $D_m-D_N<\varepsilon$ for all $m\ge N$, whence $\operatorname{dist}(f_m,f_N)\le D_m-D_N<\varepsilon$, proving `CauchySeq f` via `Metric.cauchySeq_iff'`. If moreover $f_m\to a$ in $X$ (`dist_le_tsum_of_dist_le_of_tendsto`, `InfiniteSum/Real.lean:37–45`), then for every $m\ge n$, shifting the index by $j=k-n$ rewrites $\sum_{k=n}^{m-1}d_k=\sum_{j=0}^{m-n-1}d_{n+j}\le\sum'_{j\in\mathbb N} d_{n+j}$ (`Summable.sum_le_tsum` applied to $d\circ(n+\cdot)$, summable by injective reindexing in §1.2.2.9 Lemma 2(1)). Continuity of $\operatorname{dist}(f_n,\cdot)$ sends $m\to\infty$ to preserve the closed upper bound $\operatorname{dist}(f_n,a)\le\sum'_{j\in\mathbb N} d_{n+j}$.

Finally, let $E$ be a `NormedAddCommGroup` (`Normed/Group/Completeness.lean:39–90`, `[BerghLofstrom1976]`, Lemma 2.2.1). If `[CompleteSpace E]` holds and $\mathrm{Summable}(n\mapsto\lVert u_n\rVert)$ holds in $\mathbb R$, set $P_n=\sum_{k=0}^{n-1}u_k$; then $\operatorname{dist}(P_n,P_{n+1})=\lVert u_n\rVert$, so `cauchySeq_of_dist_le_of_summable` makes $(P_n)$ Cauchy and completeness gives a limit (`summable_imp_tendsto_of_complete`, `:78–81`). Conversely (`completeSpace_of_summable_imp_tendsto`, `:55–74`), assume every norm-summable sequence in $E$ has convergent ordered partial sums, and let $u:\mathbb N\to E$ satisfy `CauchySeq u`. Applying `Metric.exists_subseq_bounded_of_cauchySeq` (`MetricSpace/Cauchy.lean:152–161`) with tolerances $b_k=2^{-k}>0$ extracts a strictly increasing $\varphi:\mathbb N\to\mathbb N$ such that $\lVert u_m-u_{\varphi(k)}\rVert<2^{-k}$ for all $m\ge\varphi(k)$; in particular, setting $v_k=u_{\varphi(k+1)}-u_{\varphi(k)}$ gives $0\le\lVert v_k\rVert\le 2^{-k}$. By part (2) (`Summable.of_nonneg_of_le` with `summable_geometric_two`), $k\mapsto\lVert v_k\rVert$ is **summable in $\mathbb R$** (`exists_subseq_summable_dist_of_cauchySeq`, `:39–46`). By hypothesis on $E$, the telescoping partial sums $\sum_{k=0}^{K-1}v_k=u_{\varphi(K)}-u_{\varphi(0)}$ converge to some $a\in E$, so $u_{\varphi(K)}\to a+u_{\varphi(0)}$; since $u$ is Cauchy, the full sequence converges to $a+u_{\varphi(0)}$ (`tendsto_nhds_of_cauchySeq_of_subseq`), and `Metric.complete_of_cauchySeq_tendsto` yields `CompleteSpace E`. $\square$

[Lean, read] [UniformSpace/Real.lean:26–46](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Real.lean#L26-L46) · [MetricSpace/Cauchy.lean:49–66](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/MetricSpace/Cauchy.lean#L49-L66) · [MetricSpace/Cauchy.lean:152–161](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/MetricSpace/Cauchy.lean#L152-L161) · [CauSeqFilter.lean:27–100](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/MetricSpace/CauSeqFilter.lean#L27-L100) · [EMetricSpace/Basic.lean:36–58](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/EMetricSpace/Basic.lean#L36-L58) · [EMetricSpace/Basic.lean:115–117](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/EMetricSpace/Basic.lean#L115-L117) · [MonotoneConvergence.lean:68–123](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Order/MonotoneConvergence.lean#L68-L123) · [InfiniteSum/Order.lean:302–336](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Order.lean#L302-L336) · [InfiniteSum/Real.lean:27–101](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Real.lean#L27-L101) · [InfiniteSum/ENNReal.lean:362–406](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L362-L406) · [InfiniteSum/ENNReal.lean:530–605](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L530-L605) · [NNReal/Lemmas.lean:132–156](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Instances/NNReal/Lemmas.lean#L132-L156) · [SpecificLimits/Basic.lean:316–344](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecificLimits/Basic.lean#L316-L344) · [SpecificLimits/Basic.lean:518–547](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecificLimits/Basic.lean#L518-L547) · [Normed/Group/Completeness.lean:39–90](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/Completeness.lean#L39-L90)

**Hand calculation A (rational approximations to $\sqrt{2}$: Heron's Pell recurrence versus the integer-grid `exists_isLUB` sequence, and their quotient equivalence).** Define $r:\mathbb N\to\mathbb Q$ recursively by
$$
 r_0=\frac{3}{2},\qquad r_{n+1}=\frac{1}{2}\Bigl(r_n+\frac{2}{r_n}\Bigr)=\frac{r_n^2+2}{2r_n}\qquad(n\in\mathbb N).
$$

1. *Exact Pell numerators, quadratic defects, and purely rational `IsCauSeq abs r`.* Writing $r_n=p_n/q_n$ with $(p_0,q_0)=(3,2)$, $p_{n+1}=p_n^2+2q_n^2$, and $q_{n+1}=2p_nq_n$ yields unit-Pell solutions $p_n^2-2q_n^2=(p_{n-1}^2-2q_{n-1}^2)^2=\dots=(3^2-2\cdot 2^2)^{2^n}=1$ in $\mathbb Z$ (automatically coprime since $p_n^2-2q_n^2=1$):
   $$
    r_0=\frac{3}{2},\quad r_1=\frac{17}{12},\quad r_2=\frac{577}{408},\quad r_3=\frac{665857}{470832},\quad r_4=\frac{886731088897}{627013566048}.
   $$
   In $\mathbb Q$, the quadratic defect $e_n=r_n^2-2=\frac{1}{q_n^2}$ satisfies $e_0=\frac{1}{4}$ and the exact identity
   $$
    e_{n+1}=r_{n+1}^2-2=\frac{(r_n^2+2)^2-8r_n^2}{4r_n^2}=\frac{(r_n^2-2)^2}{4r_n^2}=\frac{e_n^2}{4r_n^2}>0,
   $$
   giving $e_1=\frac{1}{144}$, $e_2=\frac{1}{166464}$, $e_3=\frac{1}{221682772224}$, and $e_4=\frac{1}{393146012008229658338304}$. Because $r_n>0$ and $r_n^2=2+e_n>2>\frac{16}{9}$, every iterate satisfies $\frac{4}{3}<r_{n+1}<r_n\le\frac{3}{2}$ with exact step
   $$
    r_n-r_{n+1}=\frac{r_n^2-2}{2r_n}=\frac{e_n}{2r_n}=\frac{1}{2p_nq_n}=\frac{1}{q_{n+1}}>0.
   $$
   Furthermore, $4r_n^2>8$ and $0<e_n\le\frac{1}{4}$ imply $e_{n+1}<\frac{(1/4)e_n}{8}=\frac{1}{32}e_n$, so by induction $0<e_n\le\frac{1}{4}\cdot 32^{-n}$ and $0<r_n-r_{n+1}<\frac{e_n}{2}\le\frac{1}{8}\cdot 32^{-n}$ for all $n\in\mathbb N$. Without mentioning any irrational number, rational telescoping for $k\ge j\ge N$ gives
   $$
    \lvert r_k-r_j\rvert=r_j-r_k=\sum_{n=j}^{k-1}(r_n-r_{n+1})\le\frac{1}{8}\sum_{n=j}^{k-1}32^{-n}<\frac{4}{31}\cdot 32^{-N},
   $$
   proving `h_heron : IsCauSeq abs r` in $\mathbb Q$. Passing to the quotient $\alpha=\mathrm{Real.mk}\,\langle r,h_{\mathrm{heron}}\rangle\in\mathbb R$, ring homomorphism properties (`Real.mk_mul`, `Real.mk_const`) give $\alpha^2-2=\mathrm{Real.mk}(r^2-\mathrm{const}\,2)=0$ because $\lvert r_n^2-2\rvert=e_n\le\frac{1}{4}\cdot 32^{-n}\to0$ (`mk_eq_zero.2`), and Lemma 1(3) (`le_mk_of_forall_le` with $r_n\ge\frac{4}{3}$) gives $\alpha\ge\frac{4}{3}>0$. By `Real.sqrt_eq_iff_eq_sq` (`Analysis/Real/Sqrt.lean:183–185`), $\alpha=\sqrt{2}$.

2. *Comparison with Lemma 2(1)'s integer-grid sequence and representative independence.* Apply Lemma 2(1)'s `exists_isLUB` construction to $S=\{x\in\mathbb R:x\le0\;\vee\;x^2<2\}$ ($0\in S$, bounded above by $2$). For $n\ge1$, a positive integer $m$ satisfies $(m/n)\in S$ iff $m^2<2n^2$ (`f_grid(0)=0`), so $f_{\mathrm{grid}}(n)=\lfloor\sqrt{2}\,n\rfloor$ (strict because $2n^2$ is never a square for $n\ge1$), producing
   $$
    g(1)=1,\quad g(2)=1,\quad g(3)=\frac{4}{3},\quad g(4)=\frac{5}{4},\quad g(5)=\frac{7}{5},\quad g(10)=\frac{7}{5},\quad g(12)=\frac{4}{3},\quad g(100)=\frac{141}{100}.
   $$
   Although $r$ approaches from above ($r_n^2>2$) and $g$ from below ($g(n)^2<2<\bigl(g(n)+\frac{1}{n}\bigr)^2$), with nonzero finite differences $r_1-g(1)=\frac{5}{12}$, $r_2-g(2)=\frac{169}{408}$, $r_3-g(3)=\frac{38081}{470832}$, and $r_4-g(4)=\frac{102964131337}{627013566048}$, for every $n\ge1$ we have $g(n)\ge1$, $r_n>\frac{4}{3}$, and $g(n)\le\frac{3}{2}$, so
   $$
    0<r_n-g(n)=\frac{r_n^2-g(n)^2}{r_n+g(n)}<\frac{e_n+\bigl((g(n)+n^{-1})^2-g(n)^2\bigr)}{7/3}\le\frac{\frac{1}{4}\cdot 32^{-n}+\frac{4}{n}}{7/3}\longrightarrow 0\quad(n\to\infty).
   $$
   Hence $\mathrm{LimZero}(r-g)$, i.e. $r\approx g$ in `CauSeq ℚ abs`, and `Real.mk_eq` identifies $\mathrm{Real.mk}(r)=\mathrm{Real.mk}(g)=\operatorname{sSup}S=\sqrt{2}$ without any dependence on which representative sequence was constructed. [Expository]

**Hand calculation B (absolutely summable step increments, a priori tail error bounds, and Banach majorant supply to §1.2.2.9).**

1. *Telescoping step control on $\mathbb R$ (`cauchySeq_of_dist_le_of_summable` and `dist_le_tsum_of_dist_le_of_tendsto`).* Write the Heron iterates as ordered partial sums $r_N=r_0+\sum_{n=0}^{N-1}u_n$ of rational increments $u_n=r_{n+1}-r_n=-\frac{1}{q_{n+1}}$:
   $$
    u_0=-\frac{1}{12},\qquad u_1=-\frac{1}{408},\qquad u_2=-\frac{1}{470832},\qquad u_3=-\frac{1}{627013566048}.
   $$
   In Hand calculation A(1) we proved $\operatorname{dist}(r_n,r_{n+1})=\lvert u_n\rvert\le d_n:=\frac{1}{8}\cdot 32^{-n}$ for all $n\in\mathbb N$ (at $n=0,1,2$: $\frac{1}{12}<\frac{1}{8}$, $\frac{1}{408}<\frac{1}{256}$, $\frac{1}{470832}<\frac{1}{8192}$). By Theorem 3(2) (`hasSum_geometric_of_lt_one` at ratio $\frac{1}{32}\in[0,1)$, scaled by $\frac{1}{8}$), $d$ is summable in $\mathbb R$ with tail sum
   $$
    \sum'_{m\in\mathbb N}d_{N+m}=\frac{1}{8}\cdot 32^{-N}\cdot\Bigl(1-\frac{1}{32}\Bigr)^{-1}=\frac{4}{31}\cdot 32^{-N}.
   $$
   Theorem 3(3) (`cauchySeq_of_dist_le_of_summable` + `Real.instCompleteSpace` + `dist_le_tsum_of_dist_le_of_tendsto`) therefore certifies both convergence $r_N\to\sqrt{2}$ and the explicit **a priori** geometric tail bound at every step $N\ge0$, alongside the sharp **a posteriori** rational bracket $[r_N^\flat,r_N]$ where $r_N^\flat=\frac{2}{r_N}<\sqrt{2}<r_N$ (since $(r_N^\flat)^2=\frac{4}{2+e_N}<2$ and $r_N-r_N^\flat=\frac{e_N}{r_N}=2\lvert u_N\rvert$):
   - $N=0$: $r_0=\frac{3}{2}$, $r_0^\flat=\frac{4}{3}$, exact bracket width $\frac{1}{6}$, geometric tail bound $\lvert r_0-\sqrt{2}\rvert\le\frac{4}{31}$;
   - $N=1$: $r_1=\frac{17}{12}$, $r_1^\flat=\frac{24}{17}$, bracket width $\frac{1}{204}$, geometric tail bound $\lvert r_1-\sqrt{2}\rvert\le\frac{1}{248}$;
   - $N=2$: $r_2=\frac{577}{408}$, $r_2^\flat=\frac{816}{577}$, bracket width $\frac{1}{235416}<\frac{1}{7936}$ (geometric tail bound);
   - $N=3$: $r_3=\frac{665857}{470832}$, $r_3^\flat=\frac{941664}{665857}$, bracket width $\frac{1}{313506783024}<\frac{1}{253952}$ (already 11 correct decimal digits!).

2. *Order-supremum majorant supply (`summable_of_sum_le`) into §1.2.2.9 (`Summable.of_norm_bounded`).* Now mirror the exact two-step pattern used in archive A2 (`LPartialSum.lean:124–133`). On $I=\mathbb N$, define the nonnegative rational/real majorant $w_n=\frac{1}{(n+1)(n+2)}=\frac{1}{n+1}-\frac{1}{n+2}>0$. For every initial segment $\mathrm{range}\,N=\{0,\dots,N-1\}$, telescoping gives
   $$
    \sum_{n=0}^{N-1}w_n=\sum_{n=0}^{N-1}\Bigl(\frac{1}{n+1}-\frac{1}{n+2}\Bigr)=1-\frac{1}{N+1}\le 1.
   $$
   Theorem 3(2) (`summable_of_sum_range_le` and `Real.tsum_le_of_sum_range_le`, backed by `ConditionallyCompleteLinearOrder ℝ`) immediately certifies `hw : Summable w` in $\mathbb R$ with $\sum'_{n\in\mathbb N} w_n=1$ and exact tail $\sum'_{m\in\mathbb N} w_{N+m}=\frac{1}{N+1}$. Now let $E=C([0,1],\mathbb C)$ with supremum norm $\lVert\cdot\rVert_\infty$ (`CompleteSpace` since $\mathbb C\cong\mathbb R^2$ inherits completeness from `Real.instCompleteSpace`), and consider the function series $f_n(t)=\frac{(-1)^n e^{2\pi i n t}}{(n+1)(n+2)+1}$. For every $n\in\mathbb N$,
   $$
    \lVert f_n\rVert_\infty=\frac{1}{(n+1)(n+2)+1}<w_n.
   $$
   Feeding `hw` into §1.2.2.9 Theorem 3(2) (`Summable.of_norm_bounded`) proves unconditional summability of $(f_n)$ in $C([0,1],\mathbb C)$ to a continuous limit $F\in C([0,1],\mathbb C)$, and applying Theorem 3(3) (`dist_le_tsum_of_dist_le_of_tendsto`) to the partial sums $F_N=\sum_{n=0}^{N-1}f_n$ bounds the uniform truncation error at $N=4$ (`w_0+w_1+w_2+w_3 = 1/2+1/6+1/12+1/20 = 4/5`) by
   $$
    \lVert F_4-F\rVert_\infty\le\sum'_{m\in\mathbb N}w_{4+m}=1-\frac{4}{5}=\frac{1}{5}
   $$
   (whereas the actual four-term norm sum is $\frac{1}{3}+\frac{1}{7}+\frac{1}{13}+\frac{1}{21}=\frac{164}{273}<\frac{4}{5}$). [Expository]

**Strict boundary in $\mathbb Q$ (why the same Cauchy sequence and the same norm-summable series fail to converge when `Real.instCompleteSpace` is removed).** Equip $\mathbb Q$ with its induced metric $\operatorname{dist}(x,y)=\lvert(x:\mathbb R)-(y:\mathbb R)\rvert$ (`Topology/Instances/Rat.lean:27–44`) and norm $\lVert q\rVert=\lvert(q:\mathbb R)\rvert$ (`Normed/Group/Rat.lean:17–24`). Because $\iota=\mathrm{Rat.cast}:\mathbb Q\hookrightarrow\mathbb R$ is a uniform embedding (`Rat.isUniformEmbedding_coe_real`), pulling back Hand calculation A(1) gives `CauchySeq r` in $\mathbb Q$; likewise, the rational increment family $v_0=\frac{3}{2}$, $v_{n+1}=u_n=r_{n+1}-r_n\in\mathbb Q$ ($n\ge0$) has partial sums $\sum_{k=0}^{N}v_k=r_N\in\mathbb Q$ and finite real norm sum
$$
 \sum'_{n\in\mathbb N}\lVert v_n\rVert=\frac{3}{2}+\sum'_{n\in\mathbb N}(r_n-r_{n+1})=\frac{3}{2}+\Bigl(\frac{3}{2}-\sqrt{2}\Bigr)=3-\sqrt{2}<\frac{13}{8}<\infty\quad\text{in }\mathbb R.
$$
The following completeness conclusions fail inside $\mathbb Q$:

1. *Explicit rational distance barrier against every candidate $q\in\mathbb Q$ (purely over $\mathbb Z$ and $\mathbb Q$).* Let $q=a/b\in\mathbb Q$ be arbitrary, written in lowest terms with $a\in\mathbb Z$, $b\in\mathbb N$, $b\ge1$, and $\gcd(\lvert a\rvert,b)=1$. First, $a^2\ne 2b^2$ in $\mathbb Z$ (matching `irrational_sqrt_two`, `Irrational.lean:61–76, 145–146`): if $a^2=2b^2$, then $2\mid a^2\implies 2\mid a$; writing $a=2k$ gives $4k^2=2b^2\implies b^2=2k^2\implies 2\mid b$, contradicting $\gcd(\lvert a\rvert,b)=1$. Because $a^2$ and $2b^2$ are distinct integers, $\lvert a^2-2b^2\rvert\ge 1$, so
   $$
    \lvert q^2-2\rvert=\frac{\lvert a^2-2b^2\rvert}{b^2}\ge\frac{1}{b^2}.
   $$
   Now bound $\lvert r_n-q\rvert$ from below on a tail of $\mathbb N$:
   - If $q\le0$, then $r_n>\frac{4}{3}$ gives $\lvert r_n-q\rvert=r_n-q>\frac{4}{3}$ for all $n\ge0$.
   - If $q>2$, then $r_n\le\frac{3}{2}$ gives $\lvert r_n-q\rvert=q-r_n>\frac{1}{2}$ for all $n\ge0$.
   - If $0<q\le 2$, then $0<r_n+q\le\frac{3}{2}+2=\frac{7}{2}$ for all $n\ge0$. Choose $N_b\in\mathbb N$ with $32^{N_b}\ge\frac{b^2}{2}$, so that $0<e_n=r_n^2-2\le\frac{1}{4}\cdot 32^{-n}\le\frac{1}{2b^2}$ for all $n\ge N_b$. By the reverse triangle inequality in $\mathbb Q$, $\lvert r_n^2-q^2\rvert=\lvert(2-q^2)+e_n\rvert\ge\lvert q^2-2\rvert-e_n\ge\frac{1}{b^2}-\frac{1}{2b^2}=\frac{1}{2b^2}$, whence for **every** $n\ge N_b$,
     $$
      \lvert r_n-q\rvert=\frac{\lvert r_n^2-q^2\rvert}{r_n+q}\ge\frac{1/(2b^2)}{7/2}=\frac{1}{7b^2}>0.
     $$
   Concretely: at $q=\frac{7}{5}$ ($b=5$, $7^2-2\cdot 5^2=-1$, $N_5=1$ since $32^1\ge\frac{25}{2}$, barrier $\frac{1}{175}$), $\lvert r_1-\frac{7}{5}\rvert=\frac{1}{60}>\frac{1}{175}$ and $\lvert r_2-\frac{7}{5}\rvert=\frac{29}{2040}>\frac{1}{175}$; even if one tests the Heron term $q=\frac{17}{12}=r_1$ itself ($b=12$, $17^2-2\cdot 12^2=+1$, $N_{12}=2$ since $32^2=1024\ge 72$, barrier $\frac{1}{1008}$), although $\lvert r_1-q\rvert=0$ at $n=1$, every $n\ge2$ satisfies $r_n\le r_2=\frac{577}{408}$, so $\lvert r_n-\frac{17}{12}\rvert=\frac{17}{12}-r_n\ge\frac{1}{408}>\frac{1}{1008}$! Thus $\neg\exists q\in\mathbb Q,\;\mathrm{Tendsto}(r,\mathrm{atTop},\mathcal N(q))$, certifying $\neg\mathrm{CompleteSpace}\,\mathbb Q$.
2. *Failure of `Summable.of_norm` and `map_tsum` on $\mathbb Q\hookrightarrow\mathbb R$.* Because any unordered sum $q\in\mathbb Q$ of $(v_n)$ would force ordered partial sums $\sum_{k\le N}v_k=r_N\to q$ (§1.2.2.9 Lemma 2(3)), $(v_n)$ is **not** `Summable` in $\mathbb Q$ despite $\mathrm{Summable}(n\mapsto\lVert v_n\rVert)$ in $\mathbb R$ — witnessing the nontrivial implication of Theorem 3(3) (`NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace`) on a one-dimensional field! Moreover, in $\mathbb Q$, Lean's totalized `tsum` assigns $\sum'_{n\in\mathbb N}v_n=0\in\mathbb Q$ (`tsum_eq_zero_of_not_summable`), so the continuous additive uniform embedding $\iota=\mathrm{Rat.cast}:\mathbb Q\hookrightarrow\mathbb R$ (dense by `Rat.isDenseEmbedding_coe_real`, hence **not closed** because $\sqrt{2}\in\overline{\iota(\mathbb Q)}\setminus\iota(\mathbb Q)$) satisfies
   $$
    \iota\Bigl(\sum'_{n\in\mathbb N}v_n\Bigr)=\iota(0)=0\;\ne\;\sqrt{2}=\sum'_{n\in\mathbb N}\iota(v_n),
   $$
   confirming on $\mathbb Q\subset\mathbb R$ why `IsClosedEmbedding.map_tsum` in §1.2.2.9 Theorem 3(3) requires closed range.
3. *Failure of `exists_isLUB` in $\mathbb Q$ (Dedekind's rational gap).* The nonempty subset $S_{\mathbb Q}=\{q\in\mathbb Q:q>0,\;q^2<2\}\subset\mathbb Q$ ($1\in S_{\mathbb Q}$, bounded above by $2$) has **no** least upper bound in $\mathbb Q$ (`[Dedekind1872]`, §IV): for every $q>0$ in $\mathbb Q$ with $q^2\ne2$, the rational Mobius step $q'=\frac{2q+2}{q+2}=q+\frac{2-q^2}{q+2}\in\mathbb Q$ satisfies $2-q'^2=\frac{2(2-q^2)}{(q+2)^2}$; thus if $q\in S_{\mathbb Q}$ ($q^2<2$), then $q'>q$ and $q'\in S_{\mathbb Q}$ (e.g. $1\mapsto\frac{4}{3}\mapsto\frac{7}{5}\mapsto\frac{24}{17}$, so $S_{\mathbb Q}$ has no maximum), whereas if $q$ is a rational upper bound of $S_{\mathbb Q}$ ($q>0$ and $q^2>2$, since $q^2=2$ is impossible), then $0<q'<q$ with $q'^2>2$, so $q'$ is a strictly smaller rational upper bound! [Expository]

**Remarks.**

1. *Why Mathlib builds $\mathbb R$ via Cantor quotients before proving Dedekind suprema.* In classical exposition, Dedekind cuts (`[Dedekind1872]`, §§IV–V) give `exists_isLUB` almost immediately at the cost of tedious case-splits for signed multiplication and reciprocals, whereas Cantor's fundamental sequences (`[Cantor1872]`, §1, pp. 123–126; cf. Tao `[TaoAnalysisI]`, Ch. 5, §§5.1–5.5) make the ring structure effortless (`Data/Real/Basic.lean:187–209`) while shifting the work to completeness. Note also that Cantor himself (§1, pp. 125–126) states the correspondence between his second-order sequence domain *Gebiet $C$* (Cauchy sequences of elements of $\mathbb Q\cup B$) and *Gebiet $B$*. In Lean (`[Mathlib2020]`, §3), Carneiro avoids choosing rational representatives from quotient classes during `cauSeq_converges` by detouring through the canonical integer floor grid $f_{\mathrm{grid}}(n)/n$ (`Archimedean/Real/Basic.lean:59–109`) to establish `exists_isLUB` first, and then proving `ConditionallyCompleteLinearOrderedField.inducedOrderRingIso` (`CompleteField.lean:284–318`) so downstream files can treat $\mathbb R$ interchangeably via Cauchy quotients, Dedekind suprema, or complete metric filters.
2. *Separation, totalized defaults, and the §1.2.2.9 audit boundary.* Both `SupSet ℝ` (`sSup s = 0` when $s=\emptyset$ or $\neg\mathrm{BddAbove}(s)$, `Archimedean/Real/Basic.lean:120, 171, 189`) and `tsum` (`∑' i, x i = 0` when $\neg\mathrm{Summable}(x)$, `InfiniteSum/Defs.lean:201`) totalize partial analytic operations by returning $0$ outside their convergence/boundedness domain; accordingly, every order inequality such as `csSup_le` or `le_csSup` requires explicit `Nonempty` and `BddAbove` witnesses (just as `ContinuousLinearMap.map_tsum` requires `Summable`). When a valid witness **does** exist, uniqueness of the chosen value in $\mathbb R$ relies on antisymmetry (for `sSup`) and on Hausdorff separation `[T2Space ℝ]` supplied by `Real.metricSpace` (for `Tendsto` and `HasSum`). Preserving the post-audit precision note on [§1.2.2.9](#1229-unordered-summation-finite-tail-cauchy-criteria-and-banach-completeness): in a general topological commutative monoid $M$, a finitely supported family $x$ always satisfies $\mathrm{HasSum}(x,\sum_{i\in\operatorname{supp}(x)}x_i)$, while deducing the equality $a=\sum_{i\in\operatorname{supp}(x)}x_i$ from an arbitrary $\mathrm{HasSum}(x,a)$ in §1.2.2.9 Lemma 2(3) requires `[T2Space M]` (`HasSum.unique`), which holds automatically in $\mathbb R$, $\mathbb Q$, and every `NormedAddCommGroup` (unlike indiscrete zero-seminorm spaces).

| Declaration read at R3 here | Direct consumers in §1.2.2.9, Mathlib, and archive A2 | Role in the book |
|---|---|---|
| `Real`, `Real.mk`, `Real.instField`, `Real.linearOrder`, `le_mk_of_forall_le`, `mk_le_of_forall_le`, `Real.instArchimedean`, `Real.of_near` ([Data/Real/Basic.lean:36–560](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Real/Basic.lean#L36-L560), [Archimedean/Real/Basic.lean:31–53](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean#L31-L53)) | `Real.exists_isLUB` (`:59–109`), `Real.pseudoMetricSpace` ([Pseudo/Defs.lean:1125](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L1125)), `Real.normedAddCommGroup` ([Normed/Group/Real.lean:55](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/Real.lean#L55)), `Rat.instMetricSpace` ([Instances/Rat.lean:27](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Instances/Rat.lean#L27)) | Lemma 1(1)–(3), Hand calculation A(1), and the $\mathbb Q\hookrightarrow\mathbb R$ boundary |
| `Real.exists_isLUB`, `ConditionallyCompleteLinearOrder ℝ`, `Real.cauSeq_converges`, `CauSeq.IsComplete ℝ abs`, `inducedOrderRingIso` ([Archimedean/Real/Basic.lean:59–146, 324–344](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean#L59-L146), [CompleteField.lean:284–318](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CompleteField.lean#L284-L318)) | `Real.instCompleteSpace` ([UniformSpace/Real.lean:26–34](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Real.lean#L26-L34)), `tendsto_atTop_ciSup` ([MonotoneConvergence.lean:116](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Order/MonotoneConvergence.lean#L116)), `summable_of_sum_le` ([InfiniteSum/Real.lean:84](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Real.lean#L84)) | Lemma 2(1)–(3) and Hand calculation A(2) |
| `Real.instCompleteSpace`, `isCauSeq_iff_cauchySeq`, `summable_abs_iff` ([UniformSpace/Real.lean:26–34](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Real.lean#L26-L34), [CauSeqFilter.lean:82–100](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/MetricSpace/CauSeqFilter.lean#L82-L100), [InfiniteSum/Order.lean:324–336](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Order.lean#L324-L336)) | Discharges `Real.instCompleteSpace` in [§1.2.2.9](#1229-unordered-summation-finite-tail-cauchy-criteria-and-banach-completeness) (`cauchySeq_finset_of_norm_bounded_eventually` at [Normed/Group/InfiniteSum.lean:61](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/InfiniteSum.lean#L61) $\to$ `Summable.of_norm_bounded`, `Summable.of_norm`) and `OrthogonalFamily.summable_iff_norm_sq_summable` ([Subspace.lean:201](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Subspace.lean#L201), [§1.2.2.8](#1228-hilbert-expansion-and-the-norm-behind-poisson-summation)) | Theorem 3(1)–(2), closing §1.2.2.9's named `Real.instCompleteSpace` input |
| `summable_of_sum_le`, `summable_of_sum_range_le`, `Summable.of_nonneg_of_le`, `hasSum_geometric_of_lt_one`, `cauchySeq_of_dist_le_of_summable`, `dist_le_tsum_of_dist_le_of_tendsto`, `summable_imp_tendsto_iff_completeSpace` ([InfiniteSum/Real.lean:27–101](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Real.lean#L27-L101), [ENNReal.lean:530–536](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L530-L536), [SpecificLimits/Basic.lean:316–344, 518–547](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecificLimits/Basic.lean#L316-L344), [Completeness.lean:39–90](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/Completeness.lean#L39-L90)) | Archive A2 `LPartialSum.lean:124–133` (`summable_of_sum_range_le` $\to$ `Summable.of_nonneg_of_le` $\to$ `norm_tsum_le_tsum_norm`), `ThetaSummable.lean:28–52` (`summable_of_sum_le` & `of_nonneg_of_le`), `ExtensionInterSubspace.lean:80, 92` (`summable_geometric_two` $\to$ `of_nonneg_of_le` $\to$ `Summable.of_norm`), `GrowthOfBasic.lean:664–672`, and `PoissonSummationDecay.lean:48, 112` | Theorem 3(2)–(3), Hand calculation B, and archive majorant consumers |

**Source note.** The reading is local R3 for `Algebra/Order/CauSeq/Basic.lean:49–142, 152–269, 352–696`, `Algebra/Order/CauSeq/Completion.lean:33–72, 141–273, 288–412`, `Data/Real/Basic.lean:36–217, 263–560`, `Algebra/Order/Archimedean/Real/Basic.lean:31–146, 171–192, 324–344, 389–415`, and `Algebra/Order/CompleteField.lean:63–318`; for the metric/filter and completeness files `Topology/MetricSpace/Pseudo/Defs.lean:1125–1148`, `Topology/MetricSpace/Basic.lean:122`, `Topology/MetricSpace/Pseudo/Lemmas.lean:23–25`, `Topology/MetricSpace/Cauchy.lean:49–66, 152–161`, `Topology/EMetricSpace/Basic.lean:36–58, 115–117`, `Topology/UniformSpace/Real.lean:26–46`, `Topology/MetricSpace/CauSeqFilter.lean:27–100`, `Analysis/Normed/Group/Real.lean:49–56`, `Analysis/Normed/Field/Basic.lean:301–304`, `Topology/Instances/Rat.lean:27–44`, `Analysis/Normed/Group/Rat.lean:17–24`, `Analysis/Real/Sqrt.lean:46–47, 112–185`, and `NumberTheory/Real/Irrational.lean:37–76, 141–146`; for the real majorant and series-completeness files `Topology/Order/MonotoneConvergence.lean:68–123`, `Topology/Algebra/InfiniteSum/Order.lean:302–336`, `Topology/Algebra/InfiniteSum/Real.lean:27–101`, `Topology/Algebra/InfiniteSum/ENNReal.lean:362–406, 530–605`, `Topology/Instances/NNReal/Lemmas.lean:132–156`, `Analysis/SpecificLimits/Basic.lean:316–344, 518–547`, and `Analysis/Normed/Group/Completeness.lean:39–90`; and for the local archive A2 call sites `LPartialSum.lean:112–134`, `ThetaSummable.lean:28–52`, `ExtensionInterSubspace.lean:74–94`, and `GrowthOfBasic.lean:662–673`. Inherited without re-proving are the unordered summation filters, finite-tail Cauchy criteria, countable-support theorem, sequential-to-filter metric bridge `UniformSpace.complete_of_cauchySeq_tendsto`, and continuous-linear/closed-embedding `HasSum` transport of [§1.2.2.9](#1229-unordered-summation-finite-tail-cauchy-criteria-and-banach-completeness) (with its post-audit `[T2Space]` separation condition on finite-support limit equality preserved), the Hilbert-basis synthesis and $\ell^2$ framework of [§1.2.2.8](#1228-hilbert-expansion-and-the-norm-behind-poisson-summation), the circle Poisson tiers of [§1.2.2.7](#1227-from-poisson-summation-to-theta-inversion), and the seminormed subsequence bridge of [Chapter 9, §9.4](09-heights-slopes-and-near-orthogonality.md#94-lemmas-and-proofs) (§9.4.10). Inputs retained at `[Lean]` interface level are ordered-field/integer arithmetic on $\mathbb Q$ and $\mathbb Z$ (`IsAbsoluteValue (abs : ℚ → ℚ)`, `Int.exists_greatest_of_bdd`, `Archimedean.floorRing`, `Nat.prime_two`), monotone order-isomorphism inversion for `NNReal.sqrt` (`powOrderIso 2`), and complete-lattice summability on $\mathbb R_{\ge0\infty}$ (`ENNReal.summable`). Primary and classical references (`[Cantor1872]`, `[Dedekind1872]`, `[Mathlib2020]`, `[TaoAnalysisI]`, `[BerghLofstrom1976]`) were verified online. The [proof map](../notes/proof-map.md#p1-chapter-1-real-completeness-and-majorant-supply) lists pinned paths and lines. Hand calculations A and B, the $r\approx g$ equivalence bound, and the $\frac{1}{7b^2}$ rational non-convergence barrier in $\mathbb Q$ are ours; exact rational assertions (`verify_real_completion.py`) check arithmetic and source pins only, do not constitute Lean kernel verification, and do not audit archive A2's transitive dependency cone.

#### 1.2.2.11 Nonnegative extended sums and finite majorants

**Motivation.** A majorant often arrives as an inequality on every finite subtotal. The index set may be a lattice or an arbitrary family of coefficients, with no preferred enumeration. The extended nonnegative line gives every nonnegative family a sum. If a bound keeps that sum finite, we can recover the real limit witness needed for norm comparison. We use the real completion, Dedekind completeness, finite-tail comparison and complex transport from [§1.2.2.9](#1229-unordered-summation-finite-tail-cauchy-criteria-and-banach-completeness) and [§1.2.2.10](#12210-rational-cauchy-completion-dedekind-suprema-and-realinstcompletespace).

**Examples.** [Expository] The following families both have infinitely many nonzero terms.

1. *Two rows with a finite total.* On $I=\mathbb N\times\{0,1\}$ put $w(n,0)=1/(3\cdot 2^n)$ and $w(n,1)=1/(6\cdot 2^n)$. Let $R_N$ consist of both rows for $0\le n<N$. Column $n$ contributes $2^{-n}-2^{-(n+1)}$, so
   $$
   \sum_{i\in R_N}w_i=1-2^{-N}.
   $$
   The first three nonempty rectangles give $1/2,3/4,7/8$. Every finite set lies in some $R_N$, so every subtotal is at most $1$. Since $2^N\ge N+1$ by induction, the rectangles approach $1$ and the supremum is $1$. A finite set disjoint from $R_N$ lies inside $R_M\setminus R_N$ for some $M\ge N$. Its weight is at most $2^{-N}-2^{-M}\le 2^{-N}$.

   Now put $z(n,0)=w(n,0)/2$ and $z(n,1)=\mathrm i\,w(n,1)/2$. The norm weights are $w_i/2$, so their total is $1/2$. The complex subtotal on $R_N$ is $(1-2^{-N})(1/3+\mathrm i/6)$. For $F\supseteq R_N$, the difference from that subtotal has norm at most $2^{-(N+1)}$ by the weight bound just proved. Thus the complex family has sum $1/3+\mathrm i/6$, and its norm satisfies $\sqrt5/6\le 1/2\le 1$. The three numbers are the norm of the complex sum, the sum of the norms and the sum of the majorant.

2. *An infinite total with finite terms tending to zero.* Put $a_n=1/(n+1)$ on $\mathbb N$. The block $B_k$ consists of $2^k-1\le n\le 2^{k+1}-2$. It has $2^k$ indices and each term exceeds $2^{-(k+1)}$, so each block subtotal exceeds $1/2$. The first three block subtotals are $1$, $1/2+1/3=5/6$ and $1/4+1/5+1/6+1/7=(105+84+70+60)/420=319/420$. Their sum is $363/140$ through $n=6$. The union of the first $K$ blocks has subtotal greater than $K/2$. This proves that the extended total is $+\infty$. Converting the terms to real numbers leaves them unchanged, whereas converting the total by `toReal` gives $0$.

**Definitions.** Let $P=\mathbb R_{\ge0}$ (`NNReal`) and $\overline P=[0,+\infty]$ (`ENNReal`). Write $j:P\hookrightarrow\overline P$ and $k:P\hookrightarrow\mathbb R$ for the inclusions. For $a\in\overline P$, set $a^\flat=a.\mathrm{toNNReal}$, so $a.\mathrm{toReal}=k(a^\flat)$. For finite $a$, $j(a^\flat)=a$. For $p\in P$, $(j(p))^\flat=p$. Both projections send $+\infty$ to zero. For any set $I$, let $\mathcal F(I)$ consist of its finite subsets, including the empty set. For $u:I\to\overline P$ define
$$
S_u(F)=\sum_{i\in F}u_i,\qquad
A(u)=\sup_{F\in\mathcal F(I)}S_u(F).
$$
In each scalar space `HasSum` means that every neighborhood of the proposed limit contains all subtotals indexed by supersets of some finite $F_0$. `Summable` asserts existence of such a limit. Any two finite sets have their union as a common upper bound. [Data/ENNReal/Basic.lean:125–153, 223–283](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/ENNReal/Basic.lean#L223-L283)

**Lemma 1 (the extended sum).** [Lean, read] Every $u:I\to\overline P$ has `HasSum` at $A(u)$, and its Mathlib `tsum` equals $A(u)$. For $I=\mathbb N$ it suffices to take the supremum of the initial-segment sums. [InfiniteSum/ENNReal.lean:55–79, 127–136](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L55-L79)

**Proof.** Nonnegativity gives $S_u(F)\le S_u(G)$ for $F\subseteq G$. For every $b<A(u)$ some $F_0$ satisfies $b<S_u(F_0)$ by the least upper bound property. All supersets of $F_0$ then pass that lower neighborhood test. Every subtotal passes each upper test $S_u(F)<d$ with $A(u)<d$. These tests generate the order neighborhoods, including the lower-only tests at $+\infty$ and upper-only tests at zero. For a finite intersection take the union of the witness sets. The production proof uses precisely this monotone convergence, via `Finset.sum_le_sum_of_subset` and `tendsto_atTop_iSup`. `ENNReal.summable` packages the witness, and `HasSum.tsum_eq` identifies the value by Hausdorff uniqueness for the default finite-subset convergence. This includes the empty index set, whose sole subtotal is zero. On $\mathbb N$, every finite set fits in an initial segment, so monotonicity identifies the two suprema. [MonotoneConvergence.lean:68–74, 89–93, 116–122, 141–146](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Order/MonotoneConvergence.lean#L141-L146) · [InfiniteSum/Defs.lean:324–338](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean#L324-L338)

**Lemma 2 (finite values and the coercion interface).** [Lean, read] The total $A(u)$ is finite exactly when one finite number $j(r)$ bounds $S_u(F)$ for every finite $F$. In this case each term is finite, $i\mapsto u_i^\flat$ has `HasSum` in $P$ at $A(u)^\flat$, and $i\mapsto u_i.\mathrm{toReal}$ has `HasSum` in $\mathbb R$ at $A(u).\mathrm{toReal}$. For $v:I\to P$ and $p\in P$ the precise interface is
$$
\mathrm{HasSum}_{P}(v,p)
\quad\Longleftrightarrow\quad A(j\circ v)=j(p)
\quad\Longleftrightarrow\quad
\mathrm{HasSum}_{\mathbb R}(k\circ v,k(p)).
$$
[InfiniteSum/ENNReal.lean:44–72, 211–217, 331–347](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L44-L72) · [NNReal/Lemmas.lean:132–156](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Instances/NNReal/Lemmas.lean#L132-L156)

**Proof.** The supremum property gives $A(u)\le j(r)$ exactly when each subtotal is $\le j(r)$. The finite-bound test `ENNReal.le_coe_iff` says
$$
a\le j(r)\quad\Longleftrightarrow\quad
\exists p\in P,\ a=j(p)\ \text{and}\ p\le r .
$$
The inequality rules out $a=+\infty$, leaving a unique $p$ by the construction as `WithTop NNReal`. Order reflection gives $p\le r$, and applying $j$ proves the reverse. A finite total provides a bound by taking $r=A(u)^\flat$. Each singleton satisfies $u_i\le A(u)$, hence is finite whenever the total is finite. [Data/ENNReal/Basic.lean:550–554](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/ENNReal/Basic.lean#L550-L554) · [Order/WithBot.lean:398–424, dual declaration](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/WithBot.lean#L398-L424)

For the forward limit implication, $j$ preserves finite addition and is continuous, so $S_v(F)\to p$ implies $j(S_v(F))\to j(p)$. Lemma 1 and uniqueness give $A(j\circ v)=j(p)$. For the reverse, the finite ray is an interval with the subspace topology of $\overline P$, so convergence of $j(S_v(F))$ to $j(p)$ gives convergence to $p$ in $P$. These are the directions of `ENNReal.hasSum_coe`. The inclusion $k$ also preserves finite addition and is a topological embedding, giving both directions of `NNReal.hasSum_coe`. Every real limit of nonnegative subtotals is nonnegative by closedness of the ray, so any such existence witness has the form $k(p)$. [ENNReal/BigOperators.lean:30–34](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/ENNReal/BigOperators.lean#L30-L34) · [Order/WithTop.lean:187–206](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Order/WithTop.lean#L187-L206)

For finite $A(u)$ apply the interface to $v_i=u_i^\flat$ and $p=A(u)^\flat$. The singleton test gives $j\circ v=u$, and $j(p)=A(u)$ gives the exact limit equality for reflection. Composing with $k$ proves the real assertion. This identifies the witness of `ENNReal.hasSum_toReal`, whose stated limit is the real `tsum` of the converted terms. Conversely, when all terms of $u$ are finite, any real `HasSum` for their converted family lifts through $k$ and $j$, forcing the extended total to be that finite value.

**Lemma 3 (both directions of finite-subtotal control).** [Expository proof of the cited interfaces] For $g:I\to\mathbb R$ with $g_i\ge0$ and $c\in\mathbb R$, the following are equivalent.

1. $S_g(F)\le c$ for every finite $F\subseteq I$.
2. There exists $q\le c$ with $\mathrm{HasSum}_{\mathbb R}(g,q)$.

The witness $q$ is the real supremum of the subtotals and equals the `toReal` of the extended total of the lifted $g$. If $m$ has a real `HasSum` at $r$ and $0\le g_i\le m_i$ for every $i$, the same $q$ satisfies $q\le r$. [InfiniteSum/Real.lean:84–101](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Real.lean#L84-L101) · [InfiniteSum/ENNReal.lean:362–374, 530–535](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L362-L374)

**Proof.** For $1\Rightarrow2$, the empty sum gives $c\ge0$. Lift $g$ to $v:I\to P$ and $c$ to $C\in P$. The inclusions preserve addition and reflect order, so every extended subtotal is $\le j(C)$. Lemma 2 gives $A(j\circ v)=j(p)$ with $p\le C$ and the real limit $q=k(p)\le c$.

For $2\Rightarrow1$, closedness of the nonnegative ray gives $q=k(p)$ for some $p\in P$. Lemma 2 identifies the extended total with $j(p)$, and each subtotal is at most that value. Reflecting the inequalities yields $S_g(F)\le q\le c$. Every real upper bound $d$ is nonnegative by the empty subtotal. Its lift $D$ satisfies $j(p)\le j(D)$ by the extended supremum property, hence $q\le d$. This identifies $q$ with the exact real supremum produced by the inherited `summable_of_sum_le`. A real limit produced by `Real.instCompleteSpace` and the inherited finite-tail criterion also equals $q$ by Hausdorff uniqueness.

For pointwise comparison, $m_i\ge0$ and its real limit $r$ is nonnegative. Lift both families and the limit to $P$. The pointwise bound compares every finite extended subtotal, hence compares the totals. The upper total is the finite inclusion of $r$, by Lemma 2. Apply the finite-bound test to the lower total and reflect its limit. [Lean, read] In `NNReal.exists_le_hasSum_of_le` the comparison of totals is made by `hasSum_le`, passing termwise and then finite-sum inequalities to the limit in the closed order relation. The proof destructures `ENNReal.le_coe_iff` into a value $p$, the equality identifying the lower total with $j(p)$, and the bound on $p$. Substituting that equality in the extended `HasSum` and applying `ENNReal.hasSum_coe.1` gives the required `HasSum` in $P$. The wrapper `NNReal.summable_of_le` keeps existence, and `Summable.of_nonneg_of_le` lifts both real families before applying it. Both supply routes identify the same real limit whenever used on the same $g$. [InfiniteSum/Order.lean:47–56](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Order.lean#L47-L56)

**Remarks.**

1. *The support boundary.* [Expository] If $A(u)\le j(r)$, each threshold set $E_t=\{i:u_i\ge j(t)\}$ for $t\in P$, $t>0$, has at most $\lfloor k(r)/k(t)\rfloor$ elements. A finite subset of larger size would already exceed the bound. The nonzero support is the union of $E_{1/n}$ for integers $n\ge1$ by the Archimedean property, also covering any infinite term. Thus finite total forces countable support. With uncountable support some $E_{1/n}$ is infinite, and its finite subsets of arbitrarily large size force infinite total. For example, constant weight $1$ on $[0,1]$ gives subtotal $N$ on the distinct points $k/(N+1)$ for $1\le k\le N$. On the same uncountable index set, the weight $2^{-n}$ at $1/n$ for $n\ge1$ and zero elsewhere has total $1$. Every finite subtotal reduces to its intersection with the supported points, where the subtotal of the first $N$ such points is $1-2^{-N}$. Example 2 shows that countable support and finite positive threshold sets still permit infinite total. The exact finiteness test remains the uniform bound of Lemma 2. The production support theorem lifts the terms and invokes the inherited countable-support result. [InfiniteSum/ENNReal.lean:301–318, 377–380, 550–554](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L550-L554)

2. *Deleting hypotheses.* [Expository] Example 2 drops the finite-total hypothesis while keeping every term finite. Its converted family has no real `HasSum` by Lemma 2, even though the totalized real `tsum` and the converted extended total both equal zero. For the converse using converted terms, dropping pointwise finiteness allows a singleton of weight $+\infty$. The converted singleton has `HasSum` at zero and the original total is infinite. Dropping nonnegativity from Lemma 3 allows $g_n=-1$: every finite subtotal is at most zero, and the cofinal initial segments tend to minus infinity. In pointwise comparison, dropping the summability of $m$ allows $g=m=a$ from Example 2. Dropping the domination allows $g=a$ and $m=0$. [InfiniteSum/ENNReal.lean:354–359, 484–491](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L484-L491)

3. *Consumer contract.* The real order-supremum channel needs nonnegativity and one finite bound on all subtotals, or pointwise nonnegative domination by an already summable family. On $\mathbb N$ all initial segments suffice. The uniform channel uses real completeness with the inherited finite-tail criterion. Both deliver the same $q$ when applied to the same majorant. For a complete normed additive group, `Summable.of_norm_bounded` uses real `Summable g` and pointwise $\|x_i\|\le g_i$ to produce target summability. The eventual variant allows finitely many exceptions for existence. `HasSum.norm_le_of_bounded` uses a target `HasSum`, the real `HasSum` at $q$, and the pointwise bound at every index to conclude that the norm of the target limit is at most $q$. Taking $g_i=\|x_i\|$ gives the inherited `Summable.of_norm` route. [Normed/Group/InfiniteSum.lean:46–76, 109–151, 176–195](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Group/InfiniteSum.lean#L109-L151)

   In archive A2, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, the interfaces meet the following calls. The surrounding estimates are inherited.

   | Archive call site | Inputs and output |
   |---|---|
   | `LPartialSum.lean:112–134` | `hf0` supplies nonnegativity and `hpart` bounds all initial segments. `hterm` dominates each norm term by that weight. The proof uses both real summability witnesses for total comparison and retains the bound from `Real.tsum_le_of_sum_range_le`. |
   | `ThetaSummable.lean:28–52` | The two natural-index halves compare nonnegative exponential terms to a summable weight. In the lattice call the product weights are nonnegative, and finite coordinate images give a bound on every finite subtotal by a product of real sums. This bound feeds `summable_of_sum_le`. |
   | `ExtensionInterSubspace.lean:74–94` | Nonnegative weighted norms are bounded by a constant times $2^{-n}$, summable by `summable_geometric_two.mul_left`. A separate fixed-$n$ norm family, `summable_norm_expTerm`, feeds `Summable.of_norm` before continuous-linear evaluation. |
   | `GrowthOfBasic.lean:662–672` | The product of two norm weights is already summable by `Summable.mul_of_nonneg`. It dominates the norm of the real part of the complex inner product. The comparison output feeds `Summable.of_norm`. |
   | `PoissonSummationDecay.lean:45–48, 105–116` | `hb` supplies real summability and `hbd` gives the local pointwise bound. On the Fourier side `hsum` supplies summable norms and the exponential has unit modulus. The intervening integrability call also uses extended termwise comparison and the finite coercion of the real sum of absolute weights (lines 86–91). The two norm bounds furnish the `Summable.of_norm_bounded` calls. |

4. *Sources and reading level.* Tao gives the arbitrary-index supremum definition in the notation of *An Introduction to Measure Theory*, p. xiii, equation (0.1), and distinguishes the extended and absolutely summable totals in the introduction to §1.3, pp. 46–47. The local source reading uses Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The predecessor audit upheld the relevant real supremum and limit supplies and identified a local error in its general geometric-decay argument. Example 1 uses a direct dyadic identity and $2^N\ge N+1$. [Tao, author-hosted preliminary edition](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-126-tao5-measure-book.pdf)

#### 1.2.2.12 Nonnegative product sums and the finite-dimensional theta majorant

A one-dimensional Gaussian controls a lattice sum once we can multiply its weights across the coordinates. The expansion of a squared norm poses the same problem for two copies of an arbitrary index set. A finite set of lattice points can have any shape. Its coordinate images give a finite box, and nonnegative weights allow us to enlarge the sum to that box.

**Example 1 (a Gaussian on the full plane lattice).** On $\mathbb Z^2$, let $w(m,n)=2^{-m^2-2n^2}$. Through radius one in each coordinate the center contributes $1$, the horizontal pair $2(1/2)$, the vertical pair $2(1/4)$, and the corners $4(1/8)$. The total on that square is $3=2(3/2)$. Through radius two the coordinate subtotals are $A_2=1+2(1/2+1/16)=17/8$ and $B_2=1+2(1/4+1/256)=193/128$. The $25$ points contribute $3281/1024$ by finite distributivity.

For $j\ge0$, $(3+j)^2=9+6j+j^2\ge9+7j$ since $j$ is an integer. The two-sided coordinate tails are bounded by $U=2\cdot2^{-9}/(1-2^{-7})=1/254$ and $V=2\cdot2^{-18}/(1-2^{-14})=1/131064$. The product lemma below gives the exact factorization of the full total $W$ into the two one-dimensional sums. It also gives the rational enclosure
$$
\frac{3281}{1024}<W\le(17/8+1/254)(193/128+1/131064)<\frac{3211}{1000}.
$$
The omitted point $(3,0)$ makes the lower inequality strict. The geometric estimates control all omitted points through the two one-dimensional tails.

**Example 2 (one divergent factor, two partners).** Take $I=\mathbb R$, $J=\mathbb N$ and $b_j=1$. The first $N$ columns have $b$-subtotal $N$. With $a_i=0$ at every $i$, every product entry and both iterated totals are zero, even though $b$ has no finite sum. Now take $a'_0=1/2$, $a'_1=1/4$ and zero elsewhere. Each column has sum $3/4$, the rectangle of the two nonzero rows and the first $N$ columns gives $3N/4$, and each of those two rows has infinite total. Thus the real product series diverges despite countable support. With the singleton family $b_0=\infty$ instead, one sees the pointwise rule too. The zero partner gives all zeros, whereas the row $i=0$ for $a'$ contains one infinite entry. These are actual families on nonempty sets.

**Definition.** For any set $I$ and $a:I\to[0,\infty]$, write $T_I(a)=\sup_{F\subseteq I,\,F\text{ finite}}\sum_{i\in F}a_i$. The empty subtotal is zero, and multiplication has $0\cdot\infty=\infty\cdot0=0$. By §1.2.2.11, $T_I$ is the limit of the finite-subset net and equals the extended sum. For nonnegative reals take the total of the included family. The inherited finite-value reflection says that a true real sum exists exactly when the extended total is finite and then equals its real projection. For an extended family with finite total, singleton bounds first ensure that all entries are finite.

**Lemma 1 (fibers and constant factors).** For every pair of sets $I,J$, every $u:I\times J\to[0,\infty]$, every $a:I\to[0,\infty]$ and every $c\in[0,\infty]$,
$$
T_{I\times J}(u)=T_I(i\mapsto T_J(u(i,\cdot)))=T_J(j\mapsto T_I(u(\cdot,j))),\qquad
T_I(i\mapsto a_i c)=T_I(a)c.
$$

**Proof.** A finite subset of the product is contained in the rectangle of its projections, and every finite rectangle is itself admissible. Fix a finite row set $F\subseteq I$ and let $R_i=T_J(u(i,\cdot))$. The rectangle subtotals for $F$ and varying finite column sets are at most $\sum_{i\in F}R_i$. If one $R_i$ is infinite, its subtotals alone exceed every finite threshold. Otherwise for nonempty $F$ select a finite witness in each row within $\varepsilon/|F|$ of $R_i$. The union of all witness column sets keeps each lower bound, so a single rectangle comes within $\varepsilon$ of the desired subtotal. For empty $F$ it is zero. Taking the supremum over $F$ proves the row formula. Swapping the coordinates proves the column formula. For dependent fibers use a finite subset of the disjoint union of the selected rows with their respective witness sets. Each finite subset of the entire disjoint union involves only finitely many rows, giving the other inequality.

Finite distributivity scales each finite subtotal by $c$. For $0<c<\infty$, multiplication by $c$ is an order isomorphism of the extended ray with inverse multiplication by $1/c$, and preserves the supremum. For $c=0$ all scaled subtotals and the scaled total are zero. For $c=\infty$, an all-zero family again gives zero, and otherwise a positive singleton alone gives infinity. A family has total zero exactly when all its singletons vanish. This proves the identity including either placement of the zero and infinite factors. $\square$

[Lean, read] The pinned extended product and order-switch declarations use the always-existing sums of the whole family and the fibers. Their general additive producer, HasSum.sigma, starts with a closed neighborhood of the full limit and a finite witness beyond which all full subtotals belong to it. Take the first-coordinate image of the witness. For a finite row set containing that image, restrict the full net to these rows. Every sufficiently large input finite set still contains the original witness after restriction. Preimages under each fiber injection are cofinal among the finite sets in that fiber, since one can include the image of any finite fiber witness. The restricted subtotal is a finite sum of these fiber subtotals, so it tends to the sum of the selected fiber limits. Closedness keeps that limit in the neighborhood. This proves convergence of the outer net. The product version uses the equivalence with constant fibers. The reversed version also uses the coordinate flip and uniqueness of limits. [Mathlib, extended wrappers](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L81) · [Mathlib, fiberwise producer](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Constructions.lean#L113)

[Lean, read] ENNReal.tsum_mul_right commutes the multiplier to the left. The left proof first handles the identically zero family. In the other case the zero-total criterion yields a nonzero limit, so ENNReal.Tendsto.const_mul allows even an infinite multiplier. That supplier splits off a zero multiplier and otherwise uses multiplication of limits with both exclusions for zero paired with infinity. The constant-multiple net comes from finite distributivity. This explains the case split in the source. Joint continuity at $(0,\infty)$ would fail, as $(1/n,n)$ has product $1$. [Mathlib, constant sums](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L178) · [Mathlib, multiplication of limits](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Instances/ENNReal/Lemmas.lean#L332)

**Lemma 2 (finitely many coordinates).** For every finite coordinate set $D$, arbitrary sets $I_d$ and functions $a_d:I_d\to[0,\infty]$,
$$
T_{\prod_{d\in D} I_d}\left(x\mapsto\prod_{d\in D}a_d(x_d)\right)=\prod_{d\in D} T_{I_d}(a_d).
$$
For nonnegative real entries the product has a real sum exactly when at least one factor total is zero or all factor totals are finite. Its value is zero in the first case and the ordinary product of the sums in the second.

**Proof.** For finite coordinate sets $S_d\subseteq I_d$, the box subtotal is $\prod_d\sum_{i\in S_d}a_d(i)$. Begin with the single empty tuple of weight $1$. On inserting a coordinate, partition the enlarged box by its new coordinate value. Each slice is indexed bijectively by old tuples. Finite distributivity in each slice gives the box identity. Every finite subset lies in the box of its coordinate images, so its subtotal is at most the claimed product. Conversely, if all totals are positive and finite, choose coordinate subtotals approaching the totals and multiply the finitely many approximations. If all are positive and some is infinite, choose one strictly positive subtotal in each other coordinate, bounding each below by a positive finite number. Varying the selected infinite-total coordinate then gives unbounded box subtotals. A zero factor makes all tuples weigh zero, with no tuples at all if some $I_d$ is empty. With $D=\varnothing$ the result is $1$. The real characterization follows from finite-value reflection. $\square$

[Lean, read] Finset.prod_sum proves the finite identity by insertion, using Pi.cons to build the slices. Disjointness between slices and injectivity within a slice justify the sum rewrites. Finset.prod_univ_sum removes the attached membership proofs for a full finite coordinate type. The archive's thetaSummable_pi takes actual projection images, enlarges the finite sum to Fintype.piFinset, rewrites the box subtotal, and compares the coordinate subtotals to their true real sums. The inherited summable_of_sum_le turns that uniform bound into a real sum. This spends the upper-bound half of Lemma 2 with a common coordinate family. [Mathlib, finite distributivity](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/Ring/Finset.lean#L123)

**Corollary (finite real totals and complete-target majorants).** Let $a:I\to\mathbb R$ and $b:J\to\mathbb R$ be nonnegative with real sums $A,B$. Their product on $I\times J$ has real sum $AB$. For every complete normed additive commutative group $E$ and $v:I\times J\to E$ with $\|v(i,j)\|\le a_i b_j$ for every $(i,j)$, the target family has a sum $s$ with $\|s\|\le AB$. The same argument applies to any nonnegative real majorant on any set with finite extended total $M$, using $M$ as the bound.

**Proof.** The real majorant sum is $M=AB$ by Lemma 2 and finite-value reflection. Choose a finite witness whose subtotal exceeds $M-\varepsilon$ for any $\varepsilon>0$. Every finite set disjoint from the witness has majorant subtotal below $\varepsilon$, by bounding their union. The difference of two target subtotals over supersets of the witness has norm bounded by the majorant subtotal on their symmetric difference. This is the finite-subset Cauchy criterion. Completeness gives the limit, and the closed norm ball of radius $M$ contains every subtotal and therefore the limit. $\square$

[Lean, read] Summable.mul_of_nonneg uses the real product-fiber criterion. A finite full total bounds every row. Conversely, once all rows are summable, each extended row total is the inclusion of its true real row sum. Lemma 1 and finite reflection now identify finiteness of the whole total with real summability of the row values. The pinned criterion reindexes through the product-to-sigma equivalence and lifts the terms to nonnegative reals. NNReal.summable_sigma takes factors and then the fiberwise sum in the forward direction. Its reverse uses ENNReal.tsum_sigma', the finite-total test and coercion of the true row sums. For a separable family the product producer supplies each row by hg.mul_left, rewrites its value by hg.tsum_mul_left, then supplies the outer sum by hf.mul_right. The real scaling rules map an existing sum by continuous multiplication by a fixed scalar. [Mathlib, real product criterion](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/InfiniteSum/Real.lean#L70) · [Mathlib, product producer](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Ring/InfiniteSum.lean#L34)

**The archive consumers.**

- **ThetaSummable.** The finite integral basis identifies a lattice element $x$ with a tuple $c\in\mathbb Z^D$. Write $Q(x)=\operatorname{Tr}_{K/\mathbb Q}h(x,x)$ and view these values in $\mathbb R$. The trace matrix and supplied coercive estimate give $Q(x(c))\ge l\sum_d c_d^2$ with $l>0$. The shift bound is $Q(x)\le 2Q(\gamma+x)+2Q(\gamma)$. For $P=\pi\operatorname{Im}\tau>0$, the norm of the actual complex exponential is $\exp(-P Q(\gamma+x))$. The two inequalities therefore bound it by $\exp(P Q(\gamma))\prod_d\exp(-Plc_d^2/2)$. Each coordinate uses $\delta=Pl/2>0$. On each natural-index half of the integers, $\exp(-\delta n^2)\le\exp(-\delta n)$ as $n^2\ge n$. The ratio is strictly between zero and one. Summable.of_nat_of_neg assembles the half families, with one copy of zero in the reindexing. The proof calls thetaSummable_pi, scales by the shift constant, uses Summable.of_norm_bounded in $\mathbb C$, and transports along the basis equivalence. At rank zero the coordinate set has one tuple, corresponding to the lattice origin.
- **GrowthOfBasic.** The actual summable_re input is summability of $t\mapsto\|f(t)\|$ on arbitrary $\tau$. Both nonnegativity witnesses supplied to Summable.mul_of_nonneg are norm nonnegativity. The real array $\operatorname{Re}\langle f(t),f(u)\rangle$ can be signed. Its absolute value is bounded by $|\langle f(t),f(u)\rangle|\le\|f(t)\|\|f(u)\|$. Real comparison yields summability of its absolute values and Summable.of_norm gives the real sum. In norm_sq_tsum the complex inner-product space is separately assumed complete to sum $f$ itself.
- **PoissonSummationDecay.** In loc_integrable, local summability on the closure of the common fundamental cell $D_0$ yields weights $c_l$ with summable absolute values. The extended norm integral on a translated cell, pulled back to $D_0$, is at most $\operatorname{ofReal}|c_l|\,\mathrm{vol}(D_0)$. Extended comparison adds the cell inequalities. ENNReal.tsum_mul_right extracts the common volume. ENNReal.ofReal_tsum_of_nonneg identifies the remaining sum with the finite inclusion of the real absolute sum. The bounded cell has finite volume, so the product is finite.

**Notes on the hypotheses.**

1. Finite extended total implies countable positive support by the inherited threshold argument. The positive support of the product is exactly the product of positive supports. One empty support kills the product, even if another support is uncountable. If all supports are nonempty and one is uncountable, fixing a positive index in every other coordinate gives an injection of that uncountable support into the product support. The extended total must be infinite. Countable support alone leaves open the outcome, as Example 2 shows.
2. Dropping nonnegativity for a general real array can give different iterated sums. On $\mathbb N^2$ put $1$ on $j=i$ and $-1$ on $j=i+1$, with zero elsewhere. Each row sums to zero. Column zero sums to one and every other column sums to zero. The finite-subset net fails the Cauchy criterion: beyond each finite witness one can add a fresh diagonal entry of size one. Two unconditionally summable real factors still have summable absolute values, so this example concerns the general array criterion.
3. At $\delta=0$ the Gaussian subtotal through radius $N$ is $2N+1$, so strict positivity matters. Completeness is also necessary for the general target assertion. In the finitely supported real sequences with the $\ell^1$ norm, let $v(0,n)=2^{-n-1}e_n$ with majorant factors $1$ and $2^{-n-1}$ on $\{0\}\times\mathbb N$. Any limit would have every coordinate $2^{-n-1}$ by continuity of coordinate evaluation, hence infinite support.
4. Tao gives the finite-subset definition in equation (0.1), proves the countable double-series theorem in Theorem 0.0.2 and gives its arbitrary-index form in Exercise 0.0.2. The finite-box and fixed-multiplier arguments here are the book's exposition. [Tao, author-hosted preliminary edition](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-126-tao5-measure-book.pdf)

#### 1.2.2.13 From a rational trace form to Gaussian summability

The preceding section bounds a product of one-dimensional Gaussians. A Hermitian form usually gives cross terms in the integral basis of its lattice. To apply the product bound, we need one positive constant that controls every coordinate tuple at once, in the basis that parametrizes the full lattice. The key step is to pass from strict positivity on rational vectors to strict positivity on real vectors. Density gives nonnegativity. Rationality of the matrix then rules out a real null direction.

**Example 1 (a binary form over the rationals).** Let $K=\mathbb Q$ with the identity involution, $V=\mathbb Q^2$, and $L=\mathbb Z^2$ with basis $e_1=(1,0)$ and $e_2=(0,1)$. Set $h(x,y)=x^{\mathsf T}G y$ with $G=\left(\begin{smallmatrix}3&1\\1&3\end{smallmatrix}\right)$. The field trace is the identity, so $G$ is both the Gram and trace matrix. Writing $Q(x)=\operatorname{Tr}_{K/\mathbb Q}h(x,x)$ gives
$$
Q(m,n)=2(m^2+n^2)+(m+n)^2\ge 2(m^2+n^2).
$$
This verifies positivity on all of $V$ and gives the optimal coordinate constant $\ell=2$, with equality along $(1,-1)$. For $\gamma=(1/2,0)$ and $\tau=4i\log(2)/\pi$, the constants in the tail estimate below are $Q(\gamma)=3/4$, $C=8$ and $r=1/16$. The lattice terms at $(0,0)$ and $(-1,0)$ each equal $1/8$. Outside $|m|,|n|\le N$, the total absolute weight is at most
$$
\frac{8704}{225}\,16^{-(N+1)^2}.
$$
In particular the absolute tail outside the nine-point box at $N=1$ is less than $1/1000$.

**Example 2 (a fractional ideal with a nonorthogonal integral basis).** Let $K=\mathbb Q(i)$ with conjugation, $V=K$, and $h(x,y)=\bar x y$. Here $\mathcal O_K=\mathbb Z[i]$. Indeed, for a nonreal integral $x=a+bi$ with $a,b\in\mathbb Q$, its quadratic minimal polynomial gives $2a,a^2+b^2\in\mathbb Z$. This implies $(2b)^2=4(a^2+b^2)-(2a)^2\in\mathbb Z$, hence $2b\in\mathbb Z$. From $(2a)^2+(2b)^2\equiv0\pmod 4$ both doubled coordinates are even. Rational integers of $K$ are ordinary integers and $i$ is integral, proving the claim. Put $a_0=(1+i)/2$ and $L=a_0\mathcal O_K$. The $\mathcal O_K$-generator is $a_0$ and an integral basis is $b_1=a_0$, $b_2=a_0(1+i)=i$, since $1,1+i$ is an integral basis of $\mathbb Z[i]$. The $K$-basis $(a_0)$ has Gram matrix $(1/2)$. On the integral basis the matrices of $h$ and its trace are
$$
H=\begin{pmatrix}1/2&(1+i)/2\\(1-i)/2&1\end{pmatrix},
\qquad G=\begin{pmatrix}1&1\\1&2\end{pmatrix}.
$$
Multiplication by $A+Bi$ on the $\mathbb Q$-basis $(1,i)$ has trace $2A$. Thus $Q(x)=2|x|^2>0$ for every nonzero $x\in K$. In integral coordinates,
$$
Q(m b_1+n b_2)
=m^2+2mn+2n^2
=\tfrac14(m^2+n^2)+\tfrac34(m+\tfrac43n)^2+\tfrac5{12}n^2.
$$
This gives $\ell=1/4$. Take $\gamma=b_1/2$ and $\tau=8i\log(2)/\pi$. Then $Q(\gamma)=1/4$, $C=4$ and $r=1/2$. The terms at $0$ and $-b_1$ both have weight $1/4$. The absolute tail outside the box $|m|,|n|\le N$ is at most $96\,2^{-(N+1)^2}$. At $N=3$ it is bounded by $3/2048$. The half-shift lies in $V$ and outside $L$. Both examples have ordinary scalar multiplication restricted from $K$, finite lattice generators and full $K$-span. The forms have Hermitian symmetry. In the second example the $K$-rank is one and the integral rank is two.

**Definitions and hypotheses.** Let $K$ be a number field with involution $z\mapsto\bar z$. Let $V$ be a $K$-vector space, with compatible $\mathcal O_K$-action through the inclusion $\mathcal O_K\to K$, and let $L\subset V$ be an $\mathcal O_K$-submodule which is finitely generated over $\mathcal O_K$ and spans $V$ over $K$. These are the two fields of the archive's algebraic lattice predicate, <code>Submodule.IsLattice K L</code>. Take $h:V\times V\to K$ conjugate-linear in its first slot and linear in its second. The Hermitian case has $h(y,x)=\overline{h(x,y)}$. The body <code>thetaSummable_main</code> uses sesquilinearity and the hypothesis
$$
Q(x)=\operatorname{Tr}_{K/\mathbb Q}h(x,x)>0\qquad(x\in V,\ x\ne0).
$$
The separately declared proposition <code>ThetaSummable</code> includes finite dimensionality over $K$ and Hermitian symmetry. Fix any $\gamma\in V$ and any $\tau\in\mathbb C$ with $\operatorname{Im}\tau>0$. Put $P=\pi\operatorname{Im}\tau$ and $f(x)=\exp(\pi i\tau Q(\gamma+x))$ for $x\in L$, using the rational-to-complex inclusion. The question is whether this family has an actual unordered complex sum, as in the definition <code>thetaL</code>. [Source record](../sources/SOURCES.md#chapter-1-12213)

**Lemma 1 (integral coordinates and the trace matrix).** [Lean, read] The lattice admits a finite $\mathbb Z$-basis $b_1,\ldots,b_d$. For every such basis, the map $c\mapsto x(c)=\sum_j c_j b_j$ is a bijection from $\mathbb Z^d$ to $L$. With $G_{jk}=\operatorname{Tr}_{K/\mathbb Q}h(b_j,b_k)\in\mathbb Q$ one has $Q(x(c))=c^{\mathsf T}G c$. In particular this last form is strictly positive for all nonzero integral tuples.

**Proof.** The ring $\mathcal O_K$ is finite over $\mathbb Z$. Multiplying its finite integer generating family by the finite $\mathcal O_K$-generators of $L$ gives a finite integer generating family of $L$. For a nonzero integer $n$, multiplication by $n$ on $V$ is invertible because $K$ has characteristic zero. Consequently $L$ is torsion-free over $\mathbb Z$. The finite torsion-free module theorem over the PID $\mathbb Z$ supplies the basis. In the archive, the proof of the PID supply chooses a maximal independent subfamily of the finite generators. A product of nonzero multipliers sends every generator into its span. Multiplication by this product identifies the input module with a submodule of a finite free module, which has a finite free basis over the PID. The finite basis is then transported back.

Every lattice element has unique integer coordinates in $b$. Since the involution fixes each integer, sesquilinearity expands $h(x(c),x(c))$ to $\sum_{j,k}c_jc_k h(b_j,b_k)$. The $\mathbb Q$-linear trace commutes with this finite sum. This is <code>thetaSummable_expand</code> and the matrix step <code>hQ</code>. If $c\ne0$, the basis equivalence and the inclusion $L\hookrightarrow V$ give $x(c)\ne0$, so the original strict trace hypothesis applies. $\square$ [Pinned PID proof](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/FreeModule/PID.lean#L328)

**Lemma 2 (rational positivity gives a uniform real bound).** [Lean, read] Let $G$ be any rational $d\times d$ matrix with $c^{\mathsf T}G c>0$ at every $c\in\mathbb Z^d\setminus\{0\}$. Then there is one $\ell>0$ with
$$
w^{\mathsf T}G w\ge\ell\sum_j w_j^2\qquad(w\in\mathbb R^d).
$$
The assertion includes $d=0$, where both sides vanish for the unique tuple. The rational restriction is the output of <code>thetaSummable_coercive_rat</code>.

**Proof.** For nonzero $w\in\mathbb Q^d$, set $D=\prod_j\operatorname{den}(w_j)$ with each denominator positive. Then $c=Dw$ is an integral nonzero tuple. Since $c^{\mathsf T}G c=D^2 w^{\mathsf T}G w$, strict positivity descends. This is <code>thetaSummable_ratpos</code>. The witness $D$ can depend on $w$ because we are transporting a sign, and division is by $D^2>0$.

Set $M=G+G^{\mathsf T}$ and use the same notation for its real scalar extension. The quadratic value of $M$ is twice that of $G$, by interchanging the two finite indices in the transpose term. In particular the form of $M$ is nonnegative on rational tuples, including zero, and hence on all real tuples by continuity and density. If a nonzero vector $u\in\mathbb R^d$ had $u^{\mathsf T}Mu=0$, then for every real $v$ the polynomial $2t\,u^{\mathsf T}Mv+t^2v^{\mathsf T}Mv$ would be nonnegative for every real $t$. A nonzero linear coefficient would give a negative value for sufficiently small $t$ of opposite sign. Thus $u^{\mathsf T}Mv=0$ for all $v$, so $Mu=0$. The archive uses the positive-semidefinite zero-form criterion for this implication. Its determinant step is essential: the real determinant vanishes, and it is the image of the rational determinant, so the rational determinant vanishes too. Row reduction over $\mathbb Q$ then gives a nonzero rational $w$ with $Mw=0$, contradicting $w^{\mathsf T}Mw=2w^{\mathsf T}G w>0$. This proves real strict positivity.

For $d>0$, the maximum-norm unit sphere in $\mathbb R^d$ is nonempty and compact. The continuous positive function $u\mapsto u^{\mathsf T}Mu$ attains a positive minimum $\lambda$ there. Scaling any nonzero $w$ by $\|w\|_\infty^{-1}$ gives $w^{\mathsf T}M w\ge\lambda\|w\|_\infty^2$, also valid at zero. Since $\sum_j w_j^2\le(d+1)\|w\|_\infty^2$, take $\ell=\lambda/[2(d+1)]$. This tracks the factors in <code>thetaSummable_coercive</code>, <code>thetaSummable_castform</code> and <code>thetaSummable_sq_le</code>. If the sphere is empty, a nonzero vector would normalize to a point on it. This is exactly the rank-zero branch, where every positive $\ell$ works. $\square$

**Lemma 3 (shift and full-lattice tail).** [Lean, read] Under the original hypotheses, for any basis and $\ell$ supplied above, put $C=e^{P Q(\gamma)}$, $\delta=P\ell/2$ and $r=e^{-\delta}$. Then
$$
|f(x(c))|\le C\prod_{j=1}^d e^{-\delta c_j^2}.
$$
The family $f$ is absolutely summable. With $B_N=\{x(c): |c_j|\le N\text{ for every }j\}$ and $H=(1+r)/(1-r)$, for every integer $N\ge0$ and $d>0$ one has the following explicit bound on the sum over the entire complement:
$$
\sum_{x\in L\setminus B_N}|f(x)|
\le C d H^{d-1}\frac{2r^{(N+1)^2}}{1-r}.
$$
For $d=0$, $L=\{0\}$ and the tail is zero. Full span then implies $V=0$ and $f(0)=1$. The comparison and reindexing follow the archive. The boxed-tail estimate is a quantitative textbook corollary.

**Proof.** Sesquilinearity gives the parallelogram identity $Q(u+v)+Q(u-v)=2Q(u)+2Q(v)$, with $Q(-v)=Q(v)$. The trace form is nonnegative everywhere, including zero. Apply the identity to $u=\gamma+x$ and $v=-\gamma$ and discard $Q(x+2\gamma)\ge0$. Thus $Q(\gamma+x)\ge Q(x)/2-Q(\gamma)$, the inequality used by <code>thetaSummable_shift</code>. In this step only nonnegativity of the discarded value is needed. The strictly positive quadratic bound enters at the next step:
$$
|f(x)|=e^{-P Q(\gamma+x)}
\le C e^{-P Q(x)/2}
\le C e^{-\delta\sum_j c_j^2}.
$$
The real part of $\pi i\tau q$ is $-Pq$ for a rational $q$, which explains the sign. Apply the one-dimensional Gaussian estimate and the finite product and complete-target comparison of §1.2.2.12. The basis bijection identifies this actual sum with summation over $L$.

For the numerical tail, the cited geometric sum and $k^2\ge k$ for integers $k\ge1$ bound the full one-coordinate sum by $1+2r/(1-r)=H$. In the tail one has $|k|=N+1+j$ with $j\ge0$, hence $k^2\ge(N+1)^2+j$. The same geometric formula bounds the two coordinate tails together by $2r^{(N+1)^2}/(1-r)$. Outside $B_N$ at least one of the $d$ coordinates is in this tail. Sum the $d$ nonnegative product bounds, allowing overlaps, and apply the finite product identity to each. This gives the claimed estimate, which also bounds the error in the complex sum when truncated to $B_N$. For Example 1 insert $(C,d,H,r)=(8,2,17/15,1/16)$. For Example 2 insert $(4,2,3,1/2)$. $\square$

**Where the proof is used.** [Lean, read] The direct call to <code>thetaSummable_main</code> is in <code>autFinite_short</code>. It sets $\gamma=0$ and $\tau=i$. For a rational threshold $R$ the summable family tends to zero off finite subsets. Every $x$ with $Q(x)\le R$ has norm at least $e^{-\pi R}>0$, so the trace sublevel set is finite. The consumer <code>autFinite</code> takes a finite $\mathcal O_K$-generating set and uses the sum of its trace values as $R$. Each lattice-preserving isometry maps every generator into that finite sublevel set. Their $K$-span is all of $V$, so the images of the generators determine the map. The result is finiteness of the lattice-preserving isometries.

One actual supplier for this call chain occurs in <code>fibres_of_gluing_facts</code>. It assumes for the given $h$ that $\operatorname{Re}\sigma(h(x,x))>0$ for every complex embedding $\sigma$ and nonzero $x\in V$. The field trace in a number field is the sum over its finite, nonempty set of embeddings, so its real value is a sum of strictly positive real parts. This is <code>trace_inner_self_pos</code>. The call uses that positivity, the ambient Hermitian symmetry and the lattice witness for the particular $M$ in the genus. It returns finiteness of the stabilizer via the injection into the finite isometry set. Another actual supply, <code>trace_pos_of_ortho</code>, starts with $K$, its archive <code>IsCMUnram</code> hypothesis, $h$ Hermitian symmetric and an orthonormal $K$-basis generating a reference lattice $I$ over $\mathcal O_K$. Conjugation compatibility gives a sum of squared complex moduli in each embedding, with at least one positive summand since $x\ne0$. Finiteness of representation sets in a lattice $L$ then uses its separate lattice witness and this same $h$. [Source and call ranges](../sources/SOURCES.md#chapter-1-12213)

The separate use in <code>traceReal_lower</code> calls Lemma 2's producers directly. A nonzero lattice vector has an integer coordinate of absolute value at least one, so $Q(x)\ge\ell$. This supplies a separation radius in the trace realization. The orthogonal rational basis used elsewhere in that realization concerns a $\mathbb Q$-space. The integral basis here reindexes the lattice. [Source and call ranges](../sources/SOURCES.md#chapter-1-12213)

**Notes on the boundaries.**

1. For a full algebraic lattice, its integral basis is also a $\mathbb Q$-basis of $V$. Independence follows by clearing denominators of a rational relation. Spanning follows because $K=\mathbb Q\mathcal O_K$ as a rational span and $L$ is stable under $\mathcal O_K$ and spans $V$ over $K$. For an arbitrary rational basis one must transport the lattice as well. For example $(2b_1,b_2)$ is a rational basis in rank two and integer tuples in it run through a sublattice of index two. The constant $\ell$ is attached to a fixed basis. The shift can be any element of $V$ and enters through $C$, with no integrality requirement.
2. Clearing denominators in Lemma 2 is a test on each rational *vector*. The sum still ranges over all integer tuples of the original lattice. Rationality of the *matrix* is also essential to that lemma's hypothesis. The real form $(s-\sqrt2 t)^2$ is strictly positive at each nonzero rational tuple and vanishes at $(\sqrt2,1)$, so a real uniform bound is impossible.
3. **Deleting strict trace positivity.** Take the same original $K,V,L$ as in Example 1 and the Hermitian form $h_0(x,y)=(x_1+x_2)(y_1+y_2)$. Its trace matrix is $\left(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\right)$ and its radical contains $v=(1,-1)\in L\setminus\{0\}$. For every $\gamma\in V$ the values $Q_0(\gamma+kv)$ all equal $Q_0(\gamma)$. For any $\tau$ in the upper half-plane the infinite sequence of distinct lattice points $kv$ therefore contributes terms of a fixed nonzero modulus. The unordered sum fails the necessary term-to-zero condition. More generally, a singular rational positive-semidefinite trace matrix has a nonzero rational kernel vector, which clears to an integral one and produces the same divergence in a full lattice. If the form instead takes a negative value on the real coordinate space, continuity and density yield a rational negative vector which clears to an integral one. Along its multiples the quadratic term dominates the affine shift and $Q(\gamma+kv)\to-\infty$ as $|k|\to\infty$. Again the terms fail to tend to zero when $P>0$.
4. For $d>0$ and a positive definite trace form, $\operatorname{Im}\tau=0$ gives modulus one on the whole lattice. When $\operatorname{Im}\tau<0$, it gives modulus at least one since $Q\ge0$. Thus the sign of $\operatorname{Im}\tau$ matters for positive rank. At rank zero the singleton sum exists for every $\tau$. The theorem provides pointwise summability of the scalar theta family. The matrix-parameter family <code>thetaN</code>, Fourier transformation and the analytic deductions elsewhere in the book have their own hypotheses.
5. Barvinok's §1.1, formulas (1.1.1)–(1.1.2), exhibits the classical full integer-lattice Gaussian and its translate in a real positive definite matrix model. The present section derives the needed positive definite coordinate form from a number-field trace and follows the particular Lean call chain. [Barvinok, *Computing the Theta Function*, v2](https://arxiv.org/abs/2208.05405v2)

#### 1.2.2.14 From a rational Hermitian trace form to a Euclidean lattice

A trace form measures length on a vector space over a number field. To use Euclidean volume or a theorem about lattice points, we need a real ambient space, an inner-product realization, and a discrete subgroup that spans that space. The trace realization chooses its coordinates once for the form. Each algebraic lattice then supplies its own integer points in those coordinates. The preceding section supplies the uniform separation on each such lattice. [Trace lower bound and Gaussian summability](#12213-from-a-rational-trace-form-to-gaussian-summability)

**Example 1 (a binary form over $\mathbb Q$).** Keep $V=\mathbb Q^2$, $M=\mathbb Z^2$ with integer basis $(e_1,e_2)$, and $h(x,y)=x^{\mathsf T}G y$ with $G=\left(\begin{smallmatrix}3&1\\1&3\end{smallmatrix}\right)$. The involution and trace are the identity. The value at $(s,t)$ is $2(s^2+t^2)+(s+t)^2$, positive away from zero. The two standard generators also span $V$ over $K=\mathbb Q$.

Take $v_1=e_1$, $v_2=e_2-e_1/3$. Their cross pairing is $1-3/3=0$ and their squared lengths are $3$ and $8/3$. The rational coordinates of $(s,t)$ are $(s+t/3,t)$. Thus the embedding matrix in the original basis is
$$
S=\begin{pmatrix}\sqrt3&1/\sqrt3\\0&\sqrt{8/3}\end{pmatrix},
\qquad S^{\mathsf T}S=G.
$$
The columns of $S$ are an integer basis of the image, since the original integer basis maps bijectively to them. In particular $v_2$ has $3v_2\in M$ and $v_2\notin M$. For $a\in\mathbb Q$, multiplication is $aI_2$ both before and after applying $S$. The norm is multiplied by $|a|$. The fundamental parallelogram has base $\sqrt3$ and height $\sqrt{8/3}$, so its Euclidean area is $2\sqrt2=\sqrt{\det G}$.

**Example 2 (a fractional ideal over $\mathbb Q(i)$).** Keep $V=K=\mathbb Q(i)$ with conjugation and $h(x,y)=\bar x y$. Here $\mathcal O_K=\mathbb Z[i]$. For a nonreal integral $a+bi$ its quadratic minimal polynomial gives $2a,a^2+b^2\in\mathbb Z$. Then $(2b)^2$ is an integer, so the rational number $2b$ is an integer. The sum of the two doubled squares is divisible by four, so both doubled coordinates are even. The rational case is the ordinary rational integer criterion, and $i$ is integral. The fractional ideal $M=((1+i)/2)\mathbb Z[i]$ is generated over $\mathcal O_K$ by $b_1=(1+i)/2$. It spans $K$ since $b_1\ne0$, and $2M\subset\mathcal O_K$. An integer basis is $(b_1,b_2)$ with $b_2=i$, since $b_2=b_1(1+i)$ and $(1,1+i)$ is a unimodular change from $(1,i)$.

On $(1,i)$ the multiplication matrix for $u+vi$ is $T_{u+vi}=\left(\begin{smallmatrix}u&-v\\v&u\end{smallmatrix}\right)$, so the field trace is $2u$. Thus the trace pairing is $2$ times the ordinary dot product of the rational coordinate pairs and is positive definite. The basis $(1,i)$ is orthogonal, with both squared lengths $2$, and the embedding matrix on it is $\sqrt2 I_2$. In the integer basis of $M$ the matrix with embedded columns and its Gram matrix are
$$
S_M=\sqrt2\begin{pmatrix}1/2&0\\1/2&1\end{pmatrix},
\qquad S_M^{\mathsf T}S_M=\begin{pmatrix}1&1\\1&2\end{pmatrix}.
$$
The two columns give all the image points by integral combinations. Their parallelogram has area $|\det S_M|=1$. The Euclidean scalar-action matrix is still $T_{u+vi}$, which has $T_{u+vi}^{\mathsf T}T_{u+vi}=(u^2+v^2)I_2$. In the integer basis of $M$ the scalar matrix is $\left(\begin{smallmatrix}u-v&-2v\\ v&u+v\end{smallmatrix}\right)$, by $i b_1=-b_1+b_2$ and $i b_2=-2b_1+b_2$. This matrix is integral for $u,v\in\mathbb Z$. The Euclidean bound $\sqrt{u^2+v^2}$ holds for all rational $u,v$, including scalars that carry points outside $M$. For instance $2\cdot 1=4b_1-2b_2\in M$ also illustrates the existence of a nonzero integer multiple for an arbitrary ambient vector.

**Definitions.** Let $K$ be a number field with an involution and $V$ a finite-dimensional $K$-vector space. Use the $\mathcal O_K$-action on $V$ compatible with the inclusion into $K$, as required by the scalar-tower hypothesis. Fix $h:V\times V\to K$, conjugate-linear in its first argument, linear in its second, and satisfying $h(y,x)=\overline{h(x,y)}$. Write $B(x,y)=\operatorname{Tr}_{K/\mathbb Q}h(x,y)$ and suppose $B(x,x)>0$ for every nonzero $x\in V$. An algebraic lattice $M$ is an $\mathcal O_K$-submodule of $V$ that is finitely generated over $\mathcal O_K$ and has $K$-span $V$. For an additive map $\iota$, <code>zmap ι M</code> is the additive image $\iota(M)$ made into a $\mathbb Z$-submodule. Mathlib's <code>IsZLattice ℝ</code> uses a <code>DiscreteTopology</code> instance on this image and has a field asserting full real span. [Pinned definitions](../sources/SOURCES.md#chapter-1-12214-trace-realization)

**Lemma (nonzero integral multiples).** [Lean, read] If $M$ is an $\mathcal O_K$-submodule with $K$-span $V$, for every $x\in V$ there is an integer $n\ne0$ such that $nx\in M$.

**Proof.** First consider $c\in K$. It is algebraic over $\mathbb Q$, so by clearing coefficients it is a root of a nonzero integer polynomial $p(X)=dX^r+\sum_{j<r}p_j X^j$ with $r\ge1$ and $d\ne0$. The monic polynomial $X^r+\sum_{j<r}p_j d^{r-1-j}X^j$ vanishes at $dc$. Thus $w=dc$ lies in $\mathcal O_K$. This is the injective-base branch of Mathlib's integral-multiple lemma.

Prove the claim by induction on membership in the $K$-span of $M$. A generator and zero both use the integer $1$. Given $ay,bz\in M$ with $a,b\in\mathbb Z\setminus\{0\}$, the product $ab$ works for $y+z$ because $(ab)(y+z)=b(ay)+a(bz)$. If $ay\in M$ and $c\in K$, choose $d,w$ as above. Then $(da)(cy)=w(ay)\in M$ by compatibility of the $\mathcal O_K$-action, and $da\ne0$. Full span puts every $x$ in the induction domain. These are the four branches of <code>Bl.general_b_fact_second'''''.goal1</code>, called by <code>traceReal_mult</code>. [Pinned proof ranges](../sources/SOURCES.md#chapter-1-12214-trace-realization)

**Theorem (trace realization).** [Lean, read] Under the stated hypotheses, let $N=\dim_{\mathbb Q}V=[K:\mathbb Q]\dim_K V$. There is a single injective additive map $\iota:V\to\mathbb R^N$ such that for all $x,y\in V$,
$$
\langle\iota(x),\iota(y)\rangle=B(x,y).
$$
For each $a\in K$ there is a finite real $C_a$ with $\|\iota(ax)\|\le C_a\|\iota(x)\|$ for every $x\in V$. For every algebraic lattice $M$, its image under this same map has discrete topology and spans $\mathbb R^N$ over $\mathbb R$. Hence it supplies both witnesses in the <code>TraceReal</code> conclusion. The construction in <code>traceReal_main</code> gives the displayed value of $N$ and the rational linearity of $\iota$.

**Proof.** Restrict scalars by $qx=(q1_K)x$ for $q\in\mathbb Q$. The scalar tower follows from associativity. A rational basis of $K$ multiplied into a $K$-basis of $V$ is a rational basis of $V$, by expanding coefficients and using independence twice. In the code, <code>Module.compHom</code> and <code>Module.Finite.trans</code> supply the action and finite dimension.

The involution fixes $\mathbb Q$. It conjugates multiplication by $z$ on the rational space $K$ to multiplication by $\bar z$, so their linear traces agree. Trace linearity and the rational fixed scalars make $B$ rational bilinear in both variables. Hermitian symmetry now gives $B(y,x)=\operatorname{Tr}(\overline{h(x,y)})=B(x,y)$.

Mathlib's orthogonal-basis proof works for any symmetric bilinear form over a field in which $2$ is invertible. In dimension zero it takes the empty basis. For the zero form it takes any basis. Otherwise polarization yields a vector $v$ with $B(v,v)\ne0$, since vanishing of all diagonal values would give $2B(x,y)=0$ for all $x,y$. The complement of the line through $v$ is $W=\{x:B(v,x)=0\}$. Indeed
$$
x=\frac{B(v,x)}{B(v,v)}v+\left(x-\frac{B(v,x)}{B(v,v)}v\right)
$$
is a decomposition into the line and $W$, and the intersection is zero. Restrict the symmetric form to $W$, apply induction in dimension $N-1$, and concatenate $v$ with the resulting orthogonal basis of $W$. Over $\mathbb Q$ all these operations stay rational. For our positive form the resulting basis $(v_j)$ has $d_j=B(v_j,v_j)>0$ for each index.

Write $x=\sum_j q_j(x)v_j$ and put $\iota(x)_j=\sqrt{d_j}\,q_j(x)$, viewing rational numbers as real. Each coordinate is additive and respects rational scalar multiplication. Orthogonality kills the off-diagonal terms of $B(x,y)$, giving $\sum_j d_j q_j(x)q_j(y)$. The Euclidean dot product gives the same sum because $(\sqrt{d_j})^2=d_j$. In particular $\|\iota(x)\|^2=B(x,x)$, and if $\iota(x)=\iota(y)$ then positivity applied to $x-y$ gives $x=y$.

For a fixed $a\in K$, commutativity gives $ax=\sum_j q_j(x)(av_j)$. Each coordinate of a vector in an orthonormal basis has absolute value at most the norm. Therefore $|q_j(x)|\le\|\iota(x)\|/\sqrt{d_j}$. Apply the triangle inequality to the image of the expansion for $ax$ to obtain the explicit bound
$$
\|\iota(ax)\|
\le\sum_j |q_j(x)|\,\|\iota(av_j)\|
\le\left(\sum_j\frac{\|\iota(av_j)\|}{\sqrt{d_j}}\right)\|\iota(x)\|.
$$
The constant depends on $a$ and the chosen coordinates. Equivalently, if $A_a$ is the rational matrix of $a$ in $(v_j)$ and $D$ is the diagonal matrix with entries $\sqrt{d_j}$, then $D A_a D^{-1}$ gives the real linear extension in Euclidean coordinates.

Now take any $M$ with its two original lattice witnesses and put $\Lambda=\iota(M)$. The bound <code>traceReal_lower</code> on this $M$ gives an $\ell_M>0$ with $B(m,m)\ge\ell_M$ for $m\in M\setminus\{0\}$. The open ball of radius $\sqrt{\ell_M}$ about zero therefore meets $\Lambda$ just at zero. Translation by each element of this additive subgroup isolates that element as well. This is the discrete-topology witness.

For real span, let $U=\operatorname{span}_{\mathbb R}\Lambda$. Given any $x\in V$, the integral-multiple lemma supplies $nx\in M$ and $n\ne0$. Additivity gives $n\iota(x)=\iota(nx)\in U$, and scaling by $1/n$ puts $\iota(x)$ in $U$. In particular $\sqrt{d_j}e_j=\iota(v_j)$ lies in $U$. Each $\sqrt{d_j}$ is nonzero, so all the standard real basis vectors $e_j$ belong to $U$. Hence $U=\mathbb R^N$, the required <code>span_top</code> field.

In dimension zero the coordinates and sums are empty. The unique map sends zero to zero, the operator bound can use $C_a=0$, and the unique lattice $M=0$ has both witnesses in $\mathbb R^0$. Its fundamental domain is a point of volume one under the usual zero-dimensional normalization. $\square$ [Pinned production and library proofs](../sources/SOURCES.md#chapter-1-12214-trace-realization)

**Covolume and the two lattice hypotheses.** A finite integer basis of $M$ exists by the preceding section. It is rationally independent by clearing denominators in any relation, and the integral-multiple lemma gives rational span of $V$. Its image therefore has an invertible real column matrix $E$ because the rational basis change and the diagonal square-root matrix are invertible. Taking coordinatewise fractional parts gives $E[0,1)^N$ as a fundamental domain. In the standard Euclidean measure its volume is $|\det E|=\sqrt{\det(E^{\mathsf T}E)}$. The Gram matrix on the right is the trace pairing on the original integer basis. This is the ordinary covolume formula in Sutherland's Lecture 14, §14.1, equation (1). The finite integral-basis input is the one used in §1.2.2.13. [Primary source, Lecture 14](https://math.mit.edu/classes/18.785/2021fa/LectureNotes14.pdf)

For $N>0$ the whole rational image is $D\mathbb Q^N$ and is dense by coordinatewise rational approximation. The isolation radius above applies to $\Lambda$, the image of the original integer module.

- **Delete finite generation.** Take $K=\mathbb Q$, $V=\mathbb Q$, $B(x,y)=xy$ and $M=\mathbb Z[1/2]$. This $\mathbb Z$-submodule spans $V$, and any finite generating set would have bounded powers of $2$ in its denominators. Its image contains $2^{-k}\iota(1)$ for every $k\ge0$, nonzero points tending to zero. The real-span witness holds and discreteness fails for any additive realization of this pairing.
- **Delete full span.** In Example 1 take $M_0=\mathbb Z e_1$. It is finitely generated and the image is a discrete infinite cyclic subgroup. Its real span is the line through $\iota(e_1)$, proper since $\iota(e_1),\iota(e_2)$ have invertible Gram matrix. Also, no nonzero integer multiple of $e_2$ belongs to $M_0$.

**Where the witnesses go.** [Lean, read] In <code>classSetFinite_of</code>, the inner-product identity enters <code>GenusCovolBound</code> and <code>classSetFinite_core</code>. The scalar bounds in the core assembly are taken at the elements of an integral basis of $K$, so short vectors give bounds on the trace pairings with their scalar multiples. For each $M$ in the genus, the algebraic lattice witness supplies discreteness and real span on <code>zmap ι M</code>, the input to <code>ShortVectors</code> alongside the separate minimum and covolume bounds. The bounded-dual, bounded-scale and unimodular class-set arguments and the mass-formula finiteness argument use the same interface with their respective lattice families. The genus-wide volume and finiteness inputs have their own proofs.

The integral-multiple lemma also has consumers without a Euclidean embedding. One scales a pre-existing orthogonal $K$-basis into the given lattice. Another takes a product of multipliers over a finite generating set to move an entire source lattice into a target lattice. The local-span consumers use the multiplier as a nonzero element of $K$. The discriminant and bad-prime consumers apply it before their separate Gram and prime-divisor arguments. [Integral-multiple call sites](../sources/SOURCES.md#chapter-1-12214-trace-realization)

In <code>short_vector_every_place</code>, the same map realizes both the reference lattice and the given genus member. Their witnesses permit comparison of the two covolumes and the application of the Minkowski short-vector step to the genus member. The inner-product identity converts the resulting norm estimate back to a trace estimate. The packing argument in <code>encard_shortVectors_le</code> takes just the inner-product identity, and uses its own integrality and archimedean positivity inputs for length and separation estimates. The fixed-shift theta sum and short-vector-set finiteness in §1.2.2.13 are separate inherited applications. The present proof uses the lattice trace lower bound directly. [Consumer ranges and read levels](../sources/SOURCES.md#chapter-1-12214-trace-realization)

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
factor comes from the duplication and reflection formulas and its completed reflection from Poisson summation and the theta-kernel pair, see §§1.2.2.5–1.2.2.7), together
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
Integer shifts of $a$ reindex the first sum and preserve the second. Both kernels change sign under $a\mapsto-a$. We use Jacobi's transformation from Gaussian Poisson summation (§1.2.2.7) and the classical Gamma integral and entire reciprocal Gamma function as inputs.

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
