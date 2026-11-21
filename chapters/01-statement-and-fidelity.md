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
on which the archive builds; the other four are defined in the archive's file `Statements.lean`,
which imports Mathlib and nothing else [Lean, read] (`src/Statements.lean:1`). So the meaning of
the five theorems depends only on Mathlib and on sixteen lines of `Statements.lean`. No other file
of the archive can change it: a Lean environment never contains two declarations with the same
name, so no file can supply a second, different `RiemannHypothesis` or `DirichletLZerosOnLine`,
and a declaration, once added, is immutable [Expository]. (Whether the compiled environment really contains
Mathlib's and `Statements.lean`'s definitions unchanged is what `lake comparator` checks
mechanically, by comparing the statement constants of the proof's export with those of a
separately built "challenge" file that imports only Mathlib; see Section 1.6.)

The proofs are four names defined in `Supplements/Kernels/MainTheorems.lean`, which
`Main.lean` imports through `MainTheoremsAll` and `MainTheoremsCritical` [Lean, read]
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
hypothesis $s\ne1$. In fact the hypothesis is not even needed: the junk value is nonzero, and
Mathlib proves $\zeta(s)\ne0$ on the whole closed half-plane $\Re s\ge1$, including $s=1$
[Lean] (`riemannZeta_ne_zero_of_one_le_re`,
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean:411`).

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
[Lean] (`riemannZeta_one_sub`, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178`), together
with $\zeta\ne0$ on $\Re s\ge1$ — so the two formulations are equivalent [Expository]. The
archive in fact proves the stronger form, and Section 1.4 shows the case analysis it uses.

### 1.2.4 One half

In `s.re = 1 / 2`, the left side `s.re` is a real number (`Complex.re : ℂ → ℝ`), so Lean
elaborates `1 / 2` as a real number, $0.5$. The well-known pitfall that `1 / 2` denotes $0$ in
natural-number arithmetic does not arise. The same holds in every `1 / 2` of `Statements.lean`,
each of which is compared with `s.re` [Lean, read] (`src/Statements.lean:4`, `:8`, `:12`,
`:16`). The same observation appears in the Comparator notes of
`leanprover-community/riemann-hypothesis` [Community].

## 1.3 The Dirichlet statements

### 1.3.1 The four definitions

The archive's `Statements.lean` reads, after `import Mathlib` [Lean, read]
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

### 1.3.2 `DirichletCharacter.LFunction` is the Dirichlet L-function

A Dirichlet character mod $N$ in Mathlib is a multiplicative map
$\mathbb Z/N\mathbb Z\to\mathbb C$ that vanishes on non-units: `DirichletCharacter ℂ N` is
by definition `MulChar (ZMod N) ℂ` [Lean]
(`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:40`). Its L-function is defined through a finite combination of Hurwitz zeta
functions [Lean] (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:61` defines
`LFunction χ s := ZMod.LFunction χ s`, and `Mathlib/NumberTheory/LSeries/ZMod.lean:83` defines
`ZMod.LFunction Φ s := N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s`). As
with $\zeta$, two theorems identify it:

- For $\Re s>1$, `LFunction χ s` equals the Dirichlet series $\sum_{n\ge1}\chi(n)n^{-s}$ [Lean]
  (`LFunction_eq_LSeries`, `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:75`).
- For $\chi\ne1$ it is entire [Lean] (`differentiable_LFunction`,
  `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:98`); for $N=1$ the unique character
  gives $\zeta$ [Lean] (`LFunction_modOne_eq`,
  `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:67`).

By the identity theorem again, `LFunction χ` is the classical $L(s,\chi)$ wherever the latter is
holomorphic, and for the trivial character mod $N$ it is
$\zeta(s)\prod_{p\mid N}(1-p^{-s})$ away from $s=1$ [Expository]; the product formula is the
level-change identity `LFunction_changeLevel` [Lean]
(`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:150`).

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
definitions to unfold to the same proposition. Reading `Main.lean` with this in mind gives four
small facts that the kernel has checked [Lean, read]:

- `src/Main.lean:4` and `src/Main.lean:6` use the same term `rhOfAll`, whose type is Mathlib's
  `RiemannHypothesis` (`src/Supplements/Kernels/MainTheorems.lean:9`). So
  `RiemannZetaZerosOnLine` and `RiemannHypothesis` are definitionally equal. (They differ in
  appearance only: Mathlib writes `-2 * (n + 1)` and lets the coercion $\mathbb N\to\mathbb C$
  be inserted during elaboration; `Statements.lean` writes the coercion explicitly.)
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
definitional identity. `Main.lean` does not use this second derivation for its first theorem; it
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

Sutherland reports that `#print axioms` for the five theorems of `Main.lean` lists only
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
- **`BuildAid`.** The five files `src/BuildAid/D1.lean` … `D5.lean` each add one namespace
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
each of the other eight pins in `lake-manifest.json` is a commit on the main branch of the
corresponding upstream repository [Community]. Sutherland reports that the
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
- **What is still running.** At our last check (2026-11-21 04:42 UTC), Sutherland's page
  still showed its 2026-11-20 22:05 version, and the community Comparator repository had not
  posted a result (its latest commit, at 04:27 UTC, concerns build caching). Any reader of this chapter should check
  both pages for updates [Open].

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
