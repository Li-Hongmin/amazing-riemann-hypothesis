# Chapter 12. Galois representations and partial local Langlands

> **Status tags used in this chapter:** `[Lean, read]` for declarations and `sorry`-free proof
> bodies read line by line in `MainConclusion.lean`, `WeightsConjBis.lean`, `src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean`,
> `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean`, `RowSrc.lean`, `GaloisRepresentationsOfThetaLift.lean`,
> `IntegralStructures/Development.lean`, `WeightOneGeometricRealization.lean`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean`,
> `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean`, and `LocalCentralUnits/RecTExists.lean` (`R3`); `[Lean]` for statement-level
> inspections of imported sub-modules in the 66,167-module and 26,672-module proof cones (`R2`);
> `[Paper]` for citations to Alpöge's `remark.pdf` and Masullo's draft; `[Community]` for public
> module-guide and audit reports; `[Expository]` for classical local/global Langlands background
> and worked examples; `[Open]` for unread Shimura-variety, $p$-adic Hodge, and supercuspidal proof
> cones.

Part II is now complete: Chapters 6–11 reduced both hypotheses of `core_gm` (`CoreAtH` via the
theta-lift chain of Chapters 7–10, and `VWin` via the three-way Tate–Shafarevich squeeze of Chapter 11)
to the foundational automorphic and literature packages assembled in `MainConclusion.lean`.

Open `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7–11` (read in full,
`[Lean, read]`):

```lean
theorem UpperTheory.FinalTheorems.everyCharacter_of_row
    (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
    ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)

theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter_of_row
    UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
```

Pause and admire how small that top-level root is! Once `every_character_of_literature_of_vWin`
(node **P18**, Chapter 13) and `vwin_of_row` (node **P12**, Chapter 11) are in place, **every target
theorem in `src/Main.lean` rests on two foundational existence theorems proved inside the archive**:

1. **Node P14 (`Row0b` / `Row`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`, import cone 66,167 modules):**
   To every regular algebraic polarized (conjugate-self-dual) cuspidal automorphic representation
   $\pi$ of $\mathrm{GL}_a(\mathbb A_E)$ over a CM field $E$, the archive attaches a continuous
   semisimple $a$-dimensional $\ell$-adic Galois representation
   $r : G_E \to \mathrm{GL}_a(\overline{\mathbb Q}_\ell)$ with prescribed Hodge–Tate weights and
   **weak local–global compatibility** (`PropsB`, `AwayB`, `AboveB`) — the formal counterpart of the
   Kottwitz / Clozel / Harris–Taylor / Shin / Caraiani construction `[HarrisTaylor2001]`,
   `[ClozelHarrisTaylor2008]`, `[Shin2011]`, `[Caraiani2012]`, `[Caraiani2014]`.
2. **Node P15 (`RecTExists` / `IsRecT` / `LawsT`, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:55,76,78`, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20`, import cone 26,672 modules):**
   At every finite place $w$ of any number field $E$, there exists a map `rc` from irreducible smooth
   representations of $\mathrm{GL}_n(E_w)$ to $n$-dimensional Weil–Deligne representations obeying a
   restricted 12-clause axiom package `LawsT` — a **deliberately weakened partial local Langlands
   correspondence** (compare Harris–Taylor `[HarrisTaylor2001]`, Henniart `[Henniart2000]`, and
   Bushnell–Kutzko `[BushnellKutzko1993]`).

Part III (Chapters 12–13) opens the foundations built inside the archive to inhabit `MainConclusion.lean`.
This chapter examines `Row0b` and `RecTExists`: why weak compatibility and partial local Langlands
suffice for Part II, why universal quantification over `IsRecT h rc` inside `Row0b` keeps their
interaction logically airtight, what `WeightsConjBis.lean` and `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean` state clause by
clause, how `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean` and `IntegralStructures/Development.lean` assemble them at the top
level, and how the 66,167-module Shimura-variety / congruence / even-rank theta-lift proof cone is
organized.

---

## 12.1 Motivation

### 12.1.1 Where Part II actually used Galois representations and local Langlands

Why did an analytic prime-sum bound ever need $a$-dimensional $\ell$-adic Galois representations of
$\mathrm{GL}_a(\mathbb A_E)$ over CM fields [Expository]? Look back at the exact places in Chapters 7,
10, and 11 where `Row0b` and `RecTExists` were consumed:

1. **Along the $m$-step theta-lift chain (Chapters 7 and 10):**
   - In Chapter 7 (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/PairLiftOfHoweDualityBernstein.lean:17`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44`),
     lifting an automorphic representation along $U(X_0) \to U(X_1) \to \dots \to U(X_m)$ splices its
     local split-place parameters by $\sigma \mapsto \sigma \boxplus \mu_j[t]$, and `RecTExists`
     translates local parabolic induction of characters and depth-zero types into direct sums of
     Weil–Deligne parameters (`LawsT.langlands`, `LawsT.one`, `LawsT.type`).
   - In Chapter 10 (`CutDetOrd.main`, `CutCoreUnit.main`), bounding the $\ell$-adic Hecke congruence
     denominators of each lift required attaching a Galois representation (and residually reducible
     generalized matrix algebra representation) whose Frobenius traces match the Hecke eigenvalues at
     unramified split places — turning automorphic congruences into Galois $1$-cocycles in
     $Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)$!
2. **Inside the `VWin` modularity and Euler-system engine (Chapter 11):**
   In `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4` and `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TopMainZj.lean:47,71` [Lean, read], `Row0b` enters as
   `OpenImageCondition.mk h` and `gal : RowT`, supplying:
   - the $2$-dimensional $\mathrm{GL}_2$ Galois representations and local–global compatibility needed
     by Kato's Euler system (`KatoUse`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:15`);
   - the $3$-dimensional (and $\mathrm{GSp}_4$-transferred) Galois representations $\rho : G_K \to \mathrm{GL}_3(\overline{\mathbb Q}_\ell)$
     attached to cohomological forms on $U(3)$ whose Frobenius trace differences build the nonzero
     annihilator integer `NN` in `PropGK` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:36,60`); and
   - the crystalline / Hodge–Tate jump control above $\ell$ (`AboveB.crys`, `AboveB.nice`) needed for
     ordinary Hida theory and Taylor–Wiles patching (`PfromAut`).

### 12.1.2 Why weak local–global compatibility and partial local Langlands are logically sound together

In the published literature, proving the **full** local Langlands correspondence for $\mathrm{GL}_n(E_w)$
`[HarrisTaylor2001]`, `[Henniart2000]` — pinning down wild positive-depth supercuspidal representations
uniquely via local Rankin–Selberg $\gamma$- and $\varepsilon$-factors of pairs — and proving **full**
local–global compatibility $(r_{\pi, \iota})|_{W_{E_w}}^{\mathrm{WD}} \cong \mathrm{rec}_{E_w}(\pi_w \otimes \lvert\det\rvert^{(1-a)/2})$
at every ramified place $w \nmid \ell$ (including monodromy $N \neq 0$ on nearby cycles of Shimura
varieties with bad reduction `[HarrisTaylor2001]`, `[Shin2011]`, `[Caraiani2012]`) requires hundreds of
pages of vanishing-cycle geometry and local harmonic analysis.

Notice the crucial observation embodied in nodes **P14** and **P15** [Expository]:

- **Downstream consumers never use wild supercuspidals or ramified monodromy $N \neq 0$!** Along the
  theta-lift chain and in `PropGK` / `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean`, local–global compatibility is needed at
  **spherical (unramified) places** and **abelian/toral Iwahori-level places** (`Tor` with monodromy
  `mono0`, i.e. $N = 0$), plus **depth-zero cuspidal types** inflated from $\mathrm{GL}_n(\mathbb F_g)$
  over $\mathbb Q_g$ (`TypeLaw`, using Green's characters from Chapter 13!).
- **Why weakening `IsRecT` does NOT create a loophole in `Row0b`:** A skeptical reader might worry:
  *"If `IsRecT` leaves `rc` unconstrained on wild supercuspidals, could `recTExists` define `rc` to
  be some trivial dummy map and make `Row0b` vacuously easy to prove?"* Look at the quantifier order
  in `PropsB.away` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:58–59`) [Lean, read]:
  ```lean
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h),
    Rc h rc → ∀ σ, π.IsLocComp w σ → AwayB (wdOf h hl ι r) (rc (algNorm σ))
  ```
  `PropsB` quantifies **universally** over *every* map `rc` satisfying `IsRecT h rc`! Making the
  predicate `IsRecT h rc` weaker enlarges the class of admissible maps `rc`, which makes the
  universal obligation `∀ rc, IsRecT h rc → ...` **harder (or equally hard) to prove, never easier**!
  And on the toral/spherical representations where `AwayB.tor` asserts `wdOf r = rc (algNorm σ)`,
  `LawsT.one` and `LawsT.langlands` **uniquely determine `rc`** via local Artin reciprocity and
  parabolic induction anyway! Thus weakening both `IsRecT` and `AwayB` to the exact fragment used by
  Part II is 100% logically sound: less is proved in P14–P15, and only that smaller proved contract
  is consumed in P12 and P17!

---

## 12.2 Worked examples

Let us make both `PropsB` / `LawsT` and the even-rank theta-lift subtraction device completely
concrete on small ranks $a = 1$ and $a = 2$ [Expository].

### 12.2.1 Rank $a = 1$ and $a = 2$: Hodge–Tate weights, `Tor` vs. Steinberg, and depth-zero `TypeLaw`

1. **Rank $a = 1$ over $E = \mathbb Q(i)$ (algebraic Hecke characters and `PropsB.weights`):**
   Let $E = \mathbb Q(i)$ ($E^+ = \mathbb Q$, complex conjugation $c(z) = \bar z$), fix its two complex
   embeddings $\tau_0(z) = z$ and $\tau_0 \circ c(z) = \bar z$, and consider the conjugate-self-dual
   unitary Hecke character $\pi = \chi_k$ ($k \in \mathbb Z$) whose infinity type on $E_\infty^\times = \mathbb C^\times$
   is
   $$\chi_{k, \infty}(z) = (z / \bar z)^k = z^k \bar z^{-k}, \qquad\text{infinitesimal character } z(\tau_0) = k,\ z(\tau_0 \circ c) = -k.$$
   Check the archive's Hodge–Tate weight formulas `PropsB.weights` and `PropsB.weights_conj`
   (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:60–63`) at $a = 1$:
   $$\mathrm{HT}(\tau_0) = \frac{1 - 1}{2} - k = \{-k\}, \qquad
   \mathrm{HT}(\tau_0 \circ c) = \frac{1 - 1}{2} - (-k) = \{+k\} = \{0 - (-k)\},$$
   satisfying `weights_conj` with purity weight $\mathrm{wt} = 0$! Under Weil's $\ell$-adic
   construction (`HeckeLAdicCharacter` via global Artin reciprocity `[Tate1967]`; see **Chapter 18**, Section 18.2), at every odd split
   prime $p = \varpi \bar\varpi \equiv 1 \pmod 4$ in $\mathbb Z[i]$ — say $p = 5 = (-1 + 2i)(-1 - 2i)$ —
   with $p \neq \ell$, the prime ideal $\mathfrak p = (-1 + 2i) = (2 + i)$ has the **unique** ray-one
   generator $\varpi = -1 + 2i = i(2 + i) \equiv 1 \pmod{2+2i}$ (since $(-1 + 2i) - 1 = -2 + 2i = i(2 + 2i)$,
   whereas $2 + i \equiv -i \not\equiv 1 \pmod{2+2i}$!), and the attached $1$-dimensional Galois character
   $r : G_{\mathbb Q(i)} \to \overline{\mathbb Q}_\ell^\times$ sends geometric Frobenius at $\mathfrak p$
   to $\varpi^{-k}\bar\varpi^k = (-1 + 2i)^{-k}(-1 - 2i)^k = (-1)^k (2 + i)^{-k}(2 - i)^k \in \overline{\mathbb Q}(i)^\times \hookrightarrow \overline{\mathbb Q}_\ell^\times$,
   matching `LawsT.one` (`rc (.ofChar χ) = lpOfChar (χ ∘ a)`) via `AwayB.tor`!

2. **Rank $a = 2$: testing the three regimes of `AwayB` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:26–31`):**
   Suppose $\pi$ is a regular algebraic polarized cuspidal representation of $\mathrm{GL}_2(\mathbb A_E)$
   (for instance, the base change to $E = \mathbb Q(i)$ of a classical weight-$2$ holomorphic newform
   $f \in S_2(\Gamma_0(N))$ corresponding to an elliptic curve $A / \mathbb Q$, where
   $\frac{a - 1}{2} = \frac{1}{2}$ shifts unitary normalization to arithmetic Hodge–Tate weights
   $\{0, 1\}$ with $\mathrm{wt} = 1$). Look at a prime $w \nmid \ell$ of $E$ and compare what
   `AwayB (wdOf r) (rc (algNorm σ))` asserts in three classical local cases:
   - **Case A — Principal series $\sigma_w = \operatorname{Ind}_B^{\mathrm{GL}_2(E_w)}(\chi_1 \otimes \chi_2)$ (`Toral` on `IrrGL` $\implies$ `Tor` on `WD` and `mono0`):**
     Here the cuspidal support consists of two $1$-dimensional characters $\chi_1, \chi_2$ (`y.1 = 1` in
     `Toral`, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:26`).
     By `LawsT.langlands` and `LawsT.one`, `rc (algNorm σ)` is built from $1$-dimensional `lpOfChar`
     summands, so its Weil-group image is abelian (commutator-trivial `Tor` on `WD h`,
     `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjAlt.lean:27`),
     and for generic unlinked $\chi_1, \chi_2$ the Weil–Deligne monodromy operator vanishes ($N = 0$,
     i.e. `y.mono0`). Then `AwayB.tor` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:29`) fires and gives **full isomorphism of
     Weil–Deligne representations** `x = y`! In particular, at every unramified prime $w$ of norm $q_w$,
     $r(\mathrm{Frob}_w)$ has exact characteristic polynomial $X^2 - a_w(f) X + q_w$!
   - **Case B — Special / Steinberg twist $\sigma_w = \mathrm{St}_2 \otimes \chi$ (`Tor` true, `mono0` false):**
     Classically (Caraiani `[Caraiani2012]`), the Weil–Deligne parameter has $N = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix} \neq 0$,
     corresponding to multiplicative (Tate-curve) bad reduction of $A$ at $w$. Because `y.mono0` is
     **false**, neither `AwayB.tor` nor `AwayB.tame0` fires: `AwayB` asserts **only `x.lpDim = y.lpDim`**
     ($2 = 2$)! The archive deliberately avoids formalizing weight-monodromy on nearby cycles because
     Part II never needs local–global compatibility at Steinberg places!
   - **Case C — Depth-zero supercuspidal at a split rational prime $E_w \cong \mathbb Q_g$ (`g > 16 a^2 = 64`):**
     Suppose $E_w \cong \mathbb Q_g$ ($g > 64$ prime) and $\sigma_w$ is compactly induced from a
     cuspidal Green character $\tau_\theta$ of $\mathrm{GL}_2(\mathbb F_g)$ (`Inflates σ τ` in `TypeLaw`,
     `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:35–53`, attached to a regular character $\theta : \mathbb F_{g^2}^\times \to \mathbb C^\times$
     with $\theta^g \neq \theta$). Then `TypeLaw` forces `y.mono0` ($N = 0$) and pins down the inertia
     characteristic polynomial on $I_{\mathbb Q_{g^2}}$ as $(X - \theta(z))(X - \theta(z^g))$
     (squarefree since $\theta(z) \neq \theta(z^g)$!), so `AwayB.tame0` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:31`)
     forces `x.mono0` and equates the degree-$0$ (inertia) characteristic polynomials `x.charPol g = y.charPol g`!

### 12.2.2 The even-rank theta-lift subtraction trick (`TwoUp` and `PeelAll`) in miniature

When we open the proof cone of `Row0b` below (Section 12.4.4), we encounter a classic parity obstacle
in the cohomology of unitary Shimura varieties `[Shin2011]`: passing from a quasi-split or signature-$(1, n-1)$
unitary group over $E/E^+$ to a **totally definite** unitary inner form $U(n)$ at all infinite places
requires changing the local Hermitian invariant at $n - 1$ real places of $E^+$ ($[E^+ : \mathbb Q]$
even) without introducing finite ramification. By Hilbert's product law for local norm-residue symbols,
that sign change is unobstructed **when $n$ is odd** (for instance when $[E^+ : \mathbb Q]$ is a
multiple of $2$, $(n - 1)[E^+ : \mathbb Q]$ is even; in the archive's setup `Odd n` makes the total
sign-change count a multiple of $4$), whereas **even rank $a$** encounters a Brauer/sign obstruction!

How does the archive attach an $a$-dimensional Galois representation when **$a$ is even** (say $a = 2$)
using *only* its odd-rank theorem plus a stable-range theta lift (`TLiftK`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean:4`)? Check
the polynomial algebra in five lines [Expository]:

1. Take our even-rank representation $\Pi$ on $U(2)$ (rank $a = 2$), choose an odd increment $t = 3$ so
   that $a + t = 5$ is **odd** and lies in the stable theta-lift range, and choose **two** tuples of
   auxiliary algebraic Hecke characters $(\psi_{1,1}, \psi_{1,2}, \psi_{1,3})$ and
   $(\psi_{2,1}, \psi_{2,2}, \psi_{2,3})$ whose specializations at a dense set of Frobenius elements are
   **pairwise disjoint**:
   $$\{\psi_{1,1}(\mathrm{Frob}_w), \psi_{1,2}(\mathrm{Frob}_w), \psi_{1,3}(\mathrm{Frob}_w)\}
   \cap \{\psi_{2,1}(\mathrm{Frob}_w), \psi_{2,2}(\mathrm{Frob}_w), \psi_{2,3}(\mathrm{Frob}_w)\} = \emptyset.$$
2. Apply the global theta lift (`TLiftK`) twice to obtain **two** odd-rank automorphic representations
   $\Pi^{(1)}$ and $\Pi^{(2)}$ on $U(5)$ with split-place parameters
   $$\Pi^{(1)} \boxplus \equiv \Pi \boxplus \psi_{1,1} \boxplus \psi_{1,2} \boxplus \psi_{1,3},
   \qquad
   \Pi^{(2)} \boxplus \equiv \Pi \boxplus \psi_{2,1} \boxplus \psi_{2,2} \boxplus \psi_{2,3}.$$
3. Apply the **odd-rank** Shimura-variety theorem ($a + t = 5$) to $\Pi^{(1)}$ and $\Pi^{(2)}$, obtaining
   two semisimple $5$-dimensional Galois representations $R_1, R_2 : G_E \to \mathrm{GL}_5(\overline{\mathbb Q}_\ell)$
   whose Frobenius characteristic polynomials at unramified split places $w$ satisfy
   $$P_{R_1, w}(X) = P_{\Pi, w}(X) \prod_{j = 1}^{3} \bigl(X - \psi_{1,j}(\mathrm{Frob}_w)\bigr),
   \qquad
   P_{R_2, w}(X) = P_{\Pi, w}(X) \prod_{j = 1}^{3} \bigl(X - \psi_{2,j}(\mathrm{Frob}_w)\bigr).$$
4. Because each $R_i$ is semisimple in characteristic zero and contains the known $1$-dimensional
   Galois characters $r(\psi_{i,j})$ (verified by comparing common eigenvalues of $R_1$ and $R_2$ when
   the two auxiliary triples have zero overlap!), peeling off the three linear factors $\bigoplus_{j=1}^3 r(\psi_{1,j})$
   from the representation space of $R_1$ (`PeelAll` / `SubtractQ` in the archive!) leaves a genuine
   semisimple **$2$-dimensional** Galois representation $r_\Pi : G_E \to \mathrm{GL}_2(\overline{\mathbb Q}_\ell)$
   whose Frobenius characteristic polynomial at every unramified split place is $P_{\Pi, w}(X)$!

---

## 12.3 Definitions

We now give the exact Lean signatures of nodes **P15** (`LawsT`, `IsRecT`, `RecTExists`) and **P14**
(`AwayB`, `AboveB`, `PropsB`, `Row0b`, `Row`).

### 12.3.1 Partial local Langlands (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean`)

**Definition 12.1 (`GoodCusp`, `Good`, `Toral`, `TypeLaw`, `LawsT`, `IsRecT`, and `RecTExists`, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:20,24,26,35,55,76,78`).** [Lean, read]

Let $E$ be a number field with algebraic closure $\Omega$, $w$ a finite place of $\mathcal O_E$ with
completion $k := E_w$, and $h : \mathrm{IsPlaceOver}\,A\,w$ ($A \subset \Omega$ a valuation subring above $w$).

1. **The `Good` and `Toral` representation classes (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:20–26`):** For an irreducible
   smooth representation $x \in \mathrm{IrrGL}(k)$ of $\mathrm{GL}_{x.1}(k)$:
   - `GoodCusp y` (`:20`): either $\dim(y) = y.1 = 1$ (a smooth character of $k^\times$), **or**
     $k \simeq_{\mathrm{top}} \mathbb Q_g$ ($g$ prime) and $y = y_0 \otimes (\chi \circ \det)$ is a
     character twist of a **depth-zero** supercuspidal $y_0$ (having nonzero invariants under the
     principal congruence subgroup $K_1 = 1 + g M_n(\mathbb Z_g)$: `fixed y₀.rep (KOne k (Fin y₀.1)) ≠ ⊥`);
   - `Good x` (`:24`): $x$ has Bernstein–Zelevinsky cuspidal support $s$ consisting entirely of
     `GoodCusp` representations (`∀ y ∈ s, GoodCusp y`);
   - `Toral x` (`:26`): $x$ has cuspidal support consisting entirely of $1$-dimensional characters
     (`∀ y ∈ s, y.1 = 1`, i.e. subquotients of principal series).
2. **Depth-zero Green-type inertia law (`TypeLaw h rc`, `:35–53`):** Whenever $k \simeq \mathbb Q_g$
   (so $g \nmid 2 D_0$ is unramified and split of degree $1$ in $E$!), $E'/E$ is **strictly unramified**
   at $w' \mid g$ (`g ∉ (w')^2`, i.e., absolute ramification index $e(w'/g) = 1$) with residue field $K \cong \mathbb F_{g^n}$,
   $\theta : K^\times \to \mathbb C^\times$ is a regular character (`IsRegularChar g n θ`), $\tau$ is a
   cuspidal representation of $\mathrm{GL}_n(\mathbb F_g)$ with Green character trace
   $(-1)^{n-1}\sum_{j=0}^{n-1} \theta(z^{g^j})$ on irreducible characteristic polynomials, and
   $\sigma \in \mathrm{IrrRep}(\mathrm{GL}_n(\mathbb Q_g))$ inflates $\tau$, the Weil–Deligne parameter
   `rc (cls σ)` has **zero monodromy** (`mono0`) and inertia characteristic polynomial
   $$\bigl(\mathrm{rc}(\mathrm{cls}\,\sigma)\bigr).\mathrm{inePol}(t)
   = \prod_{j = 0}^{n - 1} \bigl(X - \theta(z^{g^j})\bigr)$$
   for inertia elements $t \in I_{E'_{w'}}$ mapping under local Artin reciprocity $a'$ to units congruent
   to $z \in K^\times$!
3. **The 12-clause axiom package `LawsT` (`:55–73`), `IsRecT` (`:76`), and `RecTExists` (`:78`):**
   Given a local Artin reciprocity map `a : Weil h →* kˣ` (`ha : IsLocalArtin h a`), a map
   `rc : IrrGL k → WD h` satisfies `LawsT a ha rc` iff:
   - *(Unconditional on all $x \in \mathrm{IrrGL}(k)$ — 6 clauses)*:
     1. `dim`: `(rc x).lpDim = x.1` (exact dimension $n$);
     2. `one`: `rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) ...` ($\mathrm{GL}_1$ is local class field theory);
     3. `langlands`: `IsL l x.rep → rc x = segSum rc l` (Langlands quotient of segments maps to direct sum of segment parameters);
     4. `cusp`: `x.IsCusp → IsIrrWD (rc x)` (supercuspidals map to irreducible Weil representations with $N = 0$);
     5. `nu`: `rc (x.nu s) = (rc x).lpTw s` (unramified norm-twist compatibility $\lvert\det\rvert_w^s$);
     6. `absCentral`: `HasCentralChar x.rep ω → ‖((rc x).eig σ).prod‖ = ‖ω (a σ)‖` (absolute value of determinant matches central character);
   - *(Guarded by `Good x` / `Good y` — 5 clauses)*:
     7. `twist`: `Good x → rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))`;
     8. `central`: `Good x → HasCentralChar x.rep ω → ((rc x).eig σ).prod = ω (a σ)` (exact determinant = central character);
     9. `dual`: `Good (cls π) → π' ≃ contra π → rc (cls π') = (rc (cls π)).lpDual` (contragredient duality);
     10. `inj`: `Good y → rc x = rc y → x = y` (injectivity onto `Good` targets);
     11. `depth`: `Good x → fixed x.rep KOne ≠ ⊥ → IsTameWD (rc x)` (depth zero $\implies$ tame Weil–Deligne parameter);
   - *(Depth-zero supercuspidal explicit inertia — 1 clause)*:
     12. `type`: `TypeLaw h rc`.

   Finally, `IsRecT h rc := ∃ a ha, LawsT a ha rc` (`:76`), and `RecTExists` (`:78–80`) asserts
   `∀ E Ω A w h, ∃ rc, IsRecT h rc`.

### 12.3.2 Galois representations with weak local–global compatibility (`WeightsConjBis.lean`)

**Definition 12.2 (`IsQpBig`, `AwayB`, `AboveB`, `PropsB`, `Row0b`, and `Row` / `RowT`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:15,26,39,54,69`, `src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean:6`, and `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean:47`).** [Lean, read]

Fix a local-reciprocity predicate `Rc : RecNotion` (instantiated as `recT := fun h rc => IsRecT h rc`,
`src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean:4`), a CM number field $E$ with maximal real subfield $E^+$, a prime $\ell$, an isomorphism
$\iota : \overline{\mathbb Q}_\ell \simeq \mathbb C$, and a rank $a \ge 1$.

1. **Local compatibility away from $\ell$ (`IsQpBig`, `AwayB`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:15, 26–31`):**
   Write `IsQpBig w n` (`:15`) if $E_w \simeq_{\mathrm{top}} \mathbb Q_g$ for a rational prime $g$ with
   $n = 1$ or $16 n^2 < g$. For two Weil–Deligne representations $x, y \in \mathrm{WD}(h)$ at $w \nmid \ell$,
   `AwayB x y : Prop` asserts:
   - `dim`: `x.lpDim = y.lpDim`;
   - `tor`: `Tor y → y.mono0 → x = y` (if $y$ is abelian/toral with zero monodromy, $x$ equals $y$ on the nose!);
   - `tame0`: `IsQpBig w y.lpDim → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g, deg g = 0 → x.charPol g = y.charPol g`
     (if $E_w \cong \mathbb Q_g$ with $g > 16 n^2$ and $y$ is tame, squarefree on inertia, and $N = 0$,
     then $x$ also has $N = 0$ and the same characteristic polynomial on inertia `deg g = 0`).
2. **$p$-adic Hodge compatibility above $\ell$ (`AboveB`, `:39–52`):** Given a period-ring package
   `P : LocPrime l` and local bridge `Bw` at $w \mid \ell$ (`hj : Pst.Induces Bw`), `AboveB` asserts:
   - `crys` (`:43–46`): whenever the local component $\sigma$ of $\pi$ at $w \mid \ell$ is **spherical**
     (`IsSpherical σ.ρ`), $r|_{D_w}$ is **crystalline** and **de Rham** (`IsCrysAt`, `IsdRAt`) with
     labeled Hodge–Tate jump multiset `HT τ` at every embedding $\tau : E \to \overline{\mathbb Q}_\ell$;
   - `nice` (`:48–52`): whenever `rc (algNorm σ)` (for any `Rc h rc`) is either `(IsQpBig w a ∧ TmW ∧ Sqf)`
     or `Tor`, and has `mono0`, $r|_{D_w}$ is **de Rham** and **potentially semistable** (`IsPstAt`) with
     Hodge–Tate jumps `HT τ`, and its Fontaine–Weil–Deligne parameter `wdAt ...` satisfies `AwayB` against `rc (algNorm σ)`.
3. **Global bundle `PropsB` (`:54–67`) and `Row0b` (`:69–73`):** For a regular algebraic (`IsRegAlg`)
   cuspidal subspace $\pi \in \mathrm{CuspSub}(E, a)$ polarized by $\chi : \mathrm{HChar}(E^+)$
   (`PolarizedPair π χ`, meaning $\pi^\vee \cong \pi^c \otimes (\chi \circ \mathrm{Nm}_{E/E^+} \circ \det)$),
   `PropsB Rc π ι r wt HT` asserts that $r : G_E \to \mathrm{GL}_a(\overline{\mathbb Q}_\ell)$ is:
   - `cont` and `ss`: continuous and semisimple (`IsSSRep r`);
   - `away`: satisfies `AwayB (wdOf h hl ι r) (rc (algNorm σ))` at every $w \nmid \ell$ and for **every**
     `rc` satisfying `Rc h rc`;
   - `weights` and `weights_conj`: for every $\tau : E \to \overline{\mathbb Q}_\ell$, casting `HT τ : Multiset ℤ`
     to $\mathbb C$ equals `((CG.mk π).infChar (ι ∘ τ)).map (fun z => (a - 1)/2 - z)`, and
     `HT (τ ∘ c) = (HT τ).map (wt - ·)`;
   - `above`: satisfies `AboveB` at every $w \mid \ell$ for every tied Fontaine package `LocTied l P AI`.
   `Row0b Rc : Prop` (`:69`) asserts that for every such $(E, \ell, \iota, a \ge 1, \pi, \chi)$, there
   exist `(r, wt, HT)` satisfying `PropsB Rc π ι r wt HT`. Specializing `Rc` to `IsRecT` defines
   **`UpperTheory.One.M.Row`** (`src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean:6`) and **`UpperTheory.V.Z.Win.RowT`** (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean:47`) —
   two identical aliases for `Row0b (fun h rc => IsRecT h rc)`!

---

## 12.4 Lemmas and proofs

We now prove the `R3`-verified top-level theorems in `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean`, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean`,
`WeightsConjBis.lean`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean`, `IntegralStructures/Development.lean`, and `MainConclusion.lean`,
and then map out the 66,167-module internal Shimura-variety / congruence / theta-lift proof cone.

Compact-open fixed spaces and the duality used by NuPair are developed in [§12.4.5](#1245-compact-open-fixed-spaces-and-the-smooth-contragredient).

### 12.4.1 Multisegment assembly of partial local Langlands (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean`)

**Proposition 12.1 (Constructing `RecTExists` from local Artin reciprocity, supercuspidal seeds, and Langlands multisegments).**
*`UpperTheory.Zero.LLC.RecTExists` holds.*
*(Lean: `lawsT_of_laws` and `isRecT_of_isRec`, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:91,106`;
`UpperTheory.Zero.LLC.recTExists`, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20`.)* [Lean, read]

*Proof.* Open `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20–66` (`R3` for this file; `R2` `[Lean]` for the imported sub-lemmas
in its 26,672-module cone):

1. **Local Artin map and supercuspidal seed (`:23–24`):** Fix $(E, \Omega, A, w, h)$ with completion
   $k = E_w$. `artEx` (`:23` `[Lean]`) constructs the local Artin reciprocity homomorphism
   `a : Weil h →* kˣ` satisfying `ha : IsLocalArtin h a`, and `cuspEx` (`:24` `[Lean]`) constructs a
   seed map `r : IrrGL k → WD h` obeying the supercuspidal axioms `hr` (exact rank, $\mathrm{GL}_1$
   compatibility `hr.one`, irreducibility `hr.irr` on supercuspidals, and depth-zero Green `hr.type`).
2. **Langlands multisegment extension (`:25–28`):** Invoking `exists_isLExt` (`:26` `[Lean]`) with
   Langlands exhaustion `Pr.exh` and multisegment uniqueness `Pr.multi` `[BushnellKutzko1993]` extends `r`
   from supercuspidals to all irreducible smooth representations `rc : IrrGL k → WD h` by sending the
   Langlands quotient $L(\Delta_1, \dots, \Delta_m)$ of any multisegment `l` to the direct sum of
   segment Weil–Deligne parameters `segSum rc l`, while agreeing with `r` on every supercuspidal
   (`hcusp : x.IsCusp → rc x = r x`, `:27–28`)!
   The proof supplying `Pr.exh` and its dependence on the Jacquet and segment-production arguments are in [§12.4.8–10](#1248-why-ordered-segment-quotients-exhaust-the-irreducible-representations).
3. **Verifying all 12 clauses of `LawsT` (`:29–66`):**
   - `dim`, `absCentral`, and `central` (on `Good x`) follow from `extDim` (`:29, 33, 38, 40` `[Lean]`);
   - `one`: every $1$-dimensional character `.ofChar χ hχ` is cuspidal (`isCusp_ofChar`), so
     `rc (.ofChar χ hχ) = r (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) ...` (`:34`);
   - `langlands`: for `IsL l x.rep`, `hrc l x hl` gives `rc x = segSum r l`, and since the initial
     representation $\Delta.\mathrm{first}$ of every Zelevinsky segment $\Delta$ is supercuspidal
     (`Δ.isCusp_first`, `:51`), `r` equals `rc` on every segment (`:45–51`);
   - `cusp`: on supercuspidals `rc x = r x`, which is irreducible by `hr.irr` (`:52–54`);
   - `nu` and `twist` (on `Good x`) follow from `extTw` (`:30, 37, 55–57` `[Lean]`);
   - `dual`, `inj`, and `depth` (on `Good`) follow from `extDual`, `extInj`, and `extDepth` (`:41–43` `[Lean]`);
   - `type`: by `typeIff` (`:58` `[Lean]`), it suffices to check `TypeAt` on representations $\sigma$
     inflated from a cuspidal Green representation $\tau$ of $\mathrm{GL}_n(\mathbb F_g)$; by
     `isCuspidal_of_inflates` (`:64` `[Lean]`), any depth-zero inflation of a cuspidal representation
     is **automatically supercuspidal** (`hx : x.IsCusp`), so `rc x = r x` and `hr.type` concludes (`:58–66`)! $\square$

### 12.4.2 How `AwayB.tor` upgrades weak compatibility to exact equality, and the master closure (`MainConclusion.lean`)

Next let us verify two crisp `R3` deductions: first, `aRead_of` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean:105–113`), which shows
in 9 lines how downstream consumers upgrade `AwayB` to **exact Weil–Deligne equality** `x = rc (algNorm σ)`;
second, `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7–14`, which wires P14 + P15 + P12 + P18 into `EveryCharacter` and `RiemannHypothesis`!

**Proposition 12.2 (Upgrading `AwayB` on unlinked/toral places via `aRead_of`, and closing `MainConclusion.lean`).** [Lean, read]

1. *(`aRead_of`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean:105–113`)* *Assume `PlainRec` (`:49–53`, asserting that local components
   $\sigma$ satisfying the window/unlinked condition `WinAt π t w` are `PlainTor`, so `rc (algNorm σ)`
   satisfies `Tor` and `mono0`). Then `ARead` (`:98–103`) holds: for every regular algebraic $\pi$ with
   attached Galois representation $r$ satisfying `WitA ι r` (`:27–30`), at every place $w$ with either
   $w \nmid \ell$ or `Unl1 r w` (flag characters $\kappa_i \neq \kappa_j \chi_{\mathrm{cyc}}$ on $D_w$),
   **every** $x \in \mathrm{WD}(h)$ satisfying `AwayB x (rc (algNorm σ))` satisfies **`x = rc (algNorm σ)`**!*
2. *(`everyCharacter_of_row` and `everyCharacter`, `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7,10`)* *Given `galoisLocalGlobalStrong_recParameter : Row0b recT`
   (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`) and `recTExists : RecTExists` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20`), `OpenLiteratureStatements`
   (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215`) and `VWin` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`) are both inhabited,
   proving `UpperTheory.EveryCharacter` and `RiemannHypothesis`!*

*Proof.*
(1) Fix $w$ satisfying $(w \nmid \ell) \vee \mathrm{Unl1}\,r\,w$ (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean:106`). If $w \mid \ell$,
the first clause of `WitA` (`hW.1`, `:28`) upgrades `Unl1 r w` to `PotUnl r w` (`:110`); thus in both
cases $(w \nmid \ell) \vee \mathrm{PotUnl}\,r\,w$ holds, so the second clause of `WitA` (`hW.2`, `:29–30`)
produces `hwin : WinAt π t w` (`:108–111`). Feeding `hwin` into `PlainRec` (`:112`) yields `h2 : Tor (rc (algNorm σ))`
and `h3 : (rc (algNorm σ)).mono0`. Therefore, for *any* $x$ satisfying `k : AwayB x (rc (algNorm σ))`,
projecting `k.tor h2 h3` (`:113`) gives `x = rc (algNorm σ)` immediately!

(2) Look at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215–218` [Lean, read]:
```lean
structure UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop where
  caraianiLocalGlobalDual : _root_.UpperTheory.One.M.Row
  localLanglandsExists : _root_.UpperTheory.Zero.LLC.RecTExists
  galoisRepOfPolarizedPairLit : _root_.UpperTheory.One.M.Row
```
Since `UpperTheory.One.M.Row` (`src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean:6`) is definitionally `Row0b (fun h rc => IsRecT h rc)`, a
single proof `h` of `Row0b recT` fills **both** the first and third fields of `OpenLiteratureStatements`,
while `recTExists` fills the second field: `⟨h, recTExists, h⟩ : OpenLiteratureStatements`
(`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:8`)! Simultaneously, Theorem 11.4 (`vwin_of_row h`) produces `VWin`. Passing both
into `every_character_of_literature_of_vWin` proves `EveryCharacter`, and applying it to
`h := galoisLocalGlobalStrong_recParameter` proves `everyCharacter` (`:10–11`)! $\square$

### 12.4.3 Top-level spine of `galoisLocalGlobalStrong_recParameter` (`RowSrc.lean`, `IntegralStructures/Development.lean`)

Let us read the top five files of node **P14** in full (`R3` / `[Lean, read]`): `RowSrc.lean` (8 lines),
`GaloisRepresentationsOfThetaLift.lean` (8 lines), `IntegralStructures/Development.lean` (33 lines),
`WeightOneGeometricRealization.lean` (13 lines), and `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean` (5 lines).

**Proposition 12.3 (Top-level assembly of `Row0b recT` from Shimura geometry, congruences, and stable-range theta lifts).**
*Assume:*
- *`geoOne_holds : GeoOne` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean:11`, proved from the algebraic
  holomorphic Lefschetz fixed-point formula `lefschetz_fixedPoint_finite_etale_correspondence`, `:7–9`),*
- *`wtLacEx_holds` (lacunary $\ell$-adic weight interpolation, giving `CongFinOdd` via `congFinOdd_of_ex`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean:28`), and*
- *`tLiftK : TLiftK` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean:4`, stable-range global theta-lift non-vanishing on definite unitary groups).*

*Then `Row0 recT` and `Row0b recT` hold (`galoisLocalGlobalStrong_recParameter`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`).* [Lean, read]

*Proof (top-level proof terms in `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean:20–31` and `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:75–86`).*
1. `seedFinOdd_of_geoOne geoOne_holds` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean:28` `[Lean]`) cuts out odd-rank "seed" Galois
   representations from the cohomology of the PEL/Kuga–Sato variety (`GeoOne`).
2. `limFinOdd_of seed cong` (`:22` `[Lean]`) passes to $\ell$-adic congruence limits via `CongFinOdd`,
   and `toCoreK up congPhi_holds descOffT ...` (`:22` `[Lean]`) invokes `up : TLiftK` **once** to extend
   from odd rank to even rank (by the two-lift subtraction trick of Example 12.2.2) and `coreAll_of_core`
   (`:21` `[Lean]`) extends to all CM fields (`CoreAll`).
3. `rest` (`:24–25` `[Lean]`) combines `CoreAll` with spherical local–global compatibility
   (`galoisCompat_unlinkedSupport_of_spherical`) and Iwahori-fixed unlinked compatibility
   (`localGlobalCompatAtIwahoriFixed_of_unlinked`) to inhabit `Row0 recT` (which uses `Away` with
   `IsQp w` in place of `IsQpBig w n`).
4. Finally, `Row0.row0b` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:84–86` `[Lean, read]`) applies `IsQpBig.isQp` (`:18–20`:
   forgetting the $16 n^2 < g$ bound!) to weaken `Away` to `AwayB` (`Props.big`, `:75–82`), producing
   `Row0b recT`! $\square$

### 12.4.4 Architectural map of the 66,167-module proof cone (`[Lean]` / `[Community]` / `[Open]`)

Because `RowSrc.lean` imports **66,167 modules** (37.8% of the archive), human readers have not yet
checked its deep geometric and $p$-adic Hodge files line by line (`[Open]`). However, combining our
declaration-index trace with the multi-stage community reading reports (`LUMI doc 05`,
`aapolipponen/rh-lean-check-lumi/docs/05-galois-representations.md` [Community]) gives a clear
number-theoretic map of what is formalized inside that cone:

1. **Odd-rank geometric seeds without Arthur's trace formula (`WeightOneGeometricRealization.lean`, cone 45,859):**
   Rather than formalizing Kottwitz's $\mathbb F_q$-point-counting formula or Arthur's endoscopic trace
   formula `[Shin2011]`, the archive formalizes a **Harris–Taylor "simple trace formula" over $\mathbb C$**
   `[HarrisTaylor2001]` [Community]:
   - It constructs fine unitary PEL moduli schemes (`GenModel`) and $k$-fold Kuga–Sato fiber powers (`KS`)
     associated to division algebras with involution of the second kind (`HTGroup`), together with its
     own big-site $\ell$-adic étale cohomology and ordinary-locus Eichler–Shimura congruence relation (`ESGen`);
   - Imposing a supercuspidal type at one auxiliary place $w_0$ and regular elliptic support kills
     boundary and endoscopic terms legitimately;
   - Over $\mathbb C$, fixed points of Hecke correspondences on the Kuga–Sato variety are matched via
     complex period-lattice uniformization (`FixK_holds`) with orbital sums on **definite** unitary inner
     forms (`move_definite` — using Hilbert reciprocity and **odd rank $n$**!), evaluated on coherent
     Hodge cohomology by an **algebraically proved Atiyah–Bott holomorphic Lefschetz formula**
     (`lefschetz_fixedPoint_finite_etale_correspondence`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean:9` `[Lean]`)
     and transferred to $\ell$-adic étale cohomology by a Faltings-style crystalline Hodge–Tate comparison
     (`PadicHodgeComparison/`, 538 files `[Open]`) [Community]!
2. **All odd-rank forms via $\ell$-adic congruences and pseudo-characters (`CongFinOdd`, `limFinOdd_of`):**
   Following the Bellaïche–Chenevier / Chenevier congruence philosophy `[BellaicheChenevier2009]` on
   compact definite unitary groups (`[ClozelHarrisTaylor2008]`), arbitrary odd-rank weights and types
   are approximated $\ell$-adically by seed forms, and Taylor/Rouquier pseudo-characters reconstruct a
   semisimple limit representation (`exists_limit_rep`), while Kisin-style Breuil–Kisin frame closedness
   (`ClosedAtL`) preserves crystallinity and Hodge–Tate jumps at unramified places above $\ell$ [Community], `[Open]`.
3. **Even-rank reduction (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean`, cone 20,485):**
   Notice a naming subtlety pointed out by community readers (`LUMI doc 05` [Community]): although the
   top wrapper is named `galoisRepresentations_of_thetaLift`, the stable-range theta lift `tLiftK`
   (proved via Rallis's inner-product doubling method `[Rallis1984]`, `[KudlaRallis1994]`) is used
   **only once**, in `ToCoreK.lean` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean:22`), to reduce even rank $a$ to odd rank $a + t$
   by the two-lift character-peeling argument (`TwoUp`, `PeelAll`) of Example 12.2.2!

---

The P14 calculation proceeds through the
[finite étale correspondence](#the-holomorphic-lefschetz-input-to-the-odd-rank-seed),
the [local Lefschetz weight](#from-a-finite-étale-chart-to-the-local-lefschetz-weight),
the [global Čech comparison](#from-fixed-point-vanishing-to-a-global-čech-boundary),
the [reduced-fibre trace](#from-the-finite-algebra-trace-to-the-reduced-fibre),
and the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre)
that supplies the reduced origin fibre, the [jet forms](#forms-with-prescribed-jets-at-finitely-many-points)
behind its first step, the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets) behind its second, and the [finiteness of the transversal zeros](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes) behind its fifth.

#### The holomorphic Lefschetz input to the odd-rank seed

**Motivation.** A Hecke correspondence has two legs. One pulls a form back
and the other traces it down. At a point of the correspondence space where
the legs agree, their first-order difference supplies a local weight.
The fixed-point formula equates the sum of these weights to a cohomological trace.

**Example (four points) [Expository].** Take $Y=Z$ to be four copies of
$\operatorname{Spec}\mathbb C$, labelled $1,2,3,4$. Set $c_1=\mathrm{id}$
and let $c_2=\sigma=(1\;2)$ fix $3,4$. On $H^0(Z,\mathcal O_Z)=\mathbb C^4$,
pullback sends the indicator function $e_i$ to $e_{\sigma^{-1}(i)}$.
The identity transfer leaves it there. Thus
$$
T=\begin{pmatrix}0&1&0&0\\1&0&0&0\\0&0&1&0\\0&0&0&1\end{pmatrix},
\qquad \operatorname{Tr}(T)=0+0+1+1=2.
$$
The equalizer is $\{3,4\}$. Since $d=a=b=0$, both empty determinants
in the formula below are $1$, and the two local terms are $1+1$.
For arbitrary maps of finite sets, $(Tf)(z)=\sum_{c_1(y)=z}f(c_2(y))$.
Each diagonal entry counts exactly the coincidence points above that $z$.
Several such points can have the same image in $Z$.

**Definitions.** The space denoted `hodgeH s a b` is the coherent cohomology
$H^b(Z,\Omega^a_{Z/\mathbb C})$ of exterior differential forms. Here $a$ is
form degree and $b$ is sheaf-cohomology degree. On affine opens of the
target of a finite étale map, forms upstairs are obtained by base change.
The map `omegaTrace` applies the algebra trace to the upstairs coefficient
of a pulled-back form and keeps the downstairs form. The map `hodgeTrace`
then uses the finite pushforward equivalence and the induced map on
cohomology. In particular the transfer is unnormalized: on functions the
trace of $1$ is the local degree of the cover. [Lean, read]

At a coincidence $y$ with common image $z$, `IsTan` gives affine neighborhoods
and functions $t_l$ downstairs. Its evaluation-linear map on differentials
is an isomorphism on the cotangent fiber upstairs: the $d(c_1^*t_l)$ go to
the standard basis and the kernel consists of combinations with coefficients
vanishing at $y$. The coordinates of $d(c_2^*t_j)$ are $(A_{jl})_l$.
These are the rows of the derivative of the local branch $c_2\circ c_1^{-1}$
in the $t_l$ coordinates. Cotangent columns give the transpose and hence
the same determinants. [Lean, read]

**Proposition (conditional holomorphic trace formula) [Lean, read].**
Let $s:Z\to\operatorname{Spec}\mathbb C$ be projective and smooth of relative
dimension $d$. Let $Y$ have structure map $s'$ and two finite étale maps
$c_1,c_2:Y\to Z$ over $\mathbb C$. Supply a finite set $F$ of complex points
of $Y$ whose membership is equivalent to $c_1(y)=c_2(y)$, and an assignment
$y\mapsto A_y$ of $d$-by-$d$ matrices on the complex points of $Y$.
Assume `IsTan` and $\det(I-A_y)\ne0$ for every $y\in F$. Then for every
$a\ge0$ all spaces $H^b(Z,\Omega^a)$ are finite dimensional for every
$b\ge0$, and
$$
\sum_{b=0}^d(-1)^b\operatorname{Tr}
 \bigl(\operatorname{Tr}_{c_1}\circ c_2^*\mid H^b(Z,\Omega^a)\bigr)
 =\sum_{y\in F}\frac{[t^a]\det(I+tA_y)}{\det(I-A_y)}.
$$
The sign alternates in $b$ at fixed $a$. The numerator is the trace on
the $a$th exterior power. Both the sheaf and the coefficient vanish for
$a>d$. The scheme $Z$ is proper by projectivity and $Y$ is proper by
finiteness over $Z$. The formula uses ordinary algebraic coherent
cohomology. On the compact analytifications, compact supports impose
no additional restriction. The projective hypothesis places this
trace calculation on the spaces themselves, without a boundary term.

**Block trace lemma.** For a finite family of finite-dimensional spaces $M_j$ and blocks
$T_{jk}:M_k\to M_j$, the trace on $\prod_j M_j$ equals the sum of the
diagonal block traces. If $p_k$ and $i_j$ denote projection and
inclusion, write the endomorphism as $\sum_{j,k}i_jT_{jk}p_k$.
Cycling the two factors in the trace inserts $p_ki_j$, which is zero
off the diagonal and the identity on it. A linear isomorphism to this
finite product also transports finite dimensionality and preserves trace.

**Proof (following the archive).**

1. Projectivity gives quasi-compactness and the smooth clopen decomposition
   gives a finite disjoint cover by integral opens $V_j$. The complement
   of each is the union of the others. Put
   $W_{jk}=c_1^{-1}V_j\cap c_2^{-1}V_k$. These clopen pieces partition $Y$,
   and the restricted legs to $V_j,V_k$ are finite étale. At a coincidence
   the common image forces $j=k$. The point lifts uniquely to $W_{jj}$,
   and restriction preserves the equality of the two images and `IsTan`.
   Conversely a coincidence on $W_{jj}$ maps into $F$. The block theorem
   uses the clopen restriction of projectivity on $V_j$.
2. Restriction gives a linear isomorphism from global Hodge cohomology to
   the product over $V_j$, by open-restriction comparison and disjoint-cover
   cohomology. Restrict the trace to $V_j$ and split it over the clopen
   cover $\{W_{jk}\}_k$ of $c_1^{-1}V_j$. Functoriality of pullback identifies
   the $(j,k)$ block as pullback from $V_k$ to $W_{jk}$ followed by transfer
   to $V_j$. The component formula gives finite dimensionality for each
   $b$. Apply the block trace lemma and exchange the finite sums over
   $b$ and $j$. The diagonal fixed sets partition $F$, with the same weights.
3. For an integral target, the proof of the component formula splits $Y$
   into integral clopens using smoothness by étaleness and quasi-compactness
   by finiteness. Clopen inclusions are open and closed immersions, so
   their composites with both legs retain finiteness and étaleness.
   The fixed sets pull back along injective point maps. Restriction
   transports `IsTan` via the top open of the target and its isomorphism
   with the target. Apply the integral formula on each piece. One such
   application gives finite dimensionality for every $b$ if there is a
   source component. If the source has no components, use smooth
   projective Hodge finiteness directly. Add the source transfers and
   compose the pullbacks. Unique point lifts identify the sum of the
   component sums with the sum over $F$.
4. For integral source and target, establish Hodge finiteness first and
   take the two function-field embeddings. The first supplies the extension
   used for the field trace. The proof chooses a finite projective-space
   presentation placing the images of $F$ over the coordinate origin with
   reduced fiber there ([reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre)).
   Pull the affine cover back along $c_1$. In the
   origin chart the affine point comparison and evaluation of pulled-back
   sections identify the coincidence points with the fixed evaluations
   of the normalized coordinate rings in the fiber. The regular-parameter
   lemma expresses each pulled-back coordinate of the second leg as a
   linear combination of first-leg parameters after clearing a denominator
   nonzero at the point. Evaluate the coefficients and divide by that
   denominator to obtain a matrix $M_y$. The local-parameter comparison
   supplies $M_y=P A_y P^{-1}$. Both determinant polynomials are invariant
   under that conjugation.
5. Use the Hodge-to-Čech linear equivalence and the chart calculation
   `exists_chart_lift_of_finite_cover` [Lean]. Its inputs include the
   section comparison, the reduced origin fiber, the absence of fixed
   evaluations on the other standard charts, the first-order equations,
   and determinant nonvanishing. The comparison for the operator uses
   a common Čech cover on $Y$ made from both families of inverse images.
   For a cocycle downstairs, a cocycle on this combined cover restricts
   on the second-leg part to the pulled-back cocycle. On the first-leg
   part, taking its field trace represents the transferred class.
   This realizes the conjugated pull–trace operator on Čech cohomology.
   Finiteness transports to the Čech groups.
   Trace is invariant under this equivalence, so the calculated
   alternating trace is the original trace. Reindex the fixed evaluations
   by the injective map from $F$ and replace the determinants of $M_y$
   by those of $A_y$. Together with the two clopen arguments this proves
   the proposition. $\square$

**Local intersection and comparison [Expository].** In the completed
local ring at $y$, the equalizer is cut out by $c_1^*t_j-c_2^*t_j$.
Their linear terms give $I-A_y$. Invertibility makes these differences
a regular system of parameters, so the pullback of the diagonal has
local length one. The holomorphic local term still has a Jacobian
denominator and a cotangent numerator. For $a=0$ in positive dimension
the term is $1/\det(I-A_y)$. The finite set calculation only illustrates
dimension zero. The analytic graph case belongs to Atiyah–Bott's
elliptic-complex formula. GAGA gives the coherent algebraic-to-analytic
comparison for projective schemes. The archive calculation itself uses
the algebraic Čech equivalence and its compatibility with pullback
and transfer. [Atiyah–Bott, I, Theorem A, pp. 377–378](https://annals.math.princeton.edu/1967/86-2/p07) · [Serre, GAGA, no. 12, Théorème 1, p. 19](https://www.numdam.org/item/AIF_1956__6__1_0/)

**Consumption by `geoOne` [Lean, read].** `weight_one_geometric_realization`
unfolds `HolomorphicLefschetzFormula` and supplies exactly this proposition.
In `geoStep_of`, $Z$ is the Kuga–Sato space at level $N$ and $Y$ is its space
at a deeper level $N'$ with $N\mid N'$. The first leg is the identity
transition. The second is the Hecke transition followed by the diagonal
fiber endomorphism indexed by $\alpha$. `KSProj` supplies projectivity,
the tower supplies the first finite étale leg, and `FixK` supplies the
second leg's finiteness and étaleness, $F$, $A$, the fixed-point hypotheses
and the weighted group-side count. The equality projection at each $a$
is inserted into the normalized Hecke trace, which divides by the nonzero
relative level index. Summing against $(-u)^a$ gives local factors
$\det(I-uA_y)/\det(I-A_y)$. The level index cancels the factor in `FixK`.
The definite-pair and automorphic-trace comparisons then supply the
group-side input for `HodgeTr`. The assembly goes from `HodgeTr` to
`HodgeEig`, using the formula's finiteness projection via `hodgeFin_of`,
and then obtains `KSHodge`. This is the last field of `KSAll`, supplied by
`ksHodge_of_geo`. The final `geoOne_of_parts` takes `KSAll` together with
`steps_holds` and `Pl.planEx_holds`. The geometric construction of those
packages, the group-side comparisons and the separate crystalline/Hodge–Tate
comparison with $\ell$-adic cohomology remain [Lean]/[Open] here.

**Source map.** All archive paths below use A2 with Lean 4.33.1 and joined
SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
The LUMI guide previously outlined the algebraic proof and the complex
trace comparison [Community]. [LUMI guide, lines 89–103](https://github.com/aapolipponen/rh-lean-check-lumi/blob/c6d0e2bc06ae4562d6656c6ef118739670d19eeb/docs/05-galois-representations.md#L89-L103)

| Source | Step in the text |
|---|---|
| `src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/CoeEqAlgebraMapZeroEquiv.lean:50,161–165`, `src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/OmegaPullOmegaTraceOfSecTraceOne.lean:182–195,218–221`, `src/Development/AbelianVarietyTheory/Definitions/Divisors/IsGaloisCover.lean:14–23` | Hodge groups, pullback and transfer, and the tangent predicate. |
| `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LefschetzFixedPointFiniteEtaleCorrespondence.lean:8–15` | Statement of the proposition and delegation to the next theorem. |
| `src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/LefschetzFixedPointFiniteEtaleCorrespondence.lean:22–251,255–358` | Block trace lemma and Steps 1–2. Clopen restriction, comparison, point partition and final summation. |
| `src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/HolomorphicLefschetzFiniteEtaleCorrespondence.lean:15–155` | Step 3, including tangent transport and the empty-index case. |
| `src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/HolomorphicLefschetzFiniteEtaleIntegral.lean:25–70,74–245` | Steps 4–5. Presentation and fixed evaluations at lines 93–156, local matrix and conjugacy at 158–204, Čech calculation and return to the scheme formula at 205–245. |
| `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsHodgeCohomologyEquivCechDifferentials.lean:9–20`, `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsChartLiftOfFiniteCover.lean:7–30` | Comparison and chart calculation as named inputs [Lean]. The [local chart calculation](#from-a-finite-étale-chart-to-the-local-lefschetz-weight) below gives the scoped R3 reading. |
| `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFiniteCoverProjSpaceReducedFibreOriginStatement.lean:8–9`, `src/Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCorrespondenceLocalParametersStatement.lean:162–163`, `src/Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCorrespondenceFamilyStatement.lean:160–165` | Named inputs for the reduced fiber, matrix conjugacy and cocycle-level pull–trace comparison [Lean]; the reduced-fiber producer is read in the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre). |
| `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LefschetzSigmaSums/HodgeTraceFromLefschetzAndGroupSide.lean:92–111,121–140,167`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LefschetzSigmaSums/PGeoStep.lean:16–85` | Exact input contract, correspondence legs, specialization and level normalization. |
| `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LefschetzSigmaSums/KsHodgeOfGeo.lean:7–8`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LefschetzSigmaSums/HodgeTraceOfLefschetzAndGroupSide.lean:42–55` | Passage through group-side inputs to `KSHodge`. |
| `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/GeometricRealizationOfWeightOne.lean:18–25`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean:7–11` | `KSAll`, the exact theorem application, and `geoOne_holds`. |

#### From a finite étale chart to the local Lefschetz weight

The [finite étale trace formula](#the-holomorphic-lefschetz-input-to-the-odd-rank-seed) computes a global trace from local coincidences. Two calculations connect them. First, pullback and transfer must act on the same Čech representative. Second, the fixed-point equations change the normalization of a local top-degree class. The same Jacobian occurs in the second calculation even
when the fixed-point scheme has length one.

The [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre) later in this chapter uses [holomorphic local sections](#holomorphic-local-sections-of-étale-families) to supply the Sard charts and the [change of denominator](#changing-the-denominator-in-cotangent-generation) to transport the resulting transversality to the origin-fibre chart.

**Example (a scaling on the affine line) [Expository].** Take
$c_1(z)=z$ and $c_2(z)=2z$. Both are finite étale of degree one. The only
coincidence is $z=0$. With $t=z$, the difference is $t-2t=-t$, so the
quotient of $\mathbb C[z]_{(z)}$ by the difference is $\mathbb C$ and
the local intersection length is one. The maps on $\Omega^0$ and on
the cotangent line have traces $1$ and $2$. The coefficient of $z^{-1}dz$
in $dz/(z-2z)$ is $-1$. Multiplying by the two traces gives
$L_0=-1$ and $L_1=-2$. Equivalently the two values are the coefficients
of $(1+2s)/(1-2)$. These are local contributions. In fact the same
automorphism extends to $\mathbb P^1$, where the chart at infinity has
multiplier $1/2$. Its contributions $2$ and $1$ give global sums $1$
and $-1$, respectively, as expected from $H^0(\mathcal O)$ and
$H^1(\Omega^1)$.

**Example (two diagonal multipliers) [Expository].** On
$\mathbb A^2_{\mathbb C}$ let $c_1$ be the identity and set
$c_2(z,w)=(2z,3w)$. At $(0,0)$ the equations are $-z=0$ and $-2w=0$.
Their quotient local ring is $\mathbb C$. In the ordered basis
$dz,dw$ the degree-one pullback is diagonal with eigenvalues $2,3$.
On $1$ and $dz\wedge dw$ the eigenvalues are $1$ and $6$. The Jacobian
of the pair of differences is $\operatorname{diag}(-1,-2)$, of
determinant $2$. The coefficient of $z^{-1}w^{-1}dz\wedge dw$ in
$dz\wedge dw/((-z)(-2w))$ is $1/2$. The three local contributions are
$1/2,5/2,3$, obtained by dividing $1,2+3,2\cdot3$ by $2$. The alternating
sum in form degree is $1/2-5/2+3=1$. This last cancellation expresses
the identity $\det(1-A)/\det(1-A)=1$. For each individual form degree
the local weight can differ from the intersection length.

**Definition (local branch).** Let $Y$ and $Z$ be smooth of dimension
$d$ over $\mathbb C$. Write $c_1,c_2:Y\to Z$ for finite étale morphisms,
with pullback along $c_2$ and transfer along $c_1$. At a coincidence
$y$ above $z$, the analytic inverse function theorem gives a germ
$s_y:(Z,z)\to(Y,y)$ inverse to $c_1$. Put $\phi_y=c_2\circ s_y$ and
$A_y=d\phi_y|_z$. We call $y$ nondegenerate when
$\det(1-A_y)\ne 0$. The local branch is a germ **through the specified
point**. Algebraically the corresponding statement is that $c_1$
identifies the completed local rings at the two complex points. An
étale cover can have several sheets and need not have a section over
a Zariski neighbourhood.

**Lemma (the local calculation) [Expository].** At a nondegenerate
coincidence, the local intersection of $(c_1,c_2):Y\to Z\times Z$ with
the diagonal has length one. The local top-degree residue with
insertion of the trace on $a$-forms is
$$
L_a(y)=\frac{\operatorname{Tr}(\bigwedge^a A_y^\vee)}
                 {\det(1-A_y)}
      =\frac{[s^a]\det(1+sA_y)}{\det(1-A_y)}.
$$
Here $A_y^\vee$ is the dual linear map on covectors and the determinant
of the empty matrix is one.

*Proof.* Choose coordinates $t=(t_1,\ldots,t_d)$ at $z$ centred at
zero, and use $c_1^*t$ as coordinates at $y$. In these coordinates
the second leg is $\phi(t)$, with $\phi(0)=0$. Write
$\phi(t)=G(t)t$ with regular analytic coefficients, for instance by
integrating its derivative along the line from $0$ to $t$. In the
algebraic local ring the parameters generate the maximal ideal by
étaleness of the first leg, and each second-leg coordinate lies in
that ideal, so the same expansion exists with local-ring coefficients.
Then $G(0)=A_y$ in the chosen tangent basis. Set
$r=t-\phi(t)=N(t)t$, where $N=1-G$. This matrix is invertible in
the local ring, so the ideal of differences is the maximal ideal.
The quotient has length one and the point is isolated. The forms
$d\phi_i$ reduce modulo the maximal ideal to
$\sum_j (A_y)_{ij}dt_j$. In exterior degree $a$, the coefficient from the
basis wedge indexed by $T$ to the wedge indexed by $S$ is the minor
with rows $T$ and columns $S$. Taking the diagonal sum gives the
coefficient of $s^a$ in $\det(1+sA_y)$ by multilinearity in its columns.

For a germ $f$, integrate $f(t)\,dt_1\wedge\cdots\wedge dt_d/(r_1\cdots r_d)$
over a small positively oriented product of circles in the $r$ coordinates
and divide by $(2\pi i)^d$. In the coordinates $r$ this is the constant
term of $f(t(r))\det(\partial t/\partial r)$ by repeated Cauchy
integration. It is $f(0)/\det N(0)$. Taking the exterior trace as
$f(0)$ gives the formula. The algebraic version uses the same determinant.
The comparison of Koszul complexes on $r$ and $t$ sends the
generators for $r$ to the combinations of the generators for $t$
given by $N$. The top exterior map multiplies by $\det N$.
Consequently a coefficient representing the class in the
$t$ normalization must be multiplied by $\det N(0)$ to represent
the coefficient in the $r$ normalization. Division by this unit is
the origin of the denominator. For $d=0$ the local ring at a complex
point is $\mathbb C$ and the empty residue convention gives the same
conclusion. $\square$

**Theorem (conditional finite étale holomorphic trace) [Lean].** Suppose
$Z$ is smooth projective of pure dimension $d$ over $\mathbb C$,
both legs above are finite étale, and $F$ is the set of all complex
coincidences on $Y$. Assume every member is nondegenerate. For the
following chart proof also assume these named supplies for each integral
piece of the preceding assembly.

- The finite projective chart and fixed-evaluation data (<code>Y1</code>),
  Hodge–Čech comparison and its pullback and transfer naturality, and
  the common-representative lift of step 1.
- The diagonal data <code>ZFam</code>, <code>ZEx</code>, <code>ZId</code>,
  <code>PrB</code> and <code>ZF</code>, and the compatibility of the
  pulled diagonal <code>GMap</code>.
- The combined cocycle <code>YBig</code>, the $T$ comparison
  <code>YCmpT</code> and the $G$ comparison <code>YCmpG</code> under
  the named chart, column and local conditions in the
  [global comparison theorem](#from-fixed-point-vanishing-to-a-global-čech-boundary).
- The cup and edge boundary comparisons <code>LCupRel</code> and
  <code>EdgeB</code>, top trace and linearity <code>TrTop</code> and
  <code>TrLin</code>, and the reduced-fibre evaluation supplied by
  <code>ResidueOfTraceIsFiberSum</code> through
  <code>trace_cechCochain_fraction_eq_sum_fibre</code>, read in the
  [reduced-fibre subsection](#from-the-finite-algebra-trace-to-the-reduced-fibre).

For
$T_{a,b}=\operatorname{Tr}_{c_1}\circ c_2^*$ on
$H^b(Z,\Omega_Z^a)$, the spaces are finite dimensional and
$$
\sum_{b=0}^d(-1)^b\operatorname{Tr}(T_{a,b})
   =\sum_{y\in F}L_a(y).
$$
Here $\operatorname{Tr}_{c_1}$ is the ordinary sheaf transfer
induced from the algebra trace via
$\Omega_Y^a\simeq c_1^*\Omega_Z^a$. The empty sum is zero. Properness
of $Y$ follows from finiteness over $Z$. The coincidence scheme is
closed in $Y$, and the local calculation shows that its local rings
at complex points are reduced of dimension zero. Hence the set $F$
is finite. In the formal statement a finite set and the proof that
it lists precisely these points are supplied explicitly.

*Proof (the chart input to the preceding assembly).* Use the clopen
reductions and the integral Čech comparison of the preceding subsection.
The integral calculation takes $K=\mathbb C(Z)$, $K'=\mathbb C(Y)$,
the field inclusion from $c_1$, and the separate map $j_2$ from $c_2$.
It uses a finite projective coordinate cover with function field $F_0$
and $d+1$ homogeneous coordinates $x_i$. In the distinguished chart
the ratios $t_j=x_j/x_0$ cut out the origin fibre. The chart theorem
assumes the two finite-cover structures, availability of second-leg
charts locally after clearing denominators, a reduced source origin
fibre, absence of fixed evaluations on charts other than zero, and
that fixed evaluations on chart zero lie over the origin. It requires
an exact finite list of those evaluations in that fibre, generation
of the target maximal ideals by the ratios after localization,
the second-leg coordinate expansion with denominators nonvanishing
at the point, and the determinant condition. Its remaining
hypotheses are the cochain lifting property below and finite
dimensionality of the target Čech groups. The integral assembly
supplies these inputs and transports both determinant polynomials
back to the original tangent matrices.

1. **Lift the given representative.** Let $b$ be a target Čech
   cocycle. Use the ordered union of the two inverse-image covers of
   $Y$, with left indices from $c_1$ and right indices from $c_2$,
   and take a cocycle $c_0$ representing $c_2^*[b]$ there.
   Its restriction to the right differs from the componentwise
   pullback of $b$ by a boundary $\delta e$. Extend $e$ to a cochain
   on the union by zero on all indices containing a left index.
   This is a cochain because on right-only intersections it has
   exactly the required coefficients. Right restriction commutes
   with $\delta$, so $c=c_0-\delta\widetilde e$ restricts to the
   given componentwise pullback, and still represents the same
   class. Restrict $c$ to the left and apply the field trace on
   forms coefficientwise. Naturality of the comparison under
   transfer gives exactly the Čech representative of $T_{a,b}[b]$.
   This proves the lifting hypothesis in the chart theorem. It is
   a cochain construction distinct from the inverse branch germ.

2. **Compute the coefficient before changing equations.** In
   chart zero, evaluate at a fixed point $e$. The two evaluations
   from $K$ coincide there. The diagonal cocycle carries an identity
   pairing on exterior degree $a$. In the local wedge bases,
   its coefficient arrays $\alpha_{kS},\beta_{kT}$ satisfy
   $\sum_k\alpha_{kS}\beta_{kT}=\delta_{ST}$. The archive proves this
   by acting with the diagonal tensor on a basis wedge multiplied
   by a fibre idempotent representative, taking trace, and evaluating
   on that sheet. Differentiating the second-leg expansion contributes
   terms involving $t_j\,dg_{ij}$, which vanish at the origin.
   Thus the evaluated pullback coefficients are precisely the minors
   $\mu_{TS}$ of $A_e$. Contracting with the identity pairing leaves
   $\sum_{S,T,k}\beta_{kT}\mu_{TS}\alpha_{kS}=\sum_S\mu_{SS}$.
   This is the numerator, obtained without assuming diagonalizability.

3. **Compare the two local top classes.** The algebraic comparison
   uses the localized chart ring. The relation $r=Nt$ there has
   $\det N(e)=\det(1-A_e)$. The adjugate gives the inverse matrix
   and shows that the two sequences generate the same ideal.
   The numerator from step 2 is the value of a coefficient $s$
   in the coincidence calculation. Choose a chart function $h$
   taking value $L_a(e)$ at each fixed evaluation and zero at the
   other points of the reduced origin fibre, using Chinese
   remaindering. At each fixed evaluation the difference
   $s-(\det N)h$ has value zero and hence lies in the parameter
   ideal. This is the boundary test in the comparison of the
   two top Koszul components. The next subsection proves
   <code>YCmpG</code> using affine detection in the origin column,
   exactness in the other columns and a total-complex primitive.
   The separately supplied <code>YCmpT</code> gives the comparison
   with the top representative of $h\,d\log t_1\wedge\cdots
   \wedge d\log t_d$. Their sum gives the boundary used in step 4.

4. **Take the trace and evaluate the fibre.** In the proof of
   the chart formula, the diagonal identity splits into
   complementary Čech classes of degrees $d-b$ and $b$. Pairing
   each first class with the traced lift of its second class
   computes the matrix trace by contraction, with sign $(-1)^b$.
   The projection formula moves the field trace through this
   pairing. The top functional kills the boundary from step 3.
   On the remaining representative it takes the coefficient in
   the logarithmic volume form, applies the field trace to $F_0$,
   and extracts the constant term. On the reduced origin fibre
   this gives $\sum_e e(h)$, so only the listed fixed points
   enter the answer. For $a>d$ the exterior powers and the
   determinant coefficients both vanish. The preceding integral
   and clopen assembly identifies this alternating Čech trace
   with the desired Hodge trace. $\square$

**Choices, degree, and scope.** A different coordinate system at $z$
conjugates $A_y$ by the derivative of the change of coordinates.
Using different source parameters changes both leg matrices and
cancels in $dc_2(dc_1)^{-1}$. The exterior trace and $\det(1-A_y)$
are therefore intrinsic. For every finite projective cover satisfying the chart hypotheses,
the integral comparison identifies the resulting sum with the same
intrinsic point weights and the same cohomological operator. A
change of Čech representative changes the corresponding images
by boundaries, as in step 1.

On a small analytic neighbourhood the first leg is a disjoint
union of sheets. The transfer is their sum, because multiplication
in a split finite algebra is diagonal. Each coincidence is counted
on its own sheet, even if two coincidences lie above the same
target point. For degree $m$ on a connected component,
$\operatorname{Tr}_{c_1}(1)=m$ and
$\operatorname{Tr}_{c_1}c_1^*=m\,\mathrm{id}$ there. With $m$ disjoint
copies of the scaling example, the local contributions over zero
are $-m$ and $-2m$, while each local quotient still has length one.
The reduced origin fibre used in the proof pertains to the
auxiliary projective coordinate map and also enters with its
ordinary trace. Neither cover introduces a degree average.

When $\det(1-A_y)=0$, the change of coordinates and the unit
comparison fail. The fixed locus may be positive dimensional, as
for the identity, or isolated with multiplicity, as for the germ
$t\mapsto t+t^2$, whose difference generates $(t^2)$ in dimension
one. The latter germ is locally invertible at zero. An isolated
point alone does not justify the simple fraction. The theorem
uses neither limiting fractions at individual degenerate points
nor a formula for fixed components.

**The Kuga–Sato consumer.** In <code>geoStep_of</code> the target is
the level-$N$ Kuga–Sato space of the tower $T$, with structure map
<code>qAt T N</code>. The first leg is the level projection with
<code>T.X.tr</code> at $1$ from $N'$ to $N$. The second is
<code>leg T N' N h b₀ α</code>, incorporating the Hecke element and the
automorphism. <code>FixK</code> supplies the finite coincidence set,
the cotangent data, and the group-side sum identity. The formula
above supplies the alternating trace in $b$ at each fixed $a$.
Only then does the proof multiply by the inverse relative level
index $[\operatorname{lev}(K_N,h):K_{N'}]$, the index of the deeper
level subgroup in the intersection level of the Hecke correspondence.
This scalar relates the raw operator to the normalized Hecke operator.
Summing in form degree with weights $(-u)^a$ gives
$\det(1-uA_y)/\det(1-A_y)$.
The index cancels using the sum identity supplied by <code>FixK</code>.
The preceding subsection records the use in <code>KSHodge</code>
and <code>GeoOne</code>. The construction and group matching behind
<code>FixK</code>, <code>MarkWeightedFixedPointEqDefinitePairOdd</code>,
<code>TraceDefinitePairsEqAutomorphicTrace</code> remain [Lean] / [Open].
The separate crystalline and Hodge–Tate inputs in the geometric seed
include <code>Seam.crysStep_holds</code>,
<code>UpperTheory.Ru.crystallineComparison.phiStep</code>, and
<code>Seam.HT.htSpecGood</code>. Their comparison proofs retain the
same reading boundary.

For a single holomorphic self-map, apply Atiyah–Bott’s Theorem A
to the Dolbeault complex of $\Omega^a$. In antiholomorphic degree $b$,
the fibre trace is the holomorphic exterior trace times the trace on
the $b$th exterior power of the conjugate cotangent map. The alternating
sum over $b$ gives the factor $\overline{\det(1-A)}$. The absolute real
Jacobian in Theorem A is $|\det(1-A)|^2$, so their quotient leaves the
complex denominator $\det(1-A)$. Serre’s GAGA comparison identifies
algebraic and analytic coherent cohomology on the projective target.
The two-leg proof above uses algebraic pullback and transfer.
[Atiyah–Bott I, Theorem A, pp. 377–378](https://annals.math.princeton.edu/1967/86-2/p07)
[Serre, GAGA, §3, no. 12, Théorème 1, p. 19](https://www.numdam.org/article/AIF_1956__6__1_0.pdf)

**Reading the formal proof.** The table gives the new local reading
and the interfaces used to transport its result. Paths start at the
root of archive A2 (Lean 4.33.1, joined archive SHA-256
<code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>).

| Node | Archive path and lines | Role and reading |
|---|---|---|
| <code>exists_chart_lift_of_finite_cover</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsChartLiftOfFiniteCover.lean:7–30</code> | Exported statement and delegation. The conclusion is an alternating trace equality. The representative lift is a hypothesis. R3 [Lean, read]. |
| <code>field0</code>, <code>UpperTheory.Cb.exists_chart_lift_of_finite_cover</code> | <code>src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/ExistsChartLiftOfFiniteCover.lean:101–223</code> | Wires the diagonal, local comparison and trace packages into <code>FieldLe</code>, then <code>Field0</code>. R3 for the assembly body [Lean, read]. |
| <code>etaleCorrespondence_family_statement</code> and <code>lift_cocycle</code> | <code>src/Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCorrespondenceFamilyStatement.lean:22–244</code> | Step 1. It uses pullback naturality twice on the right and once on the left via the identity of the source, and transfer naturality for the first leg. R3 [Lean, read]. |
| <code>field0_of</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/TraceEqZeroOfBot.lean:8–89</code> | Packages the two covers and the localized fractions into <code>Y1</code> for <code>a ≤ d</code>. Above dimension both traces and minors vanish. The target generation and finite-dimensionality arguments are among the hypotheses introduced at line 52, but the proof does not use those two arguments explicitly. R3 [Lean, read]. |
| <code>dtPull_of</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PDtPull.lean:93–156</code> | Leibniz rule and exterior minors by alternating expansion. R3 for the theorem body [Lean, read]. |
| <code>idVal_of</code>, <code>valG_of</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PIdVal.lean:79–196</code> and <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PullbackKahlerDegree.lean:102–206</code> | Step 2. Evaluation of the diagonal action yields the Kronecker delta and <code>sum_delta</code> contracts the wedge matrix. R3 for these bodies [Lean, read]. |
| <code>fixLoc_of</code>, <code>pyc_local</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PFixLoc.lean:6–87</code> and <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYCmpG.lean:12–165</code> | Step 3. The first result builds and inverts the difference matrix. The second uses the vanishing of <code>s − det N · h</code> in the residue field and applies the Koszul boundary criterion. R3 for these bodies [Lean, read]. |
| <code>yMain_of</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYMain.lean:110–239</code> | Interpolates the local quotients, removes the chart's powers of the homogenizing coordinates, and adds the two supplied boundary comparisons <code>YCmpG</code> and <code>YCmpT</code>. R3 for this body [Lean, read]. |
| <code>fieldLe_of</code>, <code>trTop_of</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PFieldLe.lean:216–336</code> and <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PTrTop.lean:11–70</code> | Step 4. Signed cup products form the cocycle <code>Λ</code>. The edge test gives a Čech boundary, transitivity combines the field traces, and <code>alt_trace'</code> identifies the signed pairing with the alternating operator trace. R3 for the named bodies [Lean, read]. |
| <code>deRham_restriction_trace_degree_one</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/DeRhamRestrictionTraceDegreeOne.lean:8–16</code> | Rewrites the top trace as a constant-term evaluation of the ordinary field trace and uses the reduced-fibre sum. R3 for the wrapper [Lean, read]. |
| Chart transport and actual two-leg call | <code>src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/HolomorphicLefschetzFiniteEtaleIntegral.lean:197–245</code> and <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LefschetzSigmaSums/PGeoStep.lean:16–85</code> | The integral proof applies the chart theorem at fixed form degree and transports trace and local weight. The second file normalizes and sums the result for the Kuga–Sato space. See the preceding subsection for the existing R3 reading. |

The R3 entries cover the indicated proof bodies. The imported constructions
of the finite projective cover, reduced origin fibres, regular parameters
and tangent conjugacy, and the natural comparison
<code>exists_hodge_cohomology_equiv_cech_differentials</code> are used at
their interfaces; the projective cover and the reduced origin fibre are
read in the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre).
The diagonal supplies <code>ZFam</code>, <code>ZEx</code>,
<code>ZId</code> and <code>PrB</code>, while <code>GMap</code>,
<code>LCupRel</code>, <code>EdgeB</code> and <code>TrLin</code>
supply the join, boundary and trace comparisons. Their inner proofs,
the producers <code>yBig_of</code> and <code>yCmpT_of</code>,
the imported Koszul exactness and local form bases
(<code>koszulExactBelowLengthOfWeaklyRegular_of_htpy</code>,
<code>koszulTwoInjective_of_gl1</code>, <code>koszulThree_of_det</code>,
<code>locForms_of</code>) are further [Lean] inputs. The supplier
<code>trace_cechCochain_fraction_eq_sum_fibre</code> is read in the
[reduced-fibre subsection](#from-the-finite-algebra-trace-to-the-reduced-fibre). The following subsection proves the <code>yCmpG_of</code> comparison under its named chart and column supplies.

---

#### From fixed-point vanishing to a global Čech boundary

The preceding chart proof compares two cocycles representing a pulled diagonal and a logarithmic top form. A fixed-point evaluation tests a coefficient of a localized Koszul cocycle. The desired conclusion concerns a boundary in the mixed Čech complex of the two covers. The proof passes through an affine Koszul column and then through the total complex. The first passage detects a class by localization. The second constructs a primitive by removing successive Koszul degrees.

**A two-cover calculation [Expository].** Cover $\mathbb A^1_{\mathbb C}$ twice by $U_0=D(t-1)$ and $U_1=D(t)$, keeping the labels of the two copies distinct. Use the regular differential $dt$ as a basis and suppress it in the coefficients. At an intersection indexed by $(I,J)$ use its coordinate ring as coefficients. In this normalized model the $G$ equation is $2t$ and the appended $T$ equation is $t$. Write the total differential as
$$
D=\delta_U+(-1)^{|I|}\delta_V+(-1)^{|I|+|J|}d_K,
$$
with each sign read on the source bidegrees for that summand. Here $d_K$ is exterior multiplication by the equation vector.

Take the combined cocycle $v$ in total degree $3$ with normalized Koszul degree-one component $(2,1)$ on every singleton pair and zero elsewhere. Its Čech differences vanish and its Koszul differential in degree two is $2t\cdot 1-t\cdot2=0$. Restriction to $G$ gives the component $2$ at every singleton pair. In the $G$ complex put a primitive $u$ in Koszul degree zero at the singleton pairs, with
$$
(u_{00},u_{01},u_{10},u_{11})=(1,2,3,4).
$$
Set $c'=\operatorname{res}_Gv+Du$. Its Koszul degree-one coefficients are $2+2t\,u_{ij}$. At $(0,0)$ the coefficients are $s=2+2t$ and $h=1$ after suppressing the common orientation sign, with $s-2h=2t$ vanishing at the origin. The differences in Koszul degree one are $2t,4t,6t,8t$. In the origin column the first is the equation times $1$. In the other three columns $t$ is invertible and division by $2t$ recovers $2,3,4$.

In Koszul degree zero the defect has components $3-1=2$ and $4-2=2$ on the two left edges, and $-(2-1)=-1$ and $-(4-3)=-1$ on the two right edges. At each edge the signed Čech difference of $2t\,u_{ij}$ is canceled by $-2t$ times the edge coefficient, since $|I|+|J|=3$ there. Its Čech differential at the square is $(-1)-(-1)+(2-2)=0$. The signed lift of the four column primitives is exactly $u$, because $|I|+|J|=2$ there. Subtracting $Du$ removes the four singleton components and the four edge components, leaving zero. In particular the four nonzero edge values form the mixed Čech boundary $\operatorname{top}(Du)=\delta u$. This example uses compatible cochains on all mixed intersections, with restrictions in both directions.

**The chart and the columns.** Write $x_0,\ldots,x_d$ for the homogeneous coordinates on the auxiliary projective cover. In the notation of the preceding subsection use $K=\mathbb C(Z)$, $K'=\mathbb C(Y)$ and $j_2$ for the second field map. The two labelled source covers are pulled back from the projective charts through the two legs. For nonempty $I,J$, intersect the charts indexed by $I$ on the first leg and those indexed by $J$ on the second leg. The comparison ring $R_{IJ}$ is the subalgebra of $K'$ generated by the two chart rings, the first-leg chart ring in $K'$ and the integral closure in $K'$ of the second chart ring transported through $j_2$. The coefficient module $M_{IJ}$ consists of regular $d$-forms in the archive's field-form model. Both inclusions under enlargement of $I,J$ are part of the coordinate system. The mixed Čech complex uses both nonempty label sets. In the archive's grading a Čech component here has degree $p=|I|+|J|$, two above the usual double Čech degree.

A further ordered index set labels equations. The $G$ list comprises the pulled diagonal minors $X_iY_j-X_jY_i$ followed by the pulled auxiliary equations from the diagonal representative. The $T$ list uses the $d$ coordinates $X_1,\ldots,X_d$ of the first leg. Here $X_i,Y_j$ are the images of $x_i,x_j$ under the respective field maps. For bidegree $(a_\ell,b_\ell)$ the normalized equation on a chart pair with pivot $(i,j)$ is $\rho_\ell=z_\ell/u_\ell$, where $u_\ell=X_i^{a_\ell}Y_j^{b_\ell}$. The minima of the two label sets give the archive's pivots. The twisted coefficient of a Koszul subset $L$ is in $(\prod_{\ell\in L}u_\ell)M_{IJ}$. Dividing by that product on each fixed column conjugates the differential using $z_\ell$ to exterior multiplication by the normalized equations $\rho_\ell$. This is the equivalence supplied by <code>RS</code>. In the global construction we use the twisted complex, where restriction in the Čech directions is defined on these submodules. An empty label set on either side has zero coefficient module. Projection to the component $L=\varnothing$, called <code>top</code>, is a cochain map to the mixed Čech complex, since the Koszul differential increases $|L|$.

**Theorem (conditional global comparison) [Lean, read].** Assume the finite chart and diagonal data <code>Y1</code> and <code>ZF</code> of the preceding theorem and the following supplies for this chart system.

- <code>RYBasic</code>, <code>SysOk</code>, <code>SysBasic</code> and <code>WdUni</code> supply the compatible total complexes, restrictions to ordered equation subsets, finite-set and sign identities, and the boundary map <code>top</code>. <code>RS</code> supplies the normalized column isomorphisms.
- <code>YCols</code> supplies admissibility for the $G$, $T$, and combined lists, exactness in each Koszul degree strictly below $d$ on every mixed intersection, and exactness in all degrees away from $(I,J)=(\{0\},\{0\})$ for $G$ and for the combined list. <code>PtG</code> locates every common zero of the $G$ equations over a listed fixed evaluation, with the stated identification of local rings. <code>YKE</code> detects column boundaries from their localizations at all common zeros. The coefficient inclusions and evaluation in those localizations use <code>OmLoc</code> and <code>ValBasic</code>.
- At the fixed evaluations, <code>FixLoc</code>, <code>LocReg</code>, <code>LocMax</code>, <code>LocForms</code>, <code>K1</code>, <code>K3</code> and <code>KoszulBoundaryOfComponentMemIdeal</code> supply the local coordinate change, regularity, parameter ideal and Koszul tests used in the preceding subsection. The total boundary construction uses <code>CechKoszulSystemBoundaryCriterion</code>, proved below from the column hypotheses and the compatible total differential.

Let $v$ be a total degree $d+2$ cocycle for the combined list, and $c'$ one for $G$. In the origin singleton column assume that the distinguished $T$ component of $v$ normalizes to $(-1)^d h\omega$, and the distinguished $G$ component of $c'$ normalizes to $(-1)^d s\omega$, where $\omega=dt_0\wedge\cdots\wedge dt_{d-1}$ and $t_\ell=X_{\ell+1}/X_0$ for $0\leq\ell<d$. Here $h$ is regular on the first origin chart and $s\in K'$ is regular at the listed fixed evaluations. The distinguished $G$ indices are the minors with second index $0$ and first index different from $0$. Suppose $s(e)=h(e)\det(1-A_e)$ at every listed fixed evaluation $e$. Then
$$
\operatorname{top}c'-\operatorname{top}v
$$
is a boundary of degree $d+2$ in the mixed Čech complex. This is <code>YCmpG</code>. The two normalization factors removed from the raw components are $X_0^d$ and $(X_0Y_0)^d$, respectively.

**Lemma (lifting column primitives).** Let $d\ge0$. Let $D=D_C+D_K$ on a finite total complex $C^{p,q}$ with $C^{p,q}=0$ for $q<0$, with $D_C$ raising $p$, $D_K$ raising $q$, $D^2=0$, and $D_K=(-1)^p d_K$ in each column. Suppose a total degree $n$ cocycle $w$ has no components in $q>d$. Assume $H^q(d_K)=0$ in every column for $q<d$, and that the $q=d$ component in each column of degree $p=n-d$ is a $d_K$-boundary. Then $w$ is a total boundary.

*Proof.* Choose column primitives $u_b$ of Koszul degree $d-1$ for the degree $d$ components, where $b$ is the combined left and right chart index. Extend them by zero to all other degrees and set $y_d(b,L)=(-1)^{|b|}u_b(L)$. The two signs cancel in $D_K y_d$, which equals the degree $d$ part of $w$. The term $D_C y_d$ has Koszul degree $d-1$, so $w-Dy_d$ is a cocycle supported in degrees at most $d-1$. In general, for a remaining cocycle supported in degrees at most $k<d$, its component in degree $k$ is $D_K$-closed. Indeed its total differential in degree $k+1$ is exactly $D_K$ on that component. Column exactness supplies a primitive of degree $k-1$. Apply the same signed extension and subtraction. At $k=0$ exactness means that the kernel is zero, because degree $-1$ is zero. The sum of all chosen cochains is a total primitive. If $d=0$, the top-degree boundary hypothesis already forces the degree-zero component to vanish. In the archive <code>localOne_of_gl1</code> constructs the first signed cochain in the coordinate system, <code>colQEx_of</code> assembles the subsequent column primitives, and <code>filtrationBoundaryCriterion_of_wdBasic</code> performs the downward induction. The wrapper <code>coordinateSystem_degree_one_of_universalDerivation</code> matches the columns with <code>colCx</code> and handles empty index sets. $\square$

*Proof of the theorem.* Restrict $v$ to the ordered $G$ indices. This preserves the cocycle condition since the differential at a subset uses only its own faces. The difference $w=c'-\operatorname{res}_Gv$ is thus a total cocycle. In degree $d+2$ the Koszul degree is at most $d$, since each nonzero component has $|I|,|J|\geq1$. At $q=d$ precisely the singleton pairs occur. Their columns are cocycles, since no Čech terms arrive from a smaller allowed pair. This is <code>pyc_colZ</code>.

In the origin column, apply <code>RS</code> before localizing. If $v_G,v_T$ denote the two distinguished components of the normalized combined column, and $y=(-1)^d s\omega$, the distinguished defect is $y-v_G$. At each common zero the local relation $r=Nt$ and the local Koszul comparison of the preceding subsection give
$$
v_G-(\det N)v_T\in (t_0,\ldots,t_{d-1})M_e,
\qquad
y-(\det N)v_T=(-1)^d(s-(\det N)h)\omega\in(t_0,\ldots,t_{d-1})M_e.
$$
Here $M_e$ denotes the localized module. The second inclusion uses both zero residue and generation of the maximal ideal by the $t_\ell$. Subtracting the two expressions and using $(t)=(r)$ gives the distinguished-component ideal condition for $w$. The local boundary test applies to the entire normalized column cocycle. This is the use of <code>pyc_local</code> inside <code>collapsed_column_origin</code>.

For the affine column, consider the class of $w$ in the quotient of cochains by Koszul boundaries. Localization commutes with this quotient. At a maximal ideal where some equation $\rho_\ell$ is a unit, the Koszul complex contracts. Explicitly, contraction $\iota_\ell$ deletes the basis vector for $\ell$ with its alternating position sign. For a wedge element $\alpha$, the rule $\iota_\ell(\rho\wedge\alpha)=\rho_\ell\alpha-\rho\wedge\iota_\ell\alpha$ gives $d_K\iota_\ell+\iota_\ell d_K=\rho_\ell$. Thus $\rho_\ell^{-1}\iota_\ell w$ is a local primitive. At a common zero the preceding calculation applies by <code>PtG</code>. Every maximal ideal of the finite-type complex chart algebra gives a complex evaluation. If the quotient class were nonzero, its annihilator would be proper and contained in a maximal ideal. The class could not vanish in that localization, since any element clearing it there would lie outside that maximal ideal. This proves the affine detection used by <code>YKE</code> via <code>LG</code>. Convert the resulting normalized boundary back by <code>RS</code>.

At every other singleton pair use the all-degree exactness supplied by <code>YCols</code>. Its producer rules out a common zero on every mixed intersection other than the origin singleton pair: <code>PtG</code> forces both label sets to be $\{0\}$, and a zero for the combined list would also be a zero for $G$. The producer uses the same unit contraction and affine detection there. For the below-$d$ exactness, its common-zero branch uses that the equations generate the regular parameters locally, via <code>PtG</code>, <code>PtT</code> and <code>FixLoc</code> as appropriate. These are separate obligations from the residue identity at the origin.

The lemma now applies to $w$. If $D y=w$, taking $L=\varnothing$ gives $\delta(\operatorname{top}y)=\operatorname{top}c'-\operatorname{top}v$. The restriction discarded only equation labels, so it preserves the empty-subset component. This proves the comparison. $\square$

**Why the hypotheses matter [Expository].** On $\mathbb P^1$, take the two standard affine charts with coordinates $t$ and $u=1/t$. The overlap cocycle $\eta=dt/t$ has zero class on restriction to each single chart. For a two-chart cover a boundary has the form $f(u)\,du-g(t)\,dt$. Written in $t$, this is $-f(1/t)t^{-2}dt-g(t)dt$. The first term has powers at most $-2$ and the second powers at least $0$. The coefficient of $t^{-1}dt$ therefore distinguishes $\eta$ from every boundary. Conversely all other Laurent monomials lie in the image, so this quotient is one-dimensional. The affine cover computes $H^1(\mathbb P^1,\Omega^1)$ by the affine-intersection Čech comparison. Even a test by the representative's value at an origin can miss this class: use the chart in $\mathbb P^1$ obtained by removing the point $t=1$, together with the chart obtained by removing $t=0$. With $z=t/(t-1)$, these are the $z$ and $1/z$ affine charts. The same class generator $dz/z$ on the overlap has representative $(1-z)dz/z=dz/z-dz$ whose value at $z=1$ is zero, and whose Laurent coefficient at $z^{-1}dz$ is $1$. Thus local exactness of restrictions and even a vanishing value on the overlap leave a global obstruction. The lifting lemma removes it only for a compatible total cocycle with the specified column exactness and a primitive at the highest Koszul degree. [Stacks Project, Lemma 30.2.6](https://stacks.math.columbia.edu/tag/01XD)

**The actual consumer.** In <code>yMain_of</code>, Chinese remaindering gives $h$ with values equal to the local quotient at the fixed evaluations and zero elsewhere on the origin fibre. The pulled diagonal is $c'=gY(j_2)(c)$, where $c$ is the chosen diagonal-system cocycle. The test for $s$ comes from <code>ValG</code>; the specialization <code>hsv</code> multiplies the chosen values of $h$ by the nonzero determinants. The combined cocycle $v$ is the <code>c1</code> returned by <code>hBig</code>. At the actual <code>hCG</code> call, the arguments are $h$, $s$, that valuation identity, the combined cocycle and its prescribed component, and the pulled diagonal and its prescribed component. The second boundary is supplied by <code>hCT</code> on restriction to the $T$ indices. Its singleton support condition uses the support of $v$ supplied by <code>YBig</code>. Adding the two boundaries cancels $\operatorname{top}v$ and compares the pulled diagonal to the edge image of the logarithmic representative from the preceding subsection. The reduced-fibre trace and the actual geometric and group-side matching enter later, through the named supplies recorded above.

**Reading and sources.** The proof follows A2, joined archive SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>. See the path and reading-level table below. For the commutative-algebra steps, the Stacks Project gives maximal-ideal localization detection and the Koszul homotopy in homological indexing. The archive uses cochain indexing and checks the twisted coefficients and the two Čech directions explicitly. [Stacks Project, Lemma 10.23.1](https://stacks.math.columbia.edu/tag/00HN) · [Lemma 15.29.5](https://stacks.math.columbia.edu/tag/0626)

| Declaration | A2 source | Reading |
|---|---|---|
| <code>yMain_of</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYMain.lean:111–239</code> | Actual consumer. Lines 209–239 apply <code>hCG</code> and <code>hCT</code> and cancel the middle mixed cochain. Prior R3, rechecked. |
| <code>pyc_local</code> and its local helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYCmpG.lean:11–163</code> | Prior R3, rechecked. Compares normalized degree-$d$ components modulo the parameter ideal. |
| <code>pyc_colZ</code>, <code>collapsed_column_origin</code> and <code>yCmpG_of</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYCmpG.lean:170–366</code> | R3. Normalizes by the homogeneous units, invokes affine detection, checks all singleton pairs, and projects the total boundary. |
| <code>yCols_of</code> and its helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYCols.lean:7–151</code> | R3. Assembles admissibility, below-$d$ exactness and all-degree exactness off the origin column. Admissibility of the diagonal minor list uses <code>ThMuLat</code>. |
| <code>yKE_of</code> and its helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/ExistsInv.lean:16–117</code> | R3. Splits the common-zero and invertible-equation cases and descends the local boundary. |
| <code>lG_of</code> and its helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/ExistsPt.lean:19–180</code> | R3. Clears local denominators in a finite tuple and detects the boundary by the annihilator ideal. |
| <code>htpy_of</code> and its helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/WdApply.lean:8–114</code> | R3. Signed insertion on subset cochains implements contraction on the exterior algebra. |
| <code>coordinateSystem_degree_one_of_universalDerivation</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/CoordinateSystemDegreeOneOfUniversalDerivation.lean:7–58</code> | R3. Matches the abstract filtered boundary criterion to the twisted chart coefficients. |
| <code>localOne_of_gl1</code> and its helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PoincareLelong.lean:6–122</code> | R3. Extends the highest Koszul column primitives with the sign of the Čech degree. |
| <code>colQEx_of</code> and its helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PColQEx.lean:7–165</code> | R3. Assembles column primitives in lower Koszul degrees. |
| <code>filtrationBoundaryCriterion_of_wdBasic</code> and its helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/FiltrationBoundaryCriterionOfWdBasic.lean:9–210</code> | R3. Subtracts the differential of the signed primitive and descends in Koszul degree. |
| <code>PtG</code>, <code>YKE</code>, <code>YCols</code>, <code>YCmpG</code>, <code>GMap</code> and related interfaces | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/ResidueOfTraceIsFiberSum.lean:34–218</code> | Definitions. |
| <code>top</code>, <code>Sys</code>, and <code>sysY</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/MonoM.lean:46–176</code> | Definitions for the mixed complex, normalization and coefficients. |
| <code>RS</code>, <code>L1</code>, and the system boundary criterion | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/LiftFactorization.lean:61–139</code> | Definitions. |
| <code>R2</code>, <code>RY</code>, <code>gY</code> and <code>Val</code> | <code>src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/Edge1.lean:108–128</code> | Definitions of the join, coefficient pullback and evaluation. |
| Chart assembly | <code>src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/ExistsChartLiftOfFiniteCover.lean:123–197</code> | Prior R3 for the assembly body. Lines 175–188 wire <code>yKE_of</code>, <code>yCols_of</code>, <code>yCmpG_of</code> and <code>yMain_of</code> together. |

R3 applies to the named proof bodies. The remaining geometric chart inputs and
the suppliers <code>ptG_of</code>, <code>ptT_of</code>, <code>locEq_of</code>,
<code>rYFT_of</code>, <code>rYBasic_of</code>, <code>sysOk_of</code>,
<code>sysBasic_of</code>, <code>rS_of</code>, <code>wdUni_of</code>,
<code>WdBasic</code>, <code>OmLoc</code>, <code>ValBasic</code>,
<code>LocReg</code>, <code>LocMax</code>, <code>LocForms</code>,
<code>K1</code>, <code>koszulTwoInjective_of_gl1</code>,
<code>koszulThree_of_det</code>, <code>thMuLat_of</code>, <code>yBig_of</code>, <code>yCmpT_of</code>,
<code>GMap</code>, <code>ZFam</code>, <code>ZEx</code>, <code>ZId</code>,
<code>PrB</code>, <code>LCupRel</code>, <code>EdgeB</code> and <code>TrLin</code>
are used through their interfaces in this subsection. The separate
<code>trace_cechCochain_fraction_eq_sum_fibre</code> proof is read in the
[next subsection](#from-the-finite-algebra-trace-to-the-reduced-fibre). The geometry of
<code>FixK_holds</code> and the group-side matching
<code>MarkWeightedFixedPointEqDefinitePairOdd</code> and
<code>TraceDefinitePairsEqAutomorphicTrace</code> retain their [Lean] / [Open] status.

---

#### From the finite-algebra trace to the reduced fibre

The [chart proof](#from-a-finite-étale-chart-to-the-local-lefschetz-weight) ends with a single number. Once the [global comparison](#from-fixed-point-vanishing-to-a-global-čech-boundary) has removed every boundary, the alternating trace is the residue of one traced top form $h\,\mathrm{vol}_0$. Here $h$ is the Chinese-remainder coefficient whose values are the local weights. This subsection proves that the residue is the sum of the values of $h$ over all points of the origin fibre, each counted once. This is the content of <code>trace_cechCochain_fraction_eq_sum_fibre</code>.

**Motivation.** Three things could spoil the count. The trace of $h$ is a priori a rational function, and the residue functional of the chart proof is determined only on Laurent polynomials. Reduction at the origin need not commute with the trace when the cover is not locally free there. A fibre point may also have a residue field larger than the ground field, or a multiplicity. Under the archive's hypotheses none of this happens. The trace is a polynomial, the cover is locally free over the chart, and every fibre point is a reduced point with residue field $k$.

**Example (two coincidences over one origin) [Expository].** Return to the scaling $c_1(z)=z$, $c_2(z)=2z$ on $Z=Y=\mathbb P^1$ from the [local weight subsection](#from-a-finite-étale-chart-to-the-local-lefschetz-weight). The coincidences are $z=0$ and $z=\infty$, with multipliers $2$ and $1/2$. The local weights are $L_0(0)=-1$, $L_1(0)=-2$, $L_0(\infty)=2$ and $L_1(\infty)=1$. The chart proof needs an auxiliary finite map to $\mathbb P^1$. It must send both coincidences to the origin of the first chart and no coincidence into the second chart. Take
$$
t=\frac{z}{(1+z)^2}.
$$
Its zeros are $z=0$ and $z=\infty$, both simple. Put $v=1/(1+z)$. Then $t=v-v^2$. The preimage of the chart $t\ne\infty$ is $\mathbb P^1\setminus\{-1\}$, with ring $B=\mathbb C[v]$, which is free over $A=\mathbb C[t]$ with basis $1,v$. The fibre ring $\mathbb C[v]/(v^2-v)\cong\mathbb C\times\mathbb C$ is reduced. Since $v\cdot v=v-t$, multiplication by $v$ has matrix
$$
M_v=\begin{pmatrix}0&-t\\1&1\end{pmatrix},\qquad \operatorname{Tr}_{B/A}(v)=1,\qquad \operatorname{Tr}_{B/A}(1)=2=[\mathbb C(z):\mathbb C(t)].
$$
At $t=0$ the matrix has eigenvalues $0$ and $1$. These are the values of $v$ at the two fibre points, $z=\infty$ and $z=0$. The coefficient with the prescribed values is $h_a=L_a(\infty)+(L_a(0)-L_a(\infty))v$, so
$$
\operatorname{Tr}_{B/A}(h_a)=2L_a(\infty)+L_a(0)-L_a(\infty)=L_a(0)+L_a(\infty).
$$
This is $1$ for $a=0$ and $-1$ for $a=1$, the global sums found in the local weight subsection. Here the trace is a constant. For $h=v^3$ it is $1-3t$, whose value at $t=0$ is again $0^3+1^3$. The other chart has preimage $\mathbb C^\times_z$, where $z\ne 2z$, so it contains no coincidence. Its ring $\mathbb C[z,z^{-1}]$ is integral over $\mathbb C[1/t]$ because $1/t=z+2+z^{-1}$. The degree $2$ of the auxiliary map enters only as $\operatorname{Tr}(1)=2$. A trace normalized by $1/2$ would halve both answers.

**Definitions.** Fix a field $k$ of characteristic zero and a field $F$ with elements $x_0,\ldots,x_d\ne0$ such that the ratios $t_j=x_j/x_0$, $1\le j\le d$, are algebraically independent and generate $F$ over $k$ (<code>IsPd</code>). For a nonempty set $I$ of indices let $A_I\subset F$ be the $k$-algebra generated by the $x_j/x_i$ with $i\in I$. It is the coordinate ring of the intersection of the standard charts $D_+(x_i)$, $i\in I$. Thus $A_{\{0\}}=k[t_1,\ldots,t_d]$, and for the set of all indices $A_I$ is the Laurent polynomial ring in the $t_j$. Let $L/F$ be a finite separable extension and $B_I$ the integral closure of $A_I$ in $L$ (<code>rB</code>). The data form a *finite cover* (<code>IsFinCover</code>) if moreover every $B_{\{i\}}$ is smooth over $k$. Write $A=A_{\{0\}}$, $B=B_{\{0\}}$, $\mathfrak p=(t_1,\ldots,t_d)\subset A$ and $J=\mathfrak pB$.

- The *fibre points* are the $k$-algebra maps $e:B\to k$ with $e(t_j)=0$ for all $j$ (<code>fib</code>). The *fibre ring* is $B/J$. It is *reduced* when it has no nonzero nilpotents (<code>RedFib</code>).
- The *logarithmic volume form* is $\mathrm{vol}_0=\frac{dt_1}{t_1}\wedge\cdots\wedge\frac{dt_d}{t_d}$ in the exterior algebra of $\Omega_{L/k}$ over $L$.
- A *top coefficient* is an $L$-linear map $\tau$ with $\tau(\mathrm{vol}_0)=1$ which vanishes on forms of degree other than $d$ (<code>IsTop</code>).
- A *residue functional* is a $k$-linear map $\rho:F\to k$ with $\rho(1)=1$ and $\rho(\prod_jx_j^{m_j})=0$ for every nonzero $m\in\mathbb Z^{d+1}$ with $\sum_jm_j=0$ (<code>IsRes</code>). These products are exactly the Laurent monomials in the $t_j$. So $\rho$ is the constant term on Laurent polynomials, and nothing more is prescribed. The archive produces one by taking a linear form that is $1$ at $1$ and vanishes on the span of the other monomials (<code>exists_isRes</code>).
- The *trace functional* is $\operatorname{tr}_F=\rho\circ\operatorname{Tr}_{L/F}\circ\tau$ (<code>trF</code>). For $h\in L$ the Čech $d$-cochain <code>locCoch</code> $h$ on the $d+1$ charts is $h\,\mathrm{vol}_0$ on the intersection of all charts and zero elsewhere. This is the fractional representative of the chart proof, with denominators $t_1\cdots t_d$.

In the actual call, $L$ is the function field $K'$ of the source $Y$, viewed over $F$ through the target field $K$ and the first leg $K\to K'$. The fibre points are the points of $Y$ lying over the origin of the auxiliary chart under $Y\to Z\to\mathbb P^d$.

**Theorem (conditional reduced-fibre trace) [Lean, read].** Let $k$ be algebraically closed of characteristic zero. Let $(L,x)$ be a finite cover whose fibre ring $B/J$ is reduced, and let $\tau$ and $\rho$ be a top coefficient and a residue functional. Then the set of fibre points is finite, and for every $h\in B$
$$
\operatorname{tr}_F\bigl(h\,\mathrm{vol}_0\bigr)=\rho\bigl(\operatorname{Tr}_{L/F}h\bigr)=\sum_{e}e(h),
$$
where the sum runs over all fibre points. In particular there are exactly $[L:F]$ fibre points.

The hypotheses are those of <code>trace_cechCochain_fraction_eq_sum_fibre</code>. Its conclusion is stated for $\operatorname{tr}_F$ of the component of <code>locCoch</code> $h$ on the intersection of all charts, which is $h\,\mathrm{vol}_0$. Separability and smoothness of the chart rings enter through <code>IsFinCover</code>. Nothing is assumed about $h$ beyond regularity on the whole origin chart. The last sentence is the case $h=1$, since $\rho(\operatorname{Tr}_{L/F}1)=\rho([L:F]\cdot1)=[L:F]$.

**Lemma 1 (top coefficient, overlaps and the origin chart) [Lean, read].** (a) For every $h\in L$, $\operatorname{tr}_F(h\,\mathrm{vol}_0)=\rho(\operatorname{Tr}_{L/F}h)$. (b) There is a $k$-algebra map $\mathrm{ev}:A\to k$ with $\rho(a)=\mathrm{ev}(a)$ for all $a\in A$ and $\ker\mathrm{ev}=\mathfrak p$.

*Proof.* (a) Since $\tau$ is $L$-linear, $\tau(h\,\mathrm{vol}_0)=h$. (b) Identify $A$ with $k[X_1,\ldots,X_d]$ by $X_j\mapsto t_j$. A monomial $t^n$ equals $\prod_jx_j^{m_j}$ with $m=(-n_1-\cdots-n_d,n_1,\ldots,n_d)$, whose entries sum to zero. For $n\ne0$ the residue condition gives $\rho(t^n)=0$, while $\rho(1)=1$. By linearity $\rho(f)=f(0)$ for every polynomial $f$. Evaluation at the origin is a $k$-algebra map, and its kernel consists of the polynomials without constant term, which form the ideal generated by the $X_j$. $\square$

The residue condition is homogeneous in the $x_j$, so it does not single out a chart. The same computation on $A_{\{i\}}$ shows that $\rho$ restricted to that chart ring is evaluation at the $i$th coordinate vertex. A cochain supported on the intersection of all charts is a top Čech cochain. For $\mathbb P^d$ itself the constant term is the class: under $\Omega^d_{\mathbb P^d}\cong\mathcal O(-d-1)$ the form $\mathrm{vol}_0$ corresponds, up to sign, to the monomial $1/(T_0\cdots T_d)$. The Laurent-monomial computation of [Stacks Project, Lemma 30.8.1](https://stacks.math.columbia.edu/tag/01XT) shows that this is the only monomial surviving in top Čech cohomology. So the class of $f\,\mathrm{vol}_0$, for a Laurent polynomial $f$, is the constant term of $f$ times the class of $\mathrm{vol}_0$. [Expository] A coefficient regular on the whole chart $D_+(x_0)$ has, by (b), residue equal to its value at the vertex of that chart, the only point of the chart outside all other charts. The third clause of <code>TrTop</code>, already read with the chart proof, shows that $\operatorname{tr}_F$ composed with the first-leg transfer kills the boundaries coming from the $d$-fold intersections. Thus the residue depends only on the class of the representative.

**Lemma 2 (no denominators) [Lean, read].** For $h\in B$ the field trace $\operatorname{Tr}_{L/F}h$ lies in $A$. It is the trace of multiplication by $h$ on the finite $A$-module $B$.

*Proof.* The ring $A$ is a polynomial ring, hence a unique factorization domain. It is therefore integrally closed, with fraction field $F$. The element $h$ is integral over $A$, hence so is $\operatorname{Tr}_{L/F}h$. Indeed the trace is an integer multiple of a coefficient of the minimal polynomial of $h$, and these coefficients are integral over $A$. An element of $F$ integral over $A$ lies in $A$. The second statement is the defining property of the trace of an integral closure: its image in $F$ is the field trace (Mathlib's <code>Algebra.algebraMap_intTrace</code>). $\square$

This is the classical argument behind [Stacks Project, Lemma 10.161.8](https://stacks.math.columbia.edu/tag/032L), which uses [Lemma 10.38.6](https://stacks.math.columbia.edu/tag/037E) for the minimal polynomial.

**Lemma 3 (localization at the origin) [Lean, read].** Let $R$ be an integrally closed domain. Let $S$ be an integrally closed domain which is a finite, torsion-free and projective $R$-module. Write $\operatorname{Tr}_{S/R}$ for the trace of the fraction fields restricted to $S$, which takes values in $R$ (Mathlib's <code>Algebra.intTrace</code>). For every maximal ideal $\mathfrak m\subset R$ and every $x\in S$,
$$
\operatorname{Tr}_{(S/\mathfrak mS)/(R/\mathfrak m)}(x\bmod\mathfrak mS)=\operatorname{Tr}_{S/R}(x)\bmod\mathfrak m .
$$

*Proof.* Localize at $\mathfrak m$. The module $S_{\mathfrak m}$ is finite over the local ring $R_{\mathfrak m}$. It is flat as a localization of a projective module, hence free. Choose a basis. The trace of multiplication by $x$ in this basis is the image of $\operatorname{Tr}_{S/R}(x)$, because the trace of an integral closure commutes with localization. Reducing the basis modulo the maximal ideal gives a basis of $S_{\mathfrak m}/\mathfrak mS_{\mathfrak m}$, in which multiplication by $x$ has the reduced matrix. Finally $R/\mathfrak m\to R_{\mathfrak m}/\mathfrak mR_{\mathfrak m}$ and $S/\mathfrak mS\to S_{\mathfrak m}/\mathfrak mS_{\mathfrak m}$ are isomorphisms compatible with the algebra structures, and traces correspond under such a pair. $\square$

The proof adapts Mathlib's version for Dedekind domains, where freeness of $S_{\mathfrak m}$ comes from $R_{\mathfrak m}$ being a principal ideal domain. For $d\ge2$ the ring $A_{\mathfrak p}$ is not principal, so this source of freeness is unavailable. The archive gets projectivity of $B$ over $A$ from smoothness (<code>integralClosure_projective_rA</code>). Both rings are regular, heights add along the integral extension by going down, so $B$ is flat over $A$ by the miracle flatness criterion. Being finitely presented, it is then projective ([Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4); [Lemma 10.78.2](https://stacks.math.columbia.edu/tag/00NX)).

**Lemma 4 (points of a reduced finite algebra) [Lean, read].** Let $O$ be a nonzero commutative ring and $H$ a finite free $O$-algebra. Let $\Omega$ be an algebraically closed field which is an $O$-algebra, and assume $\Omega\otimes_OH$ is reduced. Then the set $\operatorname{Hom}_O(H,\Omega)$ of $O$-algebra maps has exactly $\operatorname{rank}_OH$ elements, and for every $h\in H$
$$
\operatorname{Tr}_{H/O}(h)=\sum_{\varphi\in\operatorname{Hom}_O(H,\Omega)}\varphi(h)\qquad\text{in }\Omega .
$$

*Proof.* Over the perfect field $\Omega$ a reduced finite algebra is étale. Over an algebraically closed field it is then a product of $n=\operatorname{rank}_OH$ copies of $\Omega$. Maps $H\to\Omega$ over $O$ correspond to maps $\Omega\otimes_OH\to\Omega$ over $\Omega$, so there are exactly $n$ of them, $P_1,\ldots,P_n$. If $n=0$ then $H=0$ and both sides vanish. Otherwise choose a basis $e_1,\ldots,e_n$ of $H$, let $M_x$ be the matrix of multiplication by $x\in H$, and put $Q_{jl}=P_j(e_l)$. Applying $P_j$ to $xe_l=\sum_i(M_x)_{il}e_i$ gives
$$
Q\,M_x=\operatorname{diag}\bigl(P_1(x),\ldots,P_n(x)\bigr)\,Q .
$$
Distinct algebra maps are linearly independent over $\Omega$ (Dedekind), so $\det Q\ne0$. Hence $M_x$ is conjugate over $\Omega$ to the diagonal matrix. Its characteristic polynomial is $\prod_j(X-P_j(x))$, and the coefficient of $X^{n-1}$ gives the trace. $\square$

For a field $O=k$ the lemma also records residue degrees. A reduced finite $k$-algebra is a product of finite separable field extensions $\kappa(\mathfrak m)$ of $k$ (characteristic zero), one for each closed point $\mathfrak m$. The maps to $\Omega$ are grouped by closed point, with $[\kappa(\mathfrak m):k]$ maps over each, so the sum becomes $\sum_{\mathfrak m}\operatorname{Tr}_{\kappa(\mathfrak m)/k}(h\bmod\mathfrak m)$ ([Stacks Project, Lemma 9.13.4](https://stacks.math.columbia.edu/tag/0CKK)). The archive checks the smallest mixed case, $\mathbb R\times\mathbb C$ over $\mathbb R$, which has $3=1+2$ algebra maps to $\mathbb C$. When $k=\Omega$ every residue field is $k$, so geometric points, closed points and $k$-points coincide. [Expository]

**Lemma 5 (the fibre ring and its points) [Lean, read].** The fibre ring $B/J$ is a finite-dimensional $k$-algebra. Composition with $B\to B/J$ is a bijection from $\operatorname{Hom}_k(B/J,k)$ onto the set of fibre points.

*Proof.* The composite $A\to B\to B/J$ equals evaluation at the origin followed by $k\to B/J$, because each $t_j$ maps to zero. An element $b\in B$ satisfies a monic equation over $A$. Evaluating its coefficients at the origin gives a monic equation for $b\bmod J$ over $k$. So $B/J$ is integral and of finite type over $k$, hence finite. A fibre point vanishes on the generators of $J$ and so factors uniquely through $B/J$. Conversely every map $B/J\to k$ gives a fibre point. $\square$

If $B/J$ is reduced, an element of $B$ which vanishes at every fibre point lies in $J$ (<code>fib_finite_and_sep</code>). Since $k$ is algebraically closed, every maximal ideal of the Artinian ring $B/J$ is the kernel of a fibre point. So the class of the element lies in the Jacobson radical, which is nilpotent, and a nilpotent class in a reduced ring is zero.

*Proof of the theorem.* Let $h\in B$. By Lemma 1(a) the left side is $\rho(\operatorname{Tr}_{L/F}h)$. By Lemma 2 this trace is an element $a\in A$, the trace of $h$ on the projective $A$-module $B$. By Lemma 1(b), $\rho(a)=\mathrm{ev}(a)$. Apply Lemma 3 with $R=A$, $S=B$ and $\mathfrak m=\mathfrak p$. The ideal $\mathfrak pB$ is generated by the images of the $t_j$, so it is $J$. The isomorphism $A/\mathfrak p\cong k$ induced by $\mathrm{ev}$ is compatible with $k\to B/J$, because $y-\mathrm{ev}(y)\in\mathfrak p$ for every $y\in A$. This gives $\mathrm{ev}(a)=\operatorname{Tr}_{(B/J)/k}(h\bmod J)$. Now apply Lemma 4 with $O=\Omega=k$ and $H=B/J$, which is free over the field $k$ and reduced, with $k\otimes_kH\cong H$. The trace is the sum of $\varphi(h\bmod J)$ over $\operatorname{Hom}_k(B/J,k)$, and Lemma 5 turns this into the sum of $e(h)$ over the fibre points. $\square$

**Example (a non-split quadratic residue field) [Expository].** Work over $k=\mathbb R$, which is not algebraically closed. Take $d=1$, $F=\mathbb R(t)$ and $L=F(s)$ with $s^2=t-1$. Then $B=\mathbb R[s]$, free over $A=\mathbb R[t]$ with basis $1,s$. At infinity, $w=s/t$ and $u=1/t$ satisfy $w^2=u-u^2$, a smooth conic. The fibre ring is $\mathbb R[s]/(s^2+1)\cong\mathbb C$. It has one closed point, of residue degree $2$, and no real point. Let
$$
h=(2+s)^2-(s^2-t+1)=3+t+4s\in B,\qquad M_h=\begin{pmatrix}3+t&4(t-1)\\4&3+t\end{pmatrix}.
$$
Hence $\operatorname{Tr}_{L/F}h=6+2t$, with value $6$ at the origin. At $t=0$ the matrix $\begin{pmatrix}3&-4\\4&3\end{pmatrix}$ is multiplication by $3+4i$ on $\mathbb C$, and $\operatorname{Tr}_{\mathbb C/\mathbb R}(3+4i)=6$. The sum over real fibre points is empty, hence $0$. The two $\mathbb R$-algebra maps $\mathbb R[s]/(s^2+1)\to\mathbb C$, $s\mapsto\pm i$, give $(3+4i)+(3-4i)=6$. So the count must run over geometric points, and the closed point carries its residue degree, as in $\operatorname{Tr}(1)=2$. After base change to $\mathbb C$ the fibre ring becomes $\mathbb C\times\mathbb C$ with points $s=\pm i$, and the theorem applies as stated. The archive states the theorem over an algebraically closed $k$ and uses it with $k=\mathbb C$, where geometric points are $k$-points. Lemma 4 is stated over any base.

**Example (a non-reduced origin fibre) [Expository].** Keep the scaling correspondence, but use the auxiliary map
$$
t=\frac{z^2}{(1+z^2)^2}.
$$
Its zeros are $z=0$ and $z=\infty$, both double. Put $p=1/(1+z^2)$ and $q=z/(1+z^2)$. Then $p^2-p+t=0$ and $q^2=t$, so $B=\mathbb C[t][p,q]/(p^2-p+t,\,q^2-t)$ is free with basis $1,p,q,pq$ and $[\mathbb C(z):\mathbb C(t)]=4$. Both chart rings are smooth: on the origin chart $B$ is the conic $q^2=p-p^2$, and the other chart has ring $\mathbb C[z,z^{-1}]$. So the data form a finite cover. The fibre ring $\mathbb C[p]/(p^2-p)\otimes\mathbb C[q]/(q^2)$ has two points, $p=1$ at $z=0$ and $p=0$ at $z=\infty$, and each local ring has length $2$. For $h_a=L_a(\infty)+(L_a(0)-L_a(\infty))p$, we have $\operatorname{Tr}(p)=2$ and $\operatorname{Tr}(1)=4$, so
$$
\operatorname{Tr}_{B/A}(h_a)=2L_a(0)+2L_a(\infty),
$$
which is $2$ for $a=0$ and $-2$ for $a=1$. The sum of the values at the two fibre points is $1$ or $-1$. Here the trace is the sum of the values weighted by the lengths of the local rings, and the pointwise sum is half of it. The element $q$ is a nonzero nilpotent of the fibre ring that vanishes at both points.

Over an algebraically closed field every finite algebra splits into local rings $H_{\mathfrak m}$ with residue field $k$. On $H_{\mathfrak m}$, multiplication by $h$ is $h(\mathfrak m)$ plus a nilpotent, so $\operatorname{Tr}(h)=\sum_{\mathfrak m}\operatorname{length}(H_{\mathfrak m})\,h(\mathfrak m)$. This multiplicity formula is elementary exposition and is not part of the archive. It does not enlarge the domain of the present argument. In the chart proof, reducedness of the origin fibre also makes the $t_j$ local parameters at each fixed point. The local Koszul comparison uses this, and so do <code>LocMax</code>, <code>LocForms</code> and <code>LocReg</code>, which all assume <code>RedFib</code>. At a ramified point the $t_j$ no longer generate the maximal ideal and the local coefficient changes. With the unchanged coefficients, the length-weighted sum gives twice the Lefschetz number in this example. The archive instead chooses an auxiliary projection whose origin fibre is reduced (<code>exists_finiteCover_projSpace_reduced_fibre_origin</code>, [Lean, read]; see the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre)).

**Remark (the actual call: one leg, raw trace and normalization) [Lean, read].** The wrapper <code>deRham_restriction_trace_degree_one</code> chooses a top coefficient for $L$ and uses Lemma 1(a) to restate the theorem without $\tau$, as $\rho(\operatorname{Tr}_{L/F}h)=\sum_ee(h)$. This is the interface <code>ResidueOfTraceIsFiberSum</code>. In <code>fieldLe_of</code> the top coefficient is chosen for the target field $K$ and the residue functional on $F$. The coefficient $h$ comes from <code>YMain</code>. Its producer obtains $h$ from <code>CRT</code>, with value $L_a(e)$ at each fixed evaluation $e\in F_x$ and $0$ at the other fibre points, and records $\sum_ee(h)=\sum_{e\in F_x}L_a(e)$. The third clause of <code>TrTop</code> kills the transferred boundary between the cup cocycle $\Lambda$ and <code>locCoch</code> $h$. The second clause then evaluates the transferred top form. The form trace along the first leg satisfies $\operatorname{tr}_{K'/K}(h\,\mathrm{vol}_0)=(\operatorname{Tr}_{K'/K}h)\,\mathrm{vol}_0$, because $\mathrm{vol}_0$ on $K'$ is the image of $\mathrm{vol}_0$ on $K$. Together with $\operatorname{Tr}_{K'/F}=\operatorname{Tr}_{K/F}\circ\operatorname{Tr}_{K'/K}$ this gives $\rho(\operatorname{Tr}_{K'/F}h)$. The theorem with $L=K'$ turns this into $\sum_ee(h)$, and the interpolation identity into $\sum_{e\in F_x}L_a(e)$. The first leg thus supplies both the transfer and the fibre. The second leg enters only through the set of fixed evaluations. No factor $[K':F]$ or $[K':K]$ appears, because the transfer is the raw one and each sheet is counted once. This is the convention of the [holomorphic trace formula](#the-holomorphic-lefschetz-input-to-the-odd-rank-seed), where $\operatorname{Tr}_{c_1}(1)$ is the local degree. The Hecke normalization comes afterwards. <code>geoStep_of</code> writes the normalized operator as the inverse relative level index times the raw composite of transfer and pullback. It applies the raw formula in each form degree, sums against $(-y)^a$, and cancels the index with the identity supplied by <code>FixK</code>.

**Remark (what each hypothesis pays for) [Expository].**

- *Regularity on the whole chart.* In the first example, $h=1/(v+1)$ is regular at both fibre points, with values $1$ and $1/2$. But $h\notin B$, since it has a pole at $v=-1$, where $t=-2$. Its trace is $3/(2+t)$, which is not a Laurent polynomial. The expansion at $t=0$ has constant term $3/2$, the fibre sum, while the expansion in $1/t$ has constant term $0$. A residue functional is unconstrained on such elements, so Lemma 2 is what makes the answer independent of the choice of $\rho$.
- *Projectivity.* Let $A=k[a^4,b^4]$ and let $B=k[a^4,a^3b,ab^3,b^4]$, the affine cone over the rational quartic curve in $\mathbb P^3$ and a standard non-Cohen–Macaulay domain. Its generic rank over $A$ is $4$. Its fibre ring at the origin has dimension $5$, with monomial basis $1,a^3b,ab^3,a^6b^2,a^2b^6$, so reduction at the origin cannot commute with the trace of $1$. The normalization adds $a^2b^2$ and restores dimension $4$. The integral closures of the archive are normal, and smoothness makes them flat in every dimension.
- *Reducedness.* This is the non-reduced example. Without it the trace counts lengths, and the local comparison of the chart proof is no longer available.
- *Algebraically closed $k$.* This is the non-split example. Over a smaller field a closed point counts with its residue degree, through its geometric points.

All calculations in this subsection are checked by exact arithmetic in the run's <code>check_fibre_trace.py</code>.

**Reading the formal proof.** Paths are relative to the root of archive A2 (Lean 4.33.1, joined SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>, Mathlib pinned at <code>0df444a360eaa60ab8c11dca51a86af692955474</code>).

| Node | A2 path and lines | Role and reading |
|---|---|---|
| <code>trace_cechCochain_fraction_eq_sum_fibre</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TraceCechCochainFractionEqSumFibreStatement.lean:9–10</code> | Exported statement and delegation. R3 [Lean, read]. |
| <code>GlobalTheory.PD.trF_locCoch_eq_finsum_fib</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TraceCechCochainFractionEqSumFibre.lean:19–33</code> | Direct producer and proof of the theorem: Lemma 1(a), Lemma 2 and the chain of three rewrites. R3 [Lean, read]. |
| <code>TraceOrigin.ev_eq_trace_quot</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TraceEvalOriginEqFibreTrace.lean:19–73</code> | Integral closure as finite projective module, $A/\mathfrak p\cong k$, $\mathfrak pB=J$, transport of the trace. R3 [Lean, read]. |
| <code>trace_quotient_eq_of_projective</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TraceQuotientEqOfProjective.lean:9–47</code> | Lemma 3. R3 [Lean, read]; Mathlib quotient and localization lemmas at statement level. |
| <code>integralClosure_projective_rA</code> | <code>src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralClosureProjectiveOverStandardOpenRing.lean:13–45</code> | Projectivity by regularity, going down and miracle flatness. R3 for the body; regularity of smooth algebras and local miracle flatness [Lean]. |
| <code>FibTrace.trace_quot_eq_finsum_fib</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TraceFibreRingEqFinsumFibrePoints.lean:14–44</code> | Lemma 4 for $H=B/J$ and the bijection of Lemma 5. R3 [Lean, read]. |
| <code>FibFin.mk_incl</code>, <code>finite_quot</code>, <code>fib_finite_and_sep</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FibFiniteAndSep.lean:17–111</code> | Lemma 5 and the separation statement. R3 [Lean, read]. |
| <code>finite_card_trace_algHom_of_isReduced_baseChange</code> | <code>src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CardAlgHomReducedTraceSum.lean:8–35</code> | Lemma 4, including the empty case. R3 [Lean, read]. |
| Point count and diagonalization | <code>src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean:82–143,177–183,196–222,354–357</code> | $Q\,M_x=\operatorname{diag}(P_j(x))\,Q$, characteristic polynomial, étaleness of reduced algebras, the count, and the $\mathbb R\times\mathbb C$ example. R3 [Lean, read]; Mathlib étale and Dedekind lemmas at statement level. |
| <code>ResEv.ker_aeval_zero</code>, <code>res_aeval</code>, <code>chart0</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LaurentConstantTermEqEvalOriginChart.lean:14–90</code> | Lemma 1(b). R3 [Lean, read]. |
| <code>exists_isRes</code> | <code>src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLaurentConstantTermFormFunctionField.lean:80–121</code> | Construction of $\rho$ used for the non-uniqueness remark. R3 for the body; independence of Laurent monomials [Lean]. |
| Definitions | <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/DlogRatioVolumeFormNeZero.lean:17–30,74–91</code>, <code>src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/TcoMem.lean:15–25</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/ResidueOfTraceIsFiberSum.lean:17–19,91–93</code> | <code>IsPd</code>, <code>rA</code>, <code>IsRes</code>, <code>rB</code>, <code>IsFinCover</code>, <code>vol0</code>, <code>IsTop</code>, <code>trF</code>, <code>fib</code>, <code>locCoch</code>, <code>RedFib</code> and the consumed interface. |
| Actual call | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PFieldLe.lean:216–336</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PTrTop.lean:11–70</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYMain.lean:111–123</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/DeRhamRestrictionTraceDegreeOne.lean:8–16</code>, <code>src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/ExistsChartLiftOfFiniteCover.lean:161</code> | Lines 318–323 of <code>fieldLe_of</code> combine <code>TrTop</code>, the theorem and <code>YMain</code>. Prior R3, rechecked. |
| Normalization | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LefschetzSigmaSums/PGeoStep.lean:16–85</code> | Raw formula, inverse relative level index and <code>FixK</code> cancellation. Prior R3, rechecked. |

R3 covers the named bodies. The polynomial-chart isomorphism <code>rA_single_polyEquiv</code> and its <code>Model.chartEquiv</code>, the fraction-field statement, finiteness and smoothness of the chart closures (<code>finite_cover_chart_smooth_normal</code>), <code>isRegularRing_of_smooth</code>, the local miracle-flatness lemma behind <code>flat_of_isRegularRing_of_isRegularRing</code>, the existence of $\tau$, <code>CRT</code> and the Mathlib library lemmas are used at their interfaces. The reduced-fibre projective chart is read in the [next subsection](#from-a-general-projection-to-a-reduced-origin-fibre). The [global boundary](#from-fixed-point-vanishing-to-a-global-čech-boundary) and the [local Koszul weights](#from-a-finite-étale-chart-to-the-local-lefschetz-weight) keep the reading levels recorded there. The geometry of <code>FixK_holds</code>, the group-side matching <code>MarkWeightedFixedPointEqDefinitePairOdd</code> and <code>TraceDefinitePairsEqAutomorphicTrace</code>, and the naturality of the Hodge–Čech comparison retain their [Lean] / [Open] status.

#### From a general projection to a reduced origin fibre

The [reduced-fibre trace](#from-the-finite-algebra-trace-to-the-reduced-fibre) took three facts about the auxiliary coordinates as given. The coordinates form a finite cover (<code>IsFinCover</code>). The origin fibre ring is reduced (<code>RedFib</code>). The coincidences of the correspondence lie over the origin. This subsection proves that such coordinates exist on every smooth projective variety over $\mathbb C$, for any prescribed finite set of points. The statement is <code>exists_finiteCover_projSpace_reduced_fibre_origin</code>. Its direct producer is <code>FibRed.exists_finCover_fibre_reduced</code>, and the germ-quotient lemma <code>FibRed.quotEquiv_of_germ</code> serves as the bridge inside the proof. We then follow the result into the chart proof, where it becomes the hypothesis <code>RedFib</code> for the source function field.

**Motivation.** The three requirements pull against each other.

- *Finiteness* concerns all of $X$: the $d+1$ forms that define the map to $\mathbb P^d$ must have no common zero.
- *Placing a finite set $S$ over the origin* is a closed condition at finitely many points: the last $d$ forms must vanish on $S$.
- *Reducedness* concerns the whole origin fibre. That includes points imposed by the first two choices, about which nothing is known in advance.

The [non-reduced example](#from-the-finite-algebra-trace-to-the-reduced-fibre) of the preceding subsection shows what is at stake. If the auxiliary map is ramified over the origin, the trace counts lengths and the local comparison of the chart proof is unavailable. The obvious repair translates the target coordinate until the origin is no longer a branch value. That repair fails, because it moves $S$ off the origin. The archive keeps $S$ fixed and translates instead by a form that vanishes to second order on $S$. Such a translation moves only the other fibre points, and Sard's theorem shows that almost every translation parameter moves them off the branch locus. The two examples below show both effects on one plane cubic.

**Example (a legal finite projection of a smooth cubic) [Expository].** Let $E\subset\mathbb P^2$ be the cubic $y^2z=x^3-xz^2$. Its partial derivatives $-3x^2+z^2$, $2yz$ and $y^2+2xz$ have no common zero on $E$, so $E$ is smooth of dimension $d=1$. Take $S=\{P_0\}$ with $P_0=(0:0:1)$, and consider the linear forms
$$
f_0=z,\qquad g=y,\qquad h=x,\qquad F_c=g+c\,h=y+cx\qquad(c\in\mathbb C).
$$
On the chart $z\ne0$ use affine coordinates $x,y$. Then $E$ is $y^2=x^3-x$, and the auxiliary coordinate is $t=F_c/f_0=y+cx$.

- *Jets at $S$.* The equation gives $x=x^3-y^2$. So $x$ lies in $\mathfrak m_{P_0}^2$, where $\mathfrak m_{P_0}=(x,y)$, and $\mathfrak m_{P_0}\subset(y)+\mathfrak m_{P_0}^2$. Thus $h$ vanishes to second order at $P_0$, and $g$ has a full first-order jet there: it generates the cotangent line. The common zeros of $g$ and $h$ on $E$ reduce to $P_0$. Since $h$ vanishes to second order, every $F_c$ has the same first-order jet $y$ at $P_0$.
- *No common zero, hence a finite map.* If $z=0$ on $E$ then $x^3=0$, so the point is $O=(0:1:0)$, where $F_c=1$. The opens $U_0=E\cap\{z\ne0\}$ and $U_1=E\cap\{F_c\ne0\}$ therefore cover $E$, and $(f_0:F_c)$ is a morphism $E\to\mathbb P^1$.
- *The origin chart.* Substituting $y=t-cx$ into $y^2=x^3-x$ gives
  $$
  x^3-c^2x^2+(2ct-1)x-t^2=0,
  $$
  a monic cubic in $x$ over $\mathbb C[t]$. Hence $\Gamma(U_0,\mathcal O)=\mathbb C[t][x]/(\text{cubic})$ is free over $A=\mathbb C[t]$ with basis $1,x,x^2$. The extension $\mathbb C(E)/\mathbb C(t)$ has degree $3$, the number of intersections of $E$ with a line.
- *The chart at infinity.* On $F_c\ne0$ use the coordinates $x/F_c$ and $u=z/F_c=1/t$. Write $x$ again for $x/F_c$. The equation becomes $-x^3+c^2ux^2+(u^2-2cu)x+u=0$, which is monic in $x$ up to sign, so the chart ring is free of rank $3$ over $\mathbb C[u]$. At $u=0$ it reduces to $x^3=0$. The fibre over $t=\infty$ is the flex $O$, counted three times. Only the origin fibre has to be reduced, so this does no harm.
- *The origin fibre.* At $t=0$ the cubic becomes $x\,(x^2-c^2x-1)$. The root $x=0$ is $P_0$, which lies on every member of the family. The quadratic factor has discriminant $c^4+4$ and does not vanish at $x=0$. So for $c^4\neq-4$ the fibre ring is
  $$
  B_0/(t)=\mathbb C[x]/\bigl(x(x^2-c^2x-1)\bigr)\cong\mathbb C\times\mathbb C\times\mathbb C .
  $$
  It is reduced with three points. For $c=0$ they are the three points of order two, $x=0,\pm1$ with $y=0$.
- *Transversality.* At each fibre point $q$ the archive checks the condition $\mathfrak m_q\subset(t)+\mathfrak m_q^2$, which says that $t$ generates the cotangent line at $q$. At $P_0$ this is the jet computation above. For $c=0$, at $q=(1,0)$ we have $(x-1)\,x(x+1)=y^2$ and $x(x+1)=2+(x-1)(x+2)$. Hence $2(x-1)=y^2-(x-1)^2(x+2)\in(y)+\mathfrak m_q^2$, and the point $(-1,0)$ is symmetric.
- *Germs and integrality.* The ring $B_0=\Gamma(U_0,\mathcal O)$ is the coordinate ring of a smooth affine curve, hence normal, and it is integral over $\mathbb C[t]$. So it is the integral closure of $\mathbb C[t]$ in $\mathbb C(E)$. Equivalently, the integral elements of $\mathbb C(E)$ are exactly the germs of regular functions on $U_0$. A function with a pole on $U_0$ illustrates both directions. At $c=0$ put $w=y/x$, which has a pole at $P_0$: there $y$ is a local parameter and $x$ vanishes to order two. With $t=y$ one checks $w^3+w^2/t-t=y\,(y^2-x^3+x)/x^3=0$. This is the minimal polynomial of $w$ over $\mathbb C(t)$. Indeed $x^3-x-t^2$ has no root in $\mathbb C(t)$, because a root would be a polynomial of degree $2/3$; so $x\notin\mathbb C(t)$, hence $w\notin\mathbb C(t)$, and the extension has degree $3$. The coefficient $1/t$ is not a polynomial, so $w$ is not integral over $\mathbb C[t]$.

This is the archive's construction in miniature. The form $g$ has full jets on $S$, the form $h$ vanishes doubly on $S$, the base locus of $g$ and $h$ is $S$, the translation is $F_c=g+ch$, and $f_0$ vanishes nowhere on the origin fibre.

**Example (a branch value at the origin) [Expository].** Keep $E$, $S$ and $f_0$, and take $c=1+i$, one of the four roots of $c^4=-4$. The quadratic factor becomes $x^2-2ix-1=(x-i)^2$, so
$$
B_0/(t)\cong\mathbb C[x]/\bigl(x(x-i)^2\bigr)\cong\mathbb C\times\mathbb C[\varepsilon]/(\varepsilon^2).
$$
The second factor sits at $Q=(i,1-i)$, where the line $y+(1+i)x=0$ is tangent to $E$. Indeed the gradient $(-3x^2+1,\,2y)$ of $y^2-x^3+x$ at $Q$ is $(4,\,2-2i)=(2-2i)\,(1+i,\,1)$. The class of $x(x-i)$ is a nonzero nilpotent. In terms of the criterion used below, $\mathfrak m_Q\not\subset(t)+\mathfrak m_Q^2$: the image of $\mathfrak m_Q$ in the fibre ring is the ideal $(x-i)$, and it is not idempotent. The [reduced-fibre trace](#from-the-finite-algebra-trace-to-the-reduced-fibre) would weight $Q$ by $2$.

There are two ways to move the branch value away from the origin, and they behave differently.

- *Translating the target coordinate.* Replacing $t$ by $t-a$, that is $F_c$ by $F_c-af_0$, makes the new origin fibre the old fibre over $a$. For $a$ outside the finitely many branch values of $t$ that fibre is reduced. But $t(P_0)=0\ne a$, so $P_0$ leaves the origin fibre, and the coincidence that $S$ was meant to record is lost.
- *Translating inside the family.* Replacing $c$ by $c'$ adds $(c'-c)h$ to $F_c$. Since $h=x$ vanishes to second order at $P_0$, every member passes through $P_0$ with the same first-order jet $y$. Only the two other points move. They are the residual intersections of $E$ with the line through $P_0$ of slope $-c'$, so they form the fibre over $-c'$ of the projection $\pi=y/x$ from $P_0$. This projection is a map $E\to\mathbb P^1$ of degree two. By Riemann–Hurwitz it has exactly four branch values, the slopes $-c$ with $c^4=-4$. Every other $c'$ gives a reduced origin fibre.

In the proof below the second mechanism appears in general. The exceptional parameters are the negatives of the critical values of $g/h$. Sard's theorem says that this set has measure zero; here it consists of four points.

Suppose instead that $g$ had a double zero on $S$, for instance $g=x$. Then every $g+ch$ would have one as well, and no choice of $c$ would help. This is why the archive requires full first-order jets of $g$ on $S$, and that uses the smoothness of $X$ at the points of $S$. The ramified auxiliary map $t=z^2/(1+z^2)^2$ of the preceding subsection fails in exactly this way. In homogeneous coordinates it is $z_0^2z_1^2/(z_0^2+z_1^2)^2$, and the numerator vanishes doubly at both points of $S=\{0,\infty\}$. The split map $t=z/(1+z)^2=z_0z_1/(z_0+z_1)^2$ of that subsection has full jets on $S$ and no common zero of numerator and denominator.

All calculations in the two examples are checked by exact arithmetic in the run's <code>check_reduced_projection.py</code>.

**Definitions.**

- *Projective presentation.* $X$ is an integral scheme with a closed immersion $\iota:X\to\mathbb P^N_{\mathbb C}$ over $\mathbb C$ (<code>IsProjOver</code>). For a homogeneous polynomial $f$ of degree $n$ write $D(f)=\iota^{-1}D_+(f)$ (<code>fOpen</code>). For forms $f,g$ of the same degree the ratio $f/g$ is a regular function on $D(g)$ (<code>fRatio</code>), and $g/g=1$ (<code>fRatio_self</code>).
- *Complex points.* A complex point is a $\mathbb C$-morphism $\operatorname{Spec}\mathbb C\to X$ (<code>CxPts</code>). For an open $U$ containing $y$, evaluation of sections is a ring map $\mathrm{ev}_y:\Gamma(X,U)\to\mathbb C$ (<code>CxPts.evHom</code>), whose kernel $\mathfrak m_y$ is a maximal ideal.
- *Transversal zero.* Sections $\varphi_1,\ldots,\varphi_k\in\Gamma(X,U)$ have a *transversal common zero* at $y$ if every $\varphi_j(y)=0$ and $\mathfrak m_y\subset(\varphi_1,\ldots,\varphi_k)+\mathfrak m_y^2$. Equivalently, their classes span the cotangent space $\mathfrak m_y/\mathfrak m_y^2$. If $X$ is smooth of dimension $d$, this space has dimension $d$ ([Stacks Project, Lemmas 10.140.1 and 10.140.3](https://stacks.math.columbia.edu/tag/00TQ)). Then $d$ sections with a transversal common zero at $y$ form a regular system of parameters there.
- *Affine chart cover.* Given forms $f_0,\ldots,f_d$, put $U_i=D(f_i)$ and $U_I=\bigcap_{i\in I}U_i$. Let $K=\mathbb C(X)$, with the $\mathbb C$-structure coming from $X\to\operatorname{Spec}\mathbb C$ (<code>ffAlg</code>). The cover is an *affine cover* for subalgebras $B_I\subset K$ (<code>IsAffCover</code>) if four things hold: the $U_i$ cover $X$; each $U_I$ with $I\ne\varnothing$ is affine; each $U_I$ contains the generic point; and $B_I$ is exactly the set of germs at the generic point of sections over $U_I$.
- With $x_i=f_i/f_0\in K$ and $t_j=x_j$ for $1\le j\le d$, we use the definitions of the [preceding subsection](#from-the-finite-algebra-trace-to-the-reduced-fibre): finite cover, chart rings $A_I\subset B_I$, $\mathfrak p$, $J=\mathfrak pB_0$ and <code>RedFib</code>.

**Theorem (a reduced auxiliary projection) [Lean, read].** Let $X$ be an integral scheme, smooth of relative dimension $d$ and projective over $\mathbb C$, and let $S$ be a finite set of complex points of $X$. Then there exist an integer $n\ge1$ and forms $f_0,\ldots,f_d$ of degree $n$ with the following properties. Put $x_i=f_i/f_0\in K$, let $F=\mathbb C(x_1,\ldots,x_d)\subset K$, and let $U_i=D(f_i)$.

1. The tuple $(x_0,\ldots,x_d)$ is a finite cover of $K$ over $F$, and $(U_i)$ is an affine cover for the integral closures $B_I$. In particular, taking germs gives $\Gamma(X,U_0)\cong B_0$.
2. Every $y\in S$ lies in $U_0$. If a section of $U_0$ has germ $x_j$ for some $1\le j\le d$, it vanishes at $y$.
3. The origin fibre ring $B_0/J$ is reduced.

Moreover, taking germs at the generic point induces a ring isomorphism $\Gamma(X,U_0)/(t_1,\ldots,t_d)\cong B_0/J$.

These are the hypotheses of <code>exists_finiteCover_projSpace_reduced_fibre_origin</code>, and items (1)–(3) are its four conclusions: the finite cover, the affine cover, the reduced fibre and the placement of $S$. The isomorphism in the last sentence is <code>FibRed.quotEquiv_of_germ</code>, used inside the proof; it is not exported. The theorem depends on the named inputs listed at the end of this subsection, which are used at their interfaces.

**Lemma 1 (finite projection by forms without common zero) [Lean, read].** Let $f_0,\ldots,f_d$ be forms of the same degree $n\ge1$ with no common zero on $X$, none vanishing at the generic point. Then the ratios $f_j/f_i$ on $D(f_i)$ glue to a finite morphism $\varphi:X\to\mathbb P^d$ with $\varphi^{-1}(D_+(T_i))=D(f_i)$. Consequently $x_i=f_i/f_0$ is a finite cover, and $(D(f_i))$ is an affine cover for the integral closures $B_I$.

*Proof.* The ratios satisfy $f_i/f_i=1$. On $D(f_i)\cap D(f_j)$ they satisfy the cocycle rule $(f_j/f_i)(f_k/f_j)=f_k/f_i$, and the nonvanishing locus of $f_j/f_i$ on $D(f_i)$ lies in $D(f_j)$. These are the axioms of a coordinate family (<code>isCoordFamily_fRatio</code>). The family defines $\varphi$ over $\mathbb C$, with the stated preimages of the standard charts (<code>formMap</code>, <code>formMap_preimage</code>).

The morphism $\varphi$ is affine. Because $f_i$ is homogeneous of positive degree, $D_+(f_i)$ is affine, and its preimage under the closed immersion $\iota$ is affine as well. The morphism $\varphi$ is also proper. Indeed $X\to\operatorname{Spec}\mathbb C$ is proper, being $\iota$ followed by the proper structure map of $\mathbb P^N$. Since $\mathbb P^d$ is separated, the first factor of $X\to\mathbb P^d\to\operatorname{Spec}\mathbb C$ is then proper. A morphism that is affine and proper is finite ([Stacks Project, Lemma 29.45.11](https://stacks.math.columbia.edu/tag/01WN)). <code>isFinite_formMap</code> concludes in exactly this way, through Mathlib's <code>IsFinite.iff_isProper_and_isAffineHom</code>.

The chart data come from <code>exists_finCover_of_isFinite</code>. Let $x_i$ be the pulled-back coordinate ratios. They agree with the germs of $f_i/f_0$ (<code>rat_formMap</code>), and $x_0=1$. Three named inputs about finite maps to $\mathbb P^d$ say that the ratios are nonzero at the generic point, that they are algebraically independent, and that $K$ is finite over the subfield $F$ they generate. Separability of $K/F$ is automatic in characteristic zero (<code>IsFinCover.of_charZero</code>). The chart preimages cover $X$, and their finite intersections are affine (<code>projective_chart_affine_cover</code>). The germ of a section over $U_I$ is integral over $A_I$ (<code>genericGerm_chartInter_integral_coordinateRatios</code>); classically this is the finiteness of $\varphi$ over the affine chart. Conversely, an element of $K$ integral over $A_I$ is the germ of a section over $U_I$ (<code>chart_function_field_integral</code>); classically this holds because $U_I$ is smooth, hence normal. So $B_I$ is the set of germs of sections over $U_I$. In particular $B_{\{i\}}$, the coordinate ring of the smooth affine $U_i$, is smooth over $\mathbb C$ (<code>affine_germ_subalgebra_smooth</code>). $\square$

**Lemma 2 (transversal forms through $S$) [Lean, read].** There exist $n\ge1$ and forms $f_0,F_1,\ldots,F_d$ of degree $n$ with three properties.

- (i) They have no common zero on $X$, and none vanishes at the generic point.
- (ii) Every $y\in S$ lies in $D(f_0)$, and all $F_j/f_0$ vanish at $y$.
- (iii) If all $F_j/f_0$ vanish at a complex point $y\in D(f_0)$, then $y$ is a transversal common zero of $F_1/f_0,\ldots,F_d/f_0$.

*Proof.* This is <code>exists_transversal_forms_first_separate</code>. <code>exists_forms_transversal</code> merely reindexes $(f_0,F)$ as a single family indexed by $0,\ldots,d$.

1. *Jets on $S$.* Choose $n\ge1$ and forms $h,g_1,\ldots,g_d$ of degree $n$ with four properties (<code>EtProj.Jets.exists_jet_forms</code>, [Lean, read]; see the [jet forms](#forms-with-prescribed-jets-at-finitely-many-points)):
   - no $g_j$ vanishes at the generic point;
   - every $g_j$ vanishes on $S$;
   - the common zeros of $h,g_1,\ldots,g_d$ on $X$ lie in $S$;
   - for every $y\in S$ and every form $f$ of degree $n$ with $f(y)\neq0$, we have $h/f\in\mathfrak m_y^2$, and $g_1/f,\ldots,g_d/f$ span $\mathfrak m_y/\mathfrak m_y^2$.
2. *Sard.* The open $D(h)$ is affine. There is a set $E\subset\mathbb C^d$ of Lebesgue measure zero such that for $c\notin E$, every common zero in $D(h)$ of the functions $g_j/h+c_j$ is transversal (<code>AlgSard.main</code>, [Lean, read]; see the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets)). Classically this is Sard's theorem for the holomorphic map $\gamma=(g_j/h)_j$ from $D(h)(\mathbb C)$ to $\mathbb C^d$; the archive's own proof of this step, through countably many holomorphic charts, is read in the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets). The common zeros of $g/h+c$ are the points of $\gamma^{-1}(-c)$. They are all transversal unless $-c$ is a critical value, and the critical values of $\gamma$ form a null set ([Sard 1942, p. 883](https://doi.org/10.1090/S0002-9904-1942-07811-6)). In the second example the parameters to avoid are the four $c$ with $c^4=-4$.
3. *Members that vanish identically.* For each $j$ at most one $c\in\mathbb C$ makes $g_j+ch$ vanish at the generic point. If two values $c\ne c'$ did, their difference would show that $(c-c')h$, hence $h$, and then $g_j$ vanish there, which step 1 excludes. Call this value $a_j$; the proof takes $a_j=0$ when there is none. Thus the archive also avoids $c_j=0$, even where that value would be harmless, as $c=0$ is in the first example.
4. *Choice of $c$.* The union of $E$ with the $d$ hyperplanes $\{c_j=a_j\}$ has measure zero, while $\mathbb C^d$ has positive measure, so some $c$ avoids it. Put $F_j=g_j+c_jh$. On $D(h)$ we have $F_j/h=g_j/h+c_j$. So at every complex point of $D(h)$ where all $F_j$ vanish, the $F_j/h$ have a transversal common zero.
5. *Finitely many transversal zeros.* In the affine open $D(h)$, the transversal common zeros of $F_1/h,\ldots,F_d/h$ form a finite set $T$ (<code>TransvZeros.finite_transv_zeros</code>, [Lean, read]; see [why the transversal zeros are finite](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes)). Each of them is an isolated point of the zero scheme: by Nakayama's lemma its maximal ideal is a minimal prime over $(F_1/h,\ldots,F_d/h)$, and a Noetherian ring has only finitely many minimal primes over an ideal.
6. *The denominator.* Choose a form $f_0$ of degree $n$ that vanishes neither at the generic point nor at any point of $S\cup T$ (<code>EtProj.exists_form_genericPoint_cxPts</code>, [Lean, read]). The [denominator and open-cover proof](#choosing-the-denominator-and-detecting-the-open-cover) gives the finite avoidance argument over $\mathbb C$.

Now we verify (i)–(iii).

*Property (i).* Let $z$ be a complex point at which $f_0$ and all $F_j$ vanish. If $z\in D(h)$, then $z\in T$ by step 4, which contradicts the choice of $f_0$. If $h(z)=0$, then $g_j(z)=F_j(z)-c_jh(z)=0$ for all $j$, so $z\in S$ by step 1, again a contradiction. Hence the open set $D(f_0)\cup\bigcup_jD(F_j)$ contains every complex point. For a scheme locally of finite type over $\mathbb C$, this pointwise test implies that the open set is the whole scheme (<code>MaxPt.eq_top_of_forall_cxPts_mem</code>, [Lean, read], [denominator and open-cover proof](#choosing-the-denominator-and-detecting-the-open-cover)). The generic point lies in each $D(F_j)$ because $c_j\ne a_j$.

*Property (ii).* Let $y\in S$. Then $f_0(y)\ne0$, and $h/f_0\in\mathfrak m_y^2$ gives $h(y)=0$. Since also $g_j(y)=0$, we get $F_j(y)=0$.

*Property (iii).* Let $z\in D(f_0)$ be a complex point at which all $F_j/f_0$ vanish. If $z\in S$, step 1 says that the $g_j/f_0$ span the cotangent space. Since $F_j/f_0=g_j/f_0+c_j\,h/f_0$ and $h/f_0\in\mathfrak m_z^2$, the $F_j/f_0$ span it as well. If $z\notin S$, then $h(z)\ne0$, since otherwise $z\in S$ as in (i). So $z\in D(h)$, and by step 4 the $F_j/h$ have a transversal zero at $z$. The ratio $h/f_0$ is a unit near $z$ and $F_j/f_0=(F_j/h)(h/f_0)$, so the $F_j/f_0$ have a transversal zero at $z$ as well (<code>GlobalTheory.T.ratio_span_cotangent_change_denominator</code> at line 226, [Lean, read]). The [change of denominator](#changing-the-denominator-in-cotangent-generation) proves the required containment in the section ring. $\square$

**Lemma 3 (the germ quotient) [Lean, read].** Let $U$ be an open set containing the generic point. Let $t_1,\ldots,t_d\in\Gamma(X,U)$ be sections whose germs are $x_1,\ldots,x_d$, where $x_0=1$, and suppose $B_0$ is exactly the set of germs of sections over $U$. Then taking germs induces a ring isomorphism $\Gamma(X,U)/(t_1,\ldots,t_d)\cong B_0/J$.

*Proof.* Because $X$ is integral, the germ map $\Gamma(X,U)\to K$ is injective (Mathlib's <code>germ_injective_of_isIntegral</code>). By hypothesis its image is $B_0$, so it is a ring isomorphism $\Gamma(X,U)\cong B_0$. It sends $t_j$ to $x_j/x_0$, hence the ideal $(t_1,\ldots,t_d)$ onto $J$. So it induces an isomorphism of the quotients (<code>Ideal.quotientEquiv</code>). $\square$

The two directions of the hypothesis "$B_0$ is the set of germs" are separate facts. That sections are integral over $A$ needs the finiteness of the projection; that integral elements are sections needs normality. The function $w=y/x$ of the first example lies in $K$ and is regular on $U_0\setminus\{P_0\}$. It is neither integral over $\mathbb C[t]$ nor a section over $U_0$.

**Lemma 4 (reducedness from transversality) [Lean, read].** Let $A$ be a ring and $I\subset A$ an ideal such that $A/I$ is Artinian. If $\mathfrak m\subset I+\mathfrak m^2$ for every maximal ideal $\mathfrak m\supset I$, then $A/I$ is reduced.

*Proof.* Put $R=A/I$. Every maximal ideal $M$ of $R$ is the image of a maximal ideal $\mathfrak m\supset I$, and the hypothesis maps to $M\subset M^2$. Hence $M^k=M$ for all $k\ge1$. The ring $R$ has finitely many maximal ideals. They are pairwise coprime, so their product $P$ equals their intersection, which is the Jacobson radical. Therefore $P^k=P$ for all $k\ge1$. On the other hand, the Jacobson radical of an Artinian ring is nilpotent ([Stacks Project, Lemma 10.53.4](https://stacks.math.columbia.edu/tag/00J8)), so $P=0$. A nilpotent element lies in every maximal ideal, hence in $P=0$. $\square$

Equivalently, each localization $R_M$ is an Artinian local ring with $M=M^2$, hence a field by Nakayama's lemma, and $R$ is the product of these fields ([Stacks Project, Lemma 10.53.5](https://stacks.math.columbia.edu/tag/00JA)). [Expository] The criterion itself is pure commutative algebra. Geometry enters only through the existence of transversal coordinates, which Lemma 2 provides.

**Lemma 5 (maximal ideals are complex points) [Lean, read].** Let $X$ be locally of finite type over $\mathbb C$ and let $U\subset X$ be affine. Then every maximal ideal of $\Gamma(X,U)$ equals $\mathfrak m_y$ for some complex point $y\in U$.

*Proof.* The ring $\Gamma(X,U)$ is a finitely generated $\mathbb C$-algebra. By Zariski's lemma its residue field at a maximal ideal $\mathfrak m$ is finite over $\mathbb C$ (Mathlib's <code>finite_of_finite_type_of_isJacobsonRing</code>; [Stacks Project, Theorem 10.34.1](https://stacks.math.columbia.edu/tag/00FV)). Since $\mathbb C$ is algebraically closed, that residue field is $\mathbb C$ itself. The composite $\Gamma(X,U)\to\Gamma(X,U)/\mathfrak m\cong\mathbb C$ is then a complex point of $U$ with kernel $\mathfrak m$ (<code>MaxPt.exists_cxPts_ker_eq</code>). $\square$

*Proof of the theorem.* We follow <code>FibRed.exists_finCover_fibre_reduced</code>, lines 40–86.

- *Setup.* Projectivity gives $\iota:X\to\mathbb P^N$. Lemma 2 gives forms $f_0,F_1,\ldots,F_d$; write $f_i=F_i$ for $i\ge1$. Lemma 1 gives $F$, $x$, the finite cover and the affine cover, with $x_i$ the germ of $f_i/f_0$; in particular $x_0=1$.
- *The germ isomorphism.* Put $U_0=D(f_0)$ and $t_j=f_j/f_0\in\Gamma(X,U_0)$; the germ of $t_j$ is $x_j=x_j/x_0$. The affine-cover property for $I=\{0\}$ says that $B_0$ is the set of germs of sections over $U_0$. So Lemma 3 gives the isomorphism $\Gamma(X,U_0)/(t)\cong B_0/J$.
- *Item (3).* The ring $B_0/J$ is a finite $\mathbb C$-algebra, by the argument of Lemma 5 of the preceding subsection (<code>isArtinianRing_fib_quot</code>). Hence it is Artinian, and so is $\Gamma(X,U_0)/(t)$. Let $\mathfrak m\supset(t)$ be a maximal ideal of $\Gamma(X,U_0)$. By Lemma 5, $\mathfrak m=\mathfrak m_y$ for a complex point $y\in U_0$, and $t_j\in\mathfrak m_y$ means that every $t_j$ vanishes at $y$. By Lemma 2(iii), $\mathfrak m_y\subset(t)+\mathfrak m_y^2$. Lemma 4 now shows that $\Gamma(X,U_0)/(t)$ is reduced, and the germ isomorphism transfers this to $B_0/J$.
- *Item (2).* Let $y\in S$. Lemma 2(ii) puts $y$ in $U_0$ with $t_j(y)=0$. A section of $U_0$ whose germ is $x_j$ equals $t_j$, because germs are injective. So it vanishes at $y$.
- *Item (1)* is Lemma 1. $\square$

**Proposition (sending <code>RedFib</code> to the source) [Lean, read].** Let $c_1:Y\to Z$ be a finite étale morphism of integral schemes over $\mathbb C$, both smooth of dimension $d$, with $Z$ projective. Let $(x,U)$ be data for $Z$ as in the theorem, and view $K=\mathbb C(Z)\subset K'=\mathbb C(Y)$ via $c_1$. Then:

- $x$ is a finite cover of $K'$, and $(c_1^{-1}U_i)$ is an affine cover for the integral closures $B'_I\subset K'$;
- the source origin fibre ring $B'_0/J'$ is reduced. That is, <code>RedFib</code> holds for $K'$.

*Proof.* The first statement is <code>isFinCover_pull</code> [Lean]. For the second, identify $B_0\cong\Gamma(Z,U_0)$ and $B'_0\cong\Gamma(Y,c_1^{-1}U_0)$ by germs. Under these identifications the inclusion $B_0\to B'_0$ is the pullback $c_1^\ast$ on sections over the affine $U_0$. That map is étale, in particular formally unramified (<code>upB_fu</code>). Both $J$ and $J'$ are generated by the same ratios, so $J$ generates $J'$ (<code>map_upB_span_tco</code>) and $B'_0/J'=B'_0\otimes_{B_0}B_0/J$. Both fibre rings are finite over $\mathbb C$ (<code>fin_quot</code>). The argument of <code>red_of_fu</code> then runs as follows.

- A reduced finite algebra over the perfect field $\mathbb C$ is a finite product of separable field extensions, hence formally unramified over $\mathbb C$ (<code>formallyUnramified_of_isReduced</code>).
- $B'_0/J'$ is formally unramified over $B_0$, as the composite of $B_0\to B'_0$ with a surjection, and hence also over $B_0/J$.
- Composites of formally unramified maps are formally unramified, so $B'_0/J'$ is formally unramified over $\mathbb C$.
- A formally unramified algebra over a field is reduced (Mathlib's <code>Algebra.FormallyUnramified.isReduced_of_field</code>). $\square$

The classical statements behind the proposition are two. A ring that is smooth, in particular étale, over a reduced ring is reduced ([Stacks Project, Lemma 10.163.7](https://stacks.math.columbia.edu/tag/033B)). Étale algebras over a field are products of finite separable extensions ([Lemma 10.143.4](https://stacks.math.columbia.edu/tag/00U3)). Étaleness near the fibre cannot be dropped. Over the three-point fibre $\mathbb C[x]/(x^3-x)$ of the first example, adjoining $s$ with $s^2=x-2$ gives $\prod_{a\in\{0,\pm1\}}\mathbb C[s]/(s^2-(a-2))$, which is six copies of $\mathbb C$. Over a point with $x=2$ the same equation gives $\mathbb C[s]/(s^2)$.

**The actual call [Lean, read].** In <code>holomorphic_lefschetz_finiteEtale_integral</code>, line 103 applies the theorem to the target $Z$, with $S$ the image under $c_1$ of the finite set of coincidences. Its outputs are consumed as follows.

- *The finite and affine covers of $Z$.* They are passed to the chart theorem <code>exists_chart_lift_of_finite_cover</code> at line 206. At line 109 they are pulled back to $Y$ by <code>isFinCover_pull</code>.
- *The reduced fibre of $Z$.* Line 110 sends it to $Y$ by the proposition (<code>etaleCorrespondence_fieldExtension_statement</code>). The result <code>hredY</code> is the fourth hypothesis of the chart theorem (line 207). <code>field0_of</code> stores it as the field <code>red</code> of <code>Y1</code> (<code>TraceEqZeroOfBot.lean:65</code>). In turn <code>fieldLe_of</code> passes <code>h0.red</code> to <code>ResidueOfTraceIsFiberSum</code> with $L=K'$ (<code>PFieldLe.lean:323</code>). This is the hypothesis <code>RedFib</code> of the [reduced-fibre trace theorem](#from-the-finite-algebra-trace-to-the-reduced-fibre). The same <code>hredY</code> supplies regular parameters at the fixed evaluations (line 156, <code>exists_regular_parameters_of_reduced_quotient</code>). The target's own reduced fibre supplies the generation of target maximal ideals by the ratios (line 225) and enters the conjugacy of tangent matrices (line 198).
- *The placement of $S$ over the origin.* Lines 117–132 use it to show that every fixed evaluation on the origin chart of $Y$ kills the $t_j$: the section of $U_0$ with germ $t_j$ vanishes at $c_1(y)$, and evaluation commutes with pullback. This is the field <code>orig</code> of <code>Y1</code>. By <code>etaleCorrespondence_differentials_statement</code>, $t_j$ does not vanish at a point of $U_0\cap U_j$. Combined with the placement, this shows at lines 208–214 that no fixed evaluation lies on another chart; that is the field <code>off</code>.

**Remark (where each hypothesis is used) [Expository].**

- *Characteristic zero.* It enters in three places.
  - It gives separability of $K/F$, the field <code>sep</code> of <code>IsFinCover</code> (<code>IsFinCover.of_charZero</code>).
  - Sard's theorem in step 2 has no characteristic-$p$ analogue. On $\mathbb A^1_{\mathbb F_p}$ the function $t^p$ has no reduced fibre, since $t^p+c=(t+c^{1/p})^p$, and no translation helps.
  - The proposition uses that $\mathbb C$ is perfect. Over the imperfect field $\mathbb F_p(s)$, the field $\mathbb F_p(s)[x]/(x^p-s)$ is reduced but not étale.

  The preceding subsection's Lemma 4 uses perfectness as well.
- *Separability.* In characteristic zero it is automatic. It is part of <code>IsFinCover</code> and of the description of reduced finite algebras as étale algebras.
- *Smooth points.* Smoothness is used at four places.
  - Full jets on $S$ (step 1): at a singular point the cotangent space has dimension larger than $d$, so $d$ functions cannot span it.
  - Regular values in Sard's theorem (step 2).
  - Normality, which gives "integral elements are sections" in Lemma 1, and smoothness of the chart rings $B_{\{i\}}$, which <code>IsFinCover</code> requires.
  - Finite type of $B_0$, used for the Artinian fibre: <code>isArtinianRing_fib_quot</code> calls <code>h.smooth 0</code>.
- *The base field $\mathbb C$.* Three properties are used.
  - Algebraic closedness: in Lemma 5 and in <code>MaxPt.eq_top_of_forall_cxPts_mem</code>, complex points detect maximal ideals and open sets.
  - Lebesgue measure on $\mathbb C^d$ in step 4, and the analytic structure for Sard's theorem in step 2.
  - Infinitude in step 6.

  Over a merely infinite algebraically closed field of characteristic zero, one would replace the Sard step by generic smoothness of $g/h$ and choose $c$ outside a proper Zariski-closed set. The archive does not take that route.
- *Projectivity and integrality.* Projectivity supplies the forms, and the properness in Lemma 1. Integrality supplies the function field, the generic point used in step 3 and the injectivity of germs in Lemma 3.

**Remark (what is and is not claimed) [Expository].**

- The forms are not a general choice. They are special along $S$, where they vanish with prescribed jets, and general only in the translation parameter $c$ and in the denominator $f_0$. No Bertini-type statement about general members of a linear system is used. The genericity is the explicit Sard null set for $c$ together with finite avoidance for $f_0$.
- Only the origin fibre is made reduced. Other fibres may be ramified, like the triple flex fibre at infinity in the first example.
- Projection from a point outside $X$ gives finiteness alone ([Stacks Project, Lemma 43.23.1](https://stacks.math.columbia.edu/tag/0B1P)), and iterating it gives projections from linear centres. The map $(f_0:\cdots:f_d)$ is a linear projection, from a centre disjoint from the image, composed with the degree-$n$ Veronese embedding. The archive proves its finiteness directly by the affine-plus-proper criterion.

**Reading the formal proof.** Paths are relative to the root of archive A2 (Lean 4.33.1, joined SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>, Mathlib pinned at <code>0df444a360eaa60ab8c11dca51a86af692955474</code>).

| Node | A2 path and lines | Role and reading |
|---|---|---|
| <code>exists_finiteCover_projSpace_reduced_fibre_origin</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFiniteCoverProjSpaceReducedFibreOriginStatement.lean:8–9</code> | Exported statement and delegation. R3 [Lean, read]. |
| <code>FibRed.exists_finCover_fibre_reduced</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFiniteCoverProjSpaceReducedFibreOrigin.lean:40–86</code> | Direct producer; proof of the theorem. R3 [Lean, read]. |
| <code>FibRed.quotEquiv_of_germ</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFiniteCoverProjSpaceReducedFibreOrigin.lean:17–38</code> | Lemma 3. R3 [Lean, read]. |
| <code>EtProj.Transv.exists_forms_transversal</code>, <code>exists_transversal_forms_first_separate</code>, <code>mem_ptsIn_fOpen_iff</code>, <code>evHom_fRatio_eq_zero_iff</code>, <code>frac_smul_deg</code>, <code>fRatio_add_smul</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFormsTransversalAtComplexPoints.lean:22–75,83–226,234–258</code>; statement <code>ExistsFormsTransversalAtComplexPointsStatement.lean:7–17</code> | Lemma 2. R3 [Lean, read] for the bodies. The following subsections read all six named direct inputs at their stated scopes. |
| <code>EtProj.isFinCover_of_forms</code>, <code>isFinite_formMap</code>, <code>isCoordFamily_fRatio</code>, <code>formMap_preimage</code>, <code>rat_formMap</code>, <code>exists_finCover_of_isFinite</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSmoothFiniteCoverOfFormsNoCommonZero.lean:29–175</code>; statement <code>IsSmoothFiniteCoverOfFormsNoCommonZeroStatement.lean:8–9</code> | Lemma 1. R3 [Lean, read] for the bodies; chart inputs at statement level. |
| <code>isReduced_quotient_of_artinian_of_maximal_le</code>, <code>quotient_maximal_le_sq</code>, <code>pow_eq_self_of_le_sq</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsReducedQuotientOfArtinianOfMaximalLe.lean:7–77</code> | Lemma 4. R3 [Lean, read]. |
| <code>MaxPt.exists_cxPts_ker_eq</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplexPointKerEvalEqMaximal.lean:13–44</code> | Lemma 5. R3 [Lean, read]. |
| <code>isArtinianRing_fib_quot</code>, <code>finite_quotient_of_integral</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsArtinianRingFibQuot.lean:7–96</code> | Artinian fibre ring. R3 [Lean, read]. |
| <code>fOpen</code>, <code>fRatio</code>, <code>fRatio_self</code>; <code>IsAffCover</code>, <code>ffAlg</code>; <code>IsProjOver</code>, <code>PSpace</code>; <code>IsFinCover.of_charZero</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FRatioSelf.lean:16–29</code>, <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/IsAffCoverSpec.lean:64–65,79–84</code>, <code>src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsCompletedStrictHens.lean:16–23</code>, <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/DlogRatioVolumeFormNeZero.lean:103–107</code> | Definitions and the characteristic-zero constructor. Read. |
| <code>etaleCorrespondence_fieldExtension_statement</code>, <code>red_of_fu</code>, <code>fin_quot</code>, <code>upB_fu</code>, <code>map_upB_span_tco</code>; <code>SepIdem.formallyUnramified_of_isReduced</code> | <code>src/Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCorrespondenceFieldExtensionStatement.lean:9–209</code>, <code>src/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormallyUnramifiedOfIsReduced.lean:7–17</code> | The proposition. R3 [Lean, read]; <code>isFinCover_pull</code>, <code>mem_rB_pull</code> and <code>rA_finite</code> at statement level. |
| Actual call | <code>src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/HolomorphicLefschetzFiniteEtaleIntegral.lean:103–139,156,198,206–225</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/TraceEqZeroOfBot.lean:52–65</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/ResidueOfTraceIsFiberSum.lean:26–40</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PFieldLe.lean:216–221,323</code> | From the target fibre to <code>Y1.red</code>, <code>orig</code> and <code>off</code>, and on to <code>RedFib</code>. Prior R3 (1123n, 1124a), rechecked for these lines. |

R3 covers the named bodies. The following are used at their interfaces.

- The six direct inputs of Lemma 2 are read below: the [jet forms](#forms-with-prescribed-jets-at-finitely-many-points), the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets), [finiteness of transversal zeros](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes), [denominator choice and complex-point detection](#choosing-the-denominator-and-detecting-the-open-cover), and the [change of denominator](#changing-the-denominator-in-cotangent-generation).
- The chart inputs of Lemma 1: <code>pulledBackProjCoordinateRatio_overlap_div</code>, <code>algebraicIndependent_pulledBackProjCoordinateRatios</code>, <code>finite_projection_function_field</code>, <code>projective_chart_affine_cover</code>, <code>chart_function_field_integral</code>, <code>genericGerm_chartInter_integral_coordinateRatios</code> and <code>affine_germ_subalgebra_smooth</code>; also <code>IsCoordFamily.toHom</code>, <code>isAffineHom_of_isAffineOpen_preimage_chart</code> and <code>isProper_str</code>.
- The pull-back <code>isFinCover_pull</code>, and the consumers <code>exists_regular_parameters_of_reduced_quotient</code>, <code>etaleCorrespondence_local_parameters_statement</code>, <code>etaleCorrespondence_differentials_statement</code> and <code>etaleCorrespondence_sections_statement</code>.
- The Mathlib library lemmas.

The [reduced-fibre trace](#from-the-finite-algebra-trace-to-the-reduced-fibre), the [global boundary](#from-fixed-point-vanishing-to-a-global-čech-boundary) and the [local Koszul weights](#from-a-finite-étale-chart-to-the-local-lefschetz-weight) keep the reading levels recorded there, as do <code>FixK_holds</code> and the group-side matching.

#### Forms with prescribed jets at finitely many points

The [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre) began with a step it took as given: forms $h,g_1,\ldots,g_d$ of one degree $n$ with full first-order jets on the finite set $S$, with $h$ vanishing to second order on $S$, and with no common zero outside $S$. That step is the statement <code>exists_forms_vanishing_complexPoints_fullJets</code>, whose only producer is <code>EtProj.Jets.exists_jet_forms</code>. This subsection reads that producer. We explain how a single degree serves every point of $S$ at once, which bridge the archive actually uses to pass from local functions to homogeneous forms, in which order the quantifiers come, and how the result is consumed. The Sard translation, the finite projection and the reduced fibre keep the reading recorded in the previous subsection; nothing there is redone here.

**Motivation.** A first-order jet at a complex point $y$ of a smooth $d$-dimensional variety is an element of $\mathfrak m_y/\mathfrak m_y^2$, a $d$-dimensional vector space. Prescribing jets at one point is a local matter. The difficulty is to do it at several points with forms of one common degree, and to do it so that the forms impose nothing unwanted elsewhere. Three things pull against each other.

- *Spanning at every point of $S$.* The $d$ forms $g_j$ must have jets at each $y\in S$ that span $\mathfrak m_y/\mathfrak m_y^2$. A form chosen for one point may have a useless jet at another.
- *Vanishing on all of $S$.* Each $g_j$ and $h$ must vanish at every point of $S$. A form that is good at $y$ must also be killed at the other points without damaging its jet at $y$.
- *No other common zeros.* Outside $S$ the $d+1$ forms must have no common zero on $X$. This is a global condition on a $d$-dimensional variety, where $d$ forms alone always have common zeros.

The textbook answer runs through Serre vanishing: for large $n$ the restriction $H^0(\mathbb P^N,\mathcal O(n))\to H^0(Z,\mathcal O_Z(n))$ is onto for the finite subscheme $Z$ cut out by $\prod_{y\in S}\mathfrak m_y^2$, since $H^1(\mathcal I_Z(n))=0$ ([Stacks 01YS](https://stacks.math.columbia.edu/tag/01YS), part (4)), and then one chooses the sections freely in the finite-dimensional ring $\Gamma(\mathcal O_Z)=\prod_y\mathcal O_y/\mathfrak m_y^2$. The archive does not use cohomology and does not use a Chinese remainder decomposition. It uses products of linear forms to separate points, the coordinate ratios to generate the chart ring, and the fact that a vector space over an infinite field is not a finite union of proper subspaces. The price is an explicit, non-sharp degree: the proof produces $n=2(|S|+1)$.

**Example (two points of $\mathbb P^1$ with first derivatives) [Expository].** Let $X=\mathbb P^1$ with coordinates $(x_0:x_1)$, $d=1$, and $S=\{P_1,P_2\}$ with $P_1=(0:1)$ and $P_2=(1:1)$. Then $|S|=2$, so the archive's recipe takes $m=3$ and $n=6$. On the chart $D(x_1)$ write $t=x_0/x_1$; the points are $t=0$ and $t=1$.

- *Linear separators.* The linear form $x_0$ vanishes at $P_1$ and not at $P_2$; the form $x_0-x_1$ vanishes at $P_2$ and not at $P_1$.
- *Killing the other point in degree $k=n-1=5$.* For $P_1$ take $w_1=x_1^4(x_0-x_1)$. It vanishes at $P_2$ and equals $-1$ at $P_1$. For $P_2$ take $w_2=x_1^4x_0$, which vanishes at $P_1$ and equals $1$ at $P_2$.
- *The jet form at $P_1$.* The function $u=t$ generates $\mathfrak m_{P_1}$. Its homogeneous lift is the linear form $l_1=x_0$, which already vanishes at $P_1$. The ratio $t_w=w_1/x_1^5=t-1$ has value $-1$ at $P_1$. The archive forms $l=(-1)^{-1}l_1=-x_0$ and the degree-six form $g^{(1)}=l\,w_1=-x_0x_1^4(x_0-x_1)$. Then $g^{(1)}/x_1^6=-t(t-1)=t-t^2$, so $u-g^{(1)}/x_1^6=t^2\in\mathfrak m_{P_1}^2$, and $g^{(1)}$ vanishes at $P_2$.
- *The jet form at $P_2$.* With $u=t-1$, $l_1=x_0-x_1$, and $t_w=w_2/x_1^5=t$ of value $1$ at $P_2$, we get $g^{(2)}=(x_0-x_1)x_1^4x_0$ and $g^{(2)}/x_1^6=t(t-1)=(t-1)+(t-1)^2$. So $u-g^{(2)}/x_1^6=-(t-1)^2\in\mathfrak m_{P_2}^2$, and $g^{(2)}$ vanishes at $P_1$.
- *One form for both points.* Since $d=1$ the induction below chooses a single form $c_1$ of degree six vanishing on $S$, not identically zero on $X$, and with nonzero jet at both points. The form $c_1=x_0(x_0-x_1)x_1^4$ works: $c_1/x_1^6=t^2-t$ has derivative $-1$ at $t=0$ and $1$ at $t=1$. Its zero set is $\{P_1,P_2,\infty\}$ with $\infty=(1:0)$ counted four times.
- *The form $h$.* Now a form $q$ of degree $m=3$ vanishing on $S$ and not at $\infty$ is needed: $q=x_0^2(x_0-x_1)$, with $q(\infty)=1$. Put $h=q^2=x_0^4(x_0-x_1)^2$. The common zeros of $h$ and $c_1$ are exactly $P_1$ and $P_2$.
- *The jet clause in the chart $x_1^6$.* We have $h/x_1^6=t^4(t-1)^2\in\mathfrak m^2$ at both points, and $t=-(c_1/x_1^6)+t^2$, $t-1=(c_1/x_1^6)-(t-1)^2$. So $\mathfrak m_y\subset(c_1/x_1^6)+\mathfrak m_y^2$ at both points.
- *Changing the denominator.* The theorem asserts the jet clause for every degree-six form $f_0$ that does not vanish at the point. Take $f_0=(x_0+x_1)^6$, with $f_0(P_1)=1$ and $f_0(P_2)=64$, and the chart coordinate $s=x_0/(x_0+x_1)$, so that $t=s/(1-s)$, $P_1$ is $s=0$ and $P_2$ is $s=1/2$. Then $c_1/f_0=s(2s-1)(1-s)^4$ and $h/f_0=s^4(2s-1)^2$. The derivative of $c_1/f_0$ is $-1$ at $s=0$ and $1/16$ at $s=1/2$. The two ratios differ by the unit $x_1^6/(x_0+x_1)^6=(1-s)^6$ on the overlap, and at $P_2$ the jet picks up this unit's value $1/64$ together with $dt/ds=4$: indeed $1\cdot4\cdot(1/64)=1/16$.
- *Degree.* The archive's $n=6$ is not the least possible degree. The four clauses allow $h=0$, and then $n=2$ already works: $g=x_0(x_0-x_1)$ is not identically zero, its zeros are exactly $P_1$ and $P_2$, $g/x_1^2=t^2-t$ has derivative $-1$ at $t=0$ and $1$ at $t=1$, and $h/f_0=0$ lies in every $\mathfrak m_y^2$. A nonzero linear form vanishes at only one point of $\mathbb P^1$, so $2$ is the least degree. If $h\ne0$ is required, then $h$ is divisible by $x_0^2(x_0-x_1)^2$, so $n\ge4$, and $n=4$ is attained by $h=x_0^2(x_0-x_1)^2$ and $c_1=x_0(x_0-x_1)x_1^2$.

**Example (two points of a smooth plane cubic) [Expository].** Let $E\subset\mathbb P^2$ be $y^2z=x^3-xz^2$, the curve of the previous subsection, and $S=\{P_0,P_1\}$ with $P_0=(0:0:1)$ and $P_1=(1:0:1)$. Again $m=3$ and $n=6$. On the chart $z=1$ the curve is $F=y^2-x^3+x=0$.

- *Cotangent spaces.* The gradient of $F$ is $(1,0)$ at $P_0$ and $(-2,0)$ at $P_1$. Hence $x\in\mathfrak m_{P_0}^2$ and $x-1\in\mathfrak m_{P_1}^2$ on $E$; explicitly $x=x^3-y^2$ and $(x-1)x(x+1)=y^2$ with $x(x+1)$ a unit of value $2$ at $P_1$. At both points $y$ is a basis of $\mathfrak m/\mathfrak m^2$.
- *Separators and jet forms.* The linear form $x$ kills $P_0$ and is a unit at $P_1$; the form $x-z$ kills $P_1$ and is a unit at $P_0$. For $u=y$ at $P_0$ take $w=z^4(x-z)$, of value $-1$ at $P_0$, so $g^{(0)}=-yz^4(x-z)$ and $g^{(0)}/z^6=y-xy\equiv y$ modulo $\mathfrak m_{P_0}^2$. For $u=y$ at $P_1$ take $w=z^4x$, of value $1$, so $g^{(1)}=xyz^4$ and $g^{(1)}/z^6=xy=y+(x-1)y\equiv y$ modulo $\mathfrak m_{P_1}^2$.
- *One form for both points.* Here the simplest choice is $c_1=yz^5$: it vanishes on $S$, is not identically zero on $E$, and $c_1/z^6=y$ is a cotangent basis at both points. Its zero set on $E$ is $\{y=0\}\cup\{z=0\}$, namely $P_0$, $P_1$, $P_{-1}=(-1:0:1)$ and the flex $O=(0:1:0)$.
- *The form $h$.* A cubic $q$ vanishing on $S$ and not at $P_{-1}$ or $O$: $q=xz(x-z)+y^3$, with $q(P_{-1})=2$ and $q(O)=1$. Put $h=q^2$. The common zeros of $h$ and $c_1$ on $E$ are exactly $P_0$ and $P_1$.
- *The jet clause.* In the chart $z^6$: $h/z^6=(x(x-1)+y^3)^2\in\mathfrak m^2$ at both points, and $\mathfrak m_{P_0}=(x,y)\subset(y)+\mathfrak m_{P_0}^2$, $\mathfrak m_{P_1}=(x-1,y)\subset(y)+\mathfrak m_{P_1}^2$. In the chart $f_0=(x+z)^6$, with coordinates $X=x/(x+z)$, $Y=y/(x+z)$ and $z/(x+z)=1-X$, the curve is $Y^2(1-X)=X^3-X(1-X)^2$, the points are $(0,0)$ and $(1/2,0)$, the gradients are $(1,0)$ and $(-1,0)$, and $c_1/f_0=Y(1-X)^5$ is congruent to $Y$ at $P_0$ and to $Y/32$ at $P_1$ modulo $\mathfrak m^2$. Both are cotangent bases.
- *Degree.* For this $S$ a pair of degree two already exists, $g=yz$ and $h=x^2-xz+y^2$, because the ambient coordinates $x$ and $x-z$ restrict to functions vanishing doubly on $E$ at $P_0$ and $P_1$; and no linear forms work. If $h\ne0$, the line $h=0$ would have to be tangent to $E$ at $P_0$, so it would be $x=0$, which misses $P_1$. If $h=0$, the line $g=0$ would have to pass through $P_0$ and $P_1$, so it would be $y=0$, which also passes through $P_{-1}$ and violates clause 3. The archive's $n=2(|S|+1)$ is a uniform bound that does not see such coincidences.

All assertions in both examples are exact polynomial identities and ideal-membership tests, checked by `check_jet_forms.py` in the run directory (82 assertions); the degree statements, corrected after the audit to allow $h=0$, are checked in Part D of `check_sard_shifts.py` (13 assertions).

**Definitions.** Throughout, $X$ is an integral scheme with a closed immersion $\iota:X\to\mathbb P^N_{\mathbb C}$, smooth of relative dimension $d$ over $\mathbb C$ (<code>SmoothOfRelativeDimension d p</code>). Forms are elements of the degree-$n$ part of $\mathbb C[X_0,\ldots,X_N]$ (<code>grading ℂ N n</code>).

- For a form $f$, $D(f)=\iota^{-1}D_+(f)$ is the open set of $X$ where $f$ does not vanish (<code>fOpen ι f</code>); a scheme point $x$ lies in $D(f)$ iff $f\notin\mathfrak p_x$, the homogeneous prime of $\iota(x)$ (<code>mem_fOpen</code>). If $f,g$ have the same degree, $f/g\in\Gamma(X,D(g))$ is the pulled-back fraction (<code>fRatio ι f g</code>), with $g/g=1$ (<code>fRatio_self</code>), additive and $\mathbb C$-linear in $f$ (<code>fRatio_add_n</code>, <code>fRatio_smul_n</code>).
- A complex point is a section $y:\operatorname{Spec}\mathbb C\to X$ over $\mathbb C$ (<code>CxPts p (RingHom.id ℂ)</code>); its underlying point is $y(\ast)$, written $y$ as well. For an open $U$ containing it, $\mathrm{ev}_y:\Gamma(X,U)\to\mathbb C$ is evaluation (<code>CxPts.evHom</code>), and $\mathfrak m_y=\ker\mathrm{ev}_y$. Then $f/g$ vanishes at $y\in D(g)$ iff $f\in\mathfrak p_y$ (<code>ev_ratio_eq_zero_iff</code>). Distinct complex points have distinct underlying points when $X$ is of finite type (<code>pt_inj</code>), and a complex point is a closed point, so a specialization $y\rightsquigarrow x$ forces $x=y$ (<code>eq_of_specializes</code>).
- For a finite set $S$ of complex points, $V_S(k)$ is the vector space of degree-$k$ forms vanishing at every point of $S$ (<code>vanS ι S k</code>). For a scheme point $x$, $V_S(k)_x\subset V_S(k)$ is the subspace of forms lying in $\mathfrak p_x$ (<code>vanAt ι S k x</code>).
- For a form $a$ of degree $k$ and $y\in S\cap D(a)$, the jet map $J_y:V_S(k)\to\Gamma(X,D(a))/\mathfrak m_y^2$ sends $f$ to the class of $f/a$ (<code>jet ι S hp k ha hy</code>). Since $f$ vanishes at $y$, the class lies in $\mathfrak m_y/\mathfrak m_y^2$.

**Theorem (forms with full jets on $S$) [Lean, read].** Let $X$, $\iota$, $d$ be as above and let $S$ be a finite set of complex points of $X$. Then there exist an integer $n\ge1$, a form $h$ of degree $n$ and forms $g_1,\ldots,g_d$ of degree $n$ such that

1. no $g_j$ vanishes at the generic point of $X$;
2. every $g_j$ vanishes at every point of $S$;
3. every complex point at which $h$ and all $g_j$ vanish lies in $S$;
4. for every $y\in S$ and every form $f_0$ of degree $n$ with $f_0(y)\ne0$, in the ring $\Gamma(X,D(f_0))$ one has $h/f_0\in\mathfrak m_y^2$ and $\mathfrak m_y\subset(g_1/f_0,\ldots,g_d/f_0)+\mathfrak m_y^2$.

The proof gives $n=2(|S|+1)$. The forms are chosen before $f_0$; the fourth clause holds for every admissible denominator at once.

This is <code>EtProj.Jets.exists_jet_forms</code>; the exported statement <code>exists_forms_vanishing_complexPoints_fullJets</code> is the same sentence and delegates to it. We first prove five lemmas, all read in the archive.

**Lemma 1 (a linear form separates a complex point from any other point) [Lean, read].** Let $y$ be a complex point and $x\in X$ a scheme point with $x\ne y$. There is a linear form $l$ with $l\in\mathfrak p_y$ and $l\notin\mathfrak p_x$.

*Proof.* This is <code>exists_lin_sep</code>. Suppose every linear form in $\mathfrak p_y$ lies in $\mathfrak p_x$. Pick a coordinate $X_i\notin\mathfrak p_y$ (<code>Generic.exists_X_notMem</code>: no point of $\mathbb P^N$ contains the irrelevant ideal) and work on the affine chart $U=D(X_i)$ with $e=\mathrm{ev}_y$ and the ratios $r_l=X_l/X_i\in\Gamma(X,U)$. Because $\iota$ is a closed immersion, the $r_l$ generate $\Gamma(X,U)$ as a $\mathbb C$-algebra (<code>RatSpan.adjoin_fRatio_eq_top</code>: the ring map $\Gamma(\mathbb P^N,D_+(X_i))\to\Gamma(X,U)$ is onto and the source is generated by the fractions). The linear forms $l_l=X_l-e(r_l)X_i$ lie in $\mathfrak p_y$, since $l_l/X_i=r_l-e(r_l)$ vanishes at $y$ (<code>rat_sub_const</code>). By assumption they lie in $\mathfrak p_x$. Then $x\in U$: otherwise $X_i\in\mathfrak p_x$, hence $X_l=l_l+e(r_l)X_i\in\mathfrak p_x$ for all $l$, which is impossible. Let $I\subset\Gamma(X,U)$ be the ideal of sections vanishing at $x$, the preimage of the maximal ideal of the stalk. From $l_l\in\mathfrak p_x$ we get $r_l-e(r_l)\in I$ (<code>basicOpen_app_frac</code>). Since the $r_l$ generate, induction over sums and products (<code>Algebra.adjoin_induction</code>) gives $u-e(u)\in I$ for every $u\in\Gamma(X,U)$. Hence every basic open $D(u)\subset U$ containing $x$ has $e(u)\ne0$, that is, contains $y$. Because $U$ is affine these basic opens form a base at $x$ (<code>IsAffineOpen.exists_basicOpen_le</code>), so $y\rightsquigarrow x$. But $y$ is a closed point (<code>eq_of_specializes</code>, via <code>isClosedImmersion_of_comp_eq_id</code> for the section $y$), so $x=y$, a contradiction. $\square$

Lemma 33.22.2 of the Stacks Project ([0B58](https://stacks.math.columbia.edu/tag/0B58)) proves more at once: over an infinite field, for a rational point $y$ and finitely many arbitrary points $x_1,\ldots,x_n\ne y$, one section of a very ample sheaf vanishes at $y$ and at no $x_i$. The archive proves the case of a single point $x$, by specialization instead of through the homogeneous ideal of $y$, and handles several points by taking products (Lemma 2), at the cost of degree.

**Lemma 2 (a form of any degree $k\ge|S|$ vanishing on $S$ and not at $x$) [Lean, read].** Let $S$ be finite, $k\ge|S|$, and $x\in X$ different from every point of $S$. There is $f\in V_S(k)$ with $f\notin\mathfrak p_x$. Consequently $V_S(k)_x\ne V_S(k)$, and also $V_S(2k)_x\ne V_S(2k)$.

*Proof.* This is <code>exists_sep</code>. For each $y\in S$ take $l_y$ from Lemma 1, and a coordinate $X_i\notin\mathfrak p_x$. Put $f=X_i^{\,k-|S|}\prod_{y\in S}l_y$. It has degree $k$ and vanishes on $S$. If $f\in\mathfrak p_x$, primality of $\mathfrak p_x$ would put $X_i$ or some $l_y$ into $\mathfrak p_x$. For the last claim use $f^2$ (<code>hvann</code> in the main proof). $\square$

**Lemma 3 (one point, one function, with the other points killed) [Lean, read].** Let $g_0$ be a linear form, $y$ a complex point in $D(g_0)$, and $u\in\Gamma(X,D(g_0))$ with $u(y)=0$.

- (a) There is a linear form $l_1\in\mathfrak p_y$ with $u-l_1/g_0\in\mathfrak m_y^2$.
- (b) Let $w$ be a form of degree $k$ with $w\notin\mathfrak p_y$, and set $t_w=w/g_0^k$. Then $l=e(t_w)^{-1}l_1$ is a linear form in $\mathfrak p_y$ with $u-lw/g_0^{1+k}\in\mathfrak m_y^2$.
- (c) Let $S\ni y$ be finite with $|S|\le k$. There is a form $g$ of degree $n=1+k$ vanishing on all of $S$ with $u-g/g_0^{\,n}\in\mathfrak m_y^2$.

*Proof.* (a) is <code>RatSpan.ratio_span_cotangent</code>. The chart ring is generated by the $r_l=X_l/g_0$, so a general algebraic fact (<code>exists_linear_mod_sq</code>, used at its statement) gives $c\in\mathbb C^{N+1}$ with $u-\sum_lc_l(r_l-e(r_l))\in\mathfrak m_y^2$: in a $\mathbb C$-algebra generated by the $r_l$, the classes of $r_l-e(r_l)$ span $\mathfrak m_y/\mathfrak m_y^2$. Taking $l_1=\sum_lc_lX_l-e(\sum_lc_lr_l)\,g_0$ gives $l_1/g_0=\sum_lc_lr_l-e(\sum c_lr_l)$ (<code>Generic.Lm_apply</code>, <code>rat_sub_const</code>), which vanishes at $y$, so $l_1\in\mathfrak p_y$.

(b) is <code>exists_lin_mul</code>. On $D(g_0)$ we have $lw/g_0^{1+k}=(l_1/g_0)\cdot(t_w/e(t_w))$, and $e(t_w)\ne0$ because $w\notin\mathfrak p_y$. Then
$$u-\frac{lw}{g_0^{1+k}}=\Bigl(u-\frac{l_1}{g_0}\Bigr)+\frac{l_1}{g_0}\Bigl(1-\frac{t_w}{e(t_w)}\Bigr).$$
The first bracket is in $\mathfrak m_y^2$ by (a); the second product has both factors in $\mathfrak m_y$. The rescaling by $e(t_w)^{-1}$ keeps $l\in\mathfrak p_y$.

(c) is <code>exists_form_jet</code>. Apply Lemma 2 to $S\setminus\{y\}$ with the point $x=y$ (distinct complex points have distinct underlying points, <code>pt_inj</code>) and degree $k\ge|S|-1$: this gives $w\in V_{S\setminus\{y\}}(k)$ with $w\notin\mathfrak p_y$. Then $g=lw$ from (b) vanishes at $y$ through $l$ and at the other points through $w$. The chart $D(g_0^{\,n})$ equals $D(g_0)$. $\square$

The multiplication by $w$ is the archive's bridge between the point $y$ and the rest of $S$. It plays the role that the idempotents of $\prod_y\mathcal O_y/\mathfrak m_y^2$ play in the Chinese remainder route, but it is a form, not a section, and it costs degree $k\ge|S|-1$ rather than cohomology.

**Lemma 4 (the jet map at a point of $S$ is onto the cotangent space) [Lean, read].** Let $a$ be a form of degree $k$ with $D(a)$ affine, let $y\in S\cap D(a)$, and suppose that every $u\in\mathfrak m_y\subset\Gamma(X,D(a))$ is congruent modulo $\mathfrak m_y^2$ to $g/a$ for some $g\in V_S(k)$. Then the range of $J_y:V_S(k)\to\Gamma(X,D(a))/\mathfrak m_y^2$ is exactly the image of $\mathfrak m_y$, a space of dimension $d$.

*Proof.* This is <code>jet_range</code>. The range is contained in the image of $\mathfrak m_y$ since forms in $V_S(k)$ vanish at $y$, and the hypothesis says it contains that image. Smoothness supplies a cotangent basis (<code>CotDim.exists_cotangent_basis</code>, used at its statement): sections $b_1,\ldots,b_d\in\mathfrak m_y$ such that every element of $\mathfrak m_y$ is congruent to a combination of them modulo $\mathfrak m_y^2$, and a combination lies in $\mathfrak m_y^2$ only when its coefficients vanish. So the range is the span of the classes of the $b_j$, which are linearly independent (<code>finrank_span_eq_card</code>). $\square$

Classically, $\dim\mathfrak m_y/\mathfrak m_y^2=d$ at a smooth point is Lemma 10.140.1 together with Lemma 10.140.3 of the Stacks Project ([00TR](https://stacks.math.columbia.edu/tag/00TR), [00TT](https://stacks.math.columbia.edu/tag/00TT)).

**Lemma 5 (a square vanishes to second order in every chart) [Lean, read].** Let $q$ be a form of degree $m$ with $q\in\mathfrak p_y$, and $f_0$ a form of degree $2m$ with $f_0\notin\mathfrak p_y$. Then $q^2/f_0\in\mathfrak m_y^2$ in $\Gamma(X,D(f_0))$.

*Proof.* This is <code>ratio_sq_mem</code>. For every form $b$ of degree $m$ the ratio $qb/f_0$ vanishes at $y$, so lies in $\mathfrak m_y$. The degree-$2m$ forms are sums of products $bc$ of degree-$m$ forms (<code>MvPolynomial.homogeneousSubmodule_one_pow</code>). For such a product, $(q^2/f_0)(bc/f_0)=(qb/f_0)(qc/f_0)\in\mathfrak m_y^2$, and the property passes to sums. Applying it to $f_0$ itself, $(q^2/f_0)(f_0/f_0)=q^2/f_0\in\mathfrak m_y^2$. $\square$

The point of the lemma is that it holds with no factorization of $f_0$ and no change of chart. It is what makes the clause $h/f_0\in\mathfrak m_y^2$ of the theorem hold for all $f_0$ simultaneously.

*Proof of the theorem.* We follow <code>exists_jet_forms</code>. Put $m=|S|+1$ and $n=2m$. The scheme $X$ is Noetherian, being closed in $\mathbb P^N$, and every point $x\in X$ has coheight at most $d$ (<code>AffineCover.coheight_le_of_smooth</code>, used at its statement): every chain of generalizations starting at $x$, that is, every chain of specializations ending at $x$, has length at most $d$, which is the classical bound $\dim\mathcal O_{X,x}\le d$ ([Stacks 02IZ](https://stacks.math.columbia.edu/tag/02IZ), [0A21](https://stacks.math.columbia.edu/tag/0A21)). Write $S$ also for the finite set of underlying points.

*Step 1, proper subspaces at points outside $S$.* By Lemma 2 with $k=m\ge|S|$, for every point $x\notin S$ we have $V_S(m)_x\ne V_S(m)$ and $V_S(n)_x\ne V_S(n)$.

*Step 2, the reference chart.* Choose a linear form $g_0$ that vanishes neither at the generic point nor at any point of $S$ (<code>EtProj.exists_form_genericPoint_cxPts</code>, [Lean, read], [denominator and open-cover proof](#choosing-the-denominator-and-detecting-the-open-cover)). Put $a=g_0^{\,n}$; then $D(a)=D(g_0)$ is affine and contains $S$. For $y\in S$ and $u\in\mathfrak m_y\subset\Gamma(X,D(a))$, Lemma 3(c) with $k=n-1\ge|S|$ produces $g\in V_S(n)$ with $u-g/a\in\mathfrak m_y^2$. So Lemma 4 applies: for each $y\in S$ the jet map $J_y:V_S(n)\to\Gamma(X,D(a))/\mathfrak m_y^2$ has range equal to the image of $\mathfrak m_y$, of dimension $d$.

*Step 3, the induction.* We show for $k\le d$: there are $c_1,\ldots,c_k\in V_S(n)$ such that (α) no $c_i$ vanishes at the generic point; (β) every point $x\notin S$ lying in $V(c_1,\ldots,c_k)$ has coheight at least $k$; (γ) for every $y\in S$ the jets $J_y(c_1),\ldots,J_y(c_k)$ are linearly independent. For $k=0$ there is nothing to prove. Suppose $c_1,\ldots,c_k$ are found and $k<d$. Let $Z=V(c_1,\ldots,c_k)\cap X$, a closed set, and let $T$ be the finite set of generic points of its irreducible components (<code>Generic.exists_finite_gen</code>, from <code>NoetherianSpace.exists_finite_set_isClosed_irreducible</code>; [Stacks 0052](https://stacks.math.columbia.edu/tag/0052)). Consider the following subspaces of $V_S(n)$:

- $V_S(n)_\xi$ for the generic point $\xi$ of $X$; this is proper by Step 1, since $\xi\notin S$ when $d>0$ (<code>hgenS</code>: at a complex point whose underlying point is $\xi$, every section vanishing there is zero by integrality, <code>eq_zero_of_generic</code>, while a cotangent basis element is a nonzero section);
- $V_S(n)_t$ for each $t\in T\setminus S$; proper by Step 1;
- $J_y^{-1}\bigl(\operatorname{span}(J_y c_1,\ldots,J_y c_k)\bigr)$ for each $y\in S$; proper because the range of $J_y$ has dimension $d>k$.

A vector space over an infinite field is not a finite union of proper subspaces (<code>Submodule.exists_forall_notMem_of_forall_ne_top</code>, Mathlib). Choose $c_{k+1}\in V_S(n)$ outside all of them. Then (α) holds for $c_{k+1}$, and (γ) holds by the choice outside the third family (<code>linearIndependent_fin_snoc</code>). For (β), let $x\notin S$ lie in $Z\cap V(c_{k+1})$. Some $t\in T$ specializes to $x$. If $t\in S$, then $t$ is a closed point and $x=t\in S$, which is excluded. So $t\notin S$, hence $t$ has coheight at least $k$ by (β) for $k$, and $t\in D(c_{k+1})$ by the choice outside the second family while $x\notin D(c_{k+1})$. Thus the specialization $t\rightsquigarrow x$ is strict, and the coheight of $x$ is at least that of $t$ plus one (<code>Generic.coheight_step</code>, from <code>Order.coheight_add_one_le</code>), that is, at least $k+1$.

*Step 4, the forms.* Take $c_1,\ldots,c_d$ from Step 3 with $k=d$ and put $g_j=c_j$. Let $Z=V(g_1,\ldots,g_d)\cap X$ and let $T$ be the generic points of its components. By Step 1, the subspaces $V_S(m)_t\subset V_S(m)$ for $t\in T\setminus S$ are proper; choose $q\in V_S(m)$ outside all of them, and put $h=q^2$, a form of degree $n$.

*Verification.* Clause 1 is (α). Clause 2 holds because $g_j\in V_S(n)$. For clause 3, let $z$ be a complex point with $h(z)=0$ and all $g_j(z)=0$, and suppose its underlying point $x$ is not in $S$. Then $x\in Z$; pick $t\in T$ with $t\rightsquigarrow x$. If $t\in S$ then $x=t$, excluded. Otherwise $q\notin\mathfrak p_t$, so $h\notin\mathfrak p_t$ and $t\in D(h)$, while $x\notin D(h)$; by (β) the coheight of $t$ is at least $d$, so that of $x$ is at least $d+1$, contradicting the bound $d$. Hence $x\in S$, and then $z\in S$ by <code>pt_inj</code>. For clause 4, fix $y\in S$ and $f_0$ of degree $n$ with $f_0(y)\ne0$. First, $h/f_0=q^2/f_0\in\mathfrak m_y^2$ by Lemma 5, since $q\in V_S(m)$. Second, in the reference chart $D(a)$ the $d$ classes $J_y(g_1),\ldots,J_y(g_d)$ are linearly independent in the $d$-dimensional range of $J_y$, hence span it (<code>Submodule.eq_of_le_of_finrank_eq</code>). Since the range is the image of $\mathfrak m_y$, every $u\in\mathfrak m_y$ satisfies $u\equiv\sum_jb_j\,g_j/a$ modulo $\mathfrak m_y^2$, that is, $\mathfrak m_y\subset(g_1/a,\ldots,g_d/a)+\mathfrak m_y^2$ in $\Gamma(X,D(a))$. Finally the denominator is changed from $a$ to $f_0$ (<code>EtProj.span_ratio_of_span_ratio</code> at line 612): if the spanning relation holds in $\Gamma(X,D(a))$ for a point $y\in D(a)\cap D(f_0)$, it holds in $\Gamma(X,D(f_0))$ for the ratios $g_j/f_0$. Classically, on $D(a)\cap D(f_0)$ one has $g_j/f_0=(g_j/a)\cdot(a/f_0)$ with $a/f_0$ a unit near $y$, and both rings have the same local ring at $y$; the [change of denominator](#changing-the-denominator-in-cotangent-generation) proves the section-ring transport by extension to the overlap and contraction. $\square$

**The actual consumer [Lean, read].** The statement is consumed once, at line 99 of <code>exists_transversal_forms_first_separate</code>, the proof of Lemma 2 of the [previous subsection](#from-a-general-projection-to-a-reduced-origin-fibre). Its four clauses are used as follows.

- Clause 1 (<code>hgen</code>, line 119): for each $j$ at most one $c\in\mathbb C$ makes $g_j+ch$ vanish at the generic point, since two such values would force $h$ and then $g_j$ to vanish there.
- Clause 2 (<code>hgS</code>, line 202), together with $h(y)=0$ extracted from clause 4 at line 197: each translate $F_j=g_j+c_jh$ vanishes on $S$, so $S$ lies over the origin.
- Clause 3 (<code>hbase</code>, lines 163–171, used at 188 and 225): a complex point where $h$ and all $F_j$ vanish lies in $S$, because $g_j=F_j-c_jh$. At line 188 this shows that the denominator $f_0$, chosen to avoid $S$ and the finitely many transversal zeros, avoids every common zero of the $F_j$. At line 225 it shows that a common zero of the $F_j/f_0$ outside $S$ lies in $D(h)$, where the Sard step applies.
- Clause 4 (<code>hjet</code>, lines 197 and 211–221): at $y\in S$, from $\mathfrak m_y\subset(g_j/f_0)+\mathfrak m_y^2$ and $g_j/f_0=F_j/f_0-c_j\,h/f_0$ with $h/f_0\in\mathfrak m_y^2$ (<code>fRatio_add_smul</code>), one gets $\mathfrak m_y\subset(F_j/f_0)+\mathfrak m_y^2$. This is the transversality of the translated forms at the points of $S$, for the denominator $f_0$ that the consumer picks only after $g$ and $h$.

The last item is why the quantifier order in clause 4 matters. The consumer chooses $f_0$ after the Sard translation, depending on the finite set of transversal zeros of $F_1,\ldots,F_d$, which depends on $g$ and $h$. Had the jet clause been proved in one chart only, the consumer would have had to repeat the jet construction in the chart $D(f_0)$.

**Remark (which bridge the archive uses) [Expository].**

- *From local functions to forms.* The transport from $u\in\Gamma(X,D(g_0))$ to a form is Lemma 3(a): the chart ring is generated by the $N+1$ ratios $X_l/g_0$, so modulo $\mathfrak m_y^2$ a vanishing function is a linear combination of $X_l/g_0-e(X_l/g_0)$, and the numerator is a linear form. This uses only that $\iota$ is a closed immersion. It replaces the choice of local coordinates by the global coordinates of $\mathbb P^N$.
- *From one point to all of $S$.* Lemma 3(b) and (c) multiply by a form $w$ that kills $S\setminus\{y\}$ and is a unit at $y$, then rescale. The jet at $y$ is unchanged modulo $\mathfrak m_y^2$ because $1-t_w/e(t_w)\in\mathfrak m_y$. There is no Chinese remainder isomorphism and no Serre vanishing in the archive's proof; the degree $k\ge|S|-1$ of $w$ is the cost.
- *From several conditions to one form.* The simultaneous choice of $c_{k+1}$ is the lemma that a finite-dimensional vector space over an infinite field is not a finite union of proper subspaces. The subspaces are of two kinds: forms vanishing at a given point of $X$ (the generic point, or the generic points of the components of the previous zero locus), and forms whose jet at $y\in S$ lies in the span of the previous jets. The Stacks Project uses the same fact inline in the proof of [0B58](https://stacks.math.columbia.edu/tag/0B58).
- *From dimension counting to the base locus.* The base-locus clause is proved without Bertini and without any statement about general members of a linear system. It is a coheight count: each new form is chosen to be a non-zero-divisor at the generic points of the previous zero locus, so the coheight of a point in the new zero locus goes up by one, and after $d+1$ forms it would exceed $d$. The classical content is that a strict specialization raises the dimension of the local ring ([Stacks 0A21](https://stacks.math.columbia.edu/tag/0A21), part (9)).
- *The degree.* Lemma 2 needs degree $\ge|S|$, Lemma 3(c) adds one for the linear factor, and the square $h=q^2$ doubles the degree of $q$. The archive takes $m=|S|+1$ so that $n=2m\ge2$ even when $S$ is empty, and $k=n-1\ge|S|$. The examples show that this uniform bound is not sharp: on $\mathbb P^1$ two points need only $n=2$ (and $n=4$ if $h\ne0$ is required), and on the cubic $n=2$ suffices for the two chosen points. Serre vanishing would give existence for all large $n$ with no explicit bound ([Stacks 01YS](https://stacks.math.columbia.edu/tag/01YS), part (4), and the separation of tangent vectors in [0E8T](https://stacks.math.columbia.edu/tag/0E8T)).

**Remark (where each hypothesis is used) [Expository].**

- *Closed immersion.* Lemma 1 and Lemma 3(a) need the ratios $X_l/g_0$ to generate the chart ring.
- *Smoothness.* Lemma 4 needs $\dim\mathfrak m_y/\mathfrak m_y^2=d$ at every $y\in S$; Step 3 needs the range of $J_y$ to have dimension exactly $d$ so that $k<d$ conditions leave a proper subspace; the coheight bound $\le d$ is the dimension of $X$.
- *Integrality.* Clause 1 refers to the generic point; the exclusion $\xi\notin S$ for $d>0$ uses that a section vanishing at the generic point is zero.
- *The field $\mathbb C$.* Its infinitude is used in the avoidance of finitely many proper subspaces and in the choice of $g_0$. Its algebraic closedness enters only through the notion of complex point, since the points of $S$ are $\mathbb C$-points. Characteristic zero is not used in this node.
- *Projectivity.* It supplies the forms, the Noetherian property of $X$, and the affine charts $D(g_0)$.

**Remark (what is and is not claimed) [Expository].**

- The theorem does not say that $g_1,\ldots,g_d$ have no common zero outside $S$; that is false for $d$ forms on a $d$-fold. It says that the $d+1$ forms $h,g_1,\ldots,g_d$ have none, and it says nothing about transversality at points outside $S$. Transversality there comes from the Sard translation of the previous subsection.
- The construction is explicit up to the choices "outside finitely many proper subspaces". Nothing is said about general members of a linear system; the forms are special along $S$.
- The following are used at their statements and not read here: the cotangent basis <code>CotDim.exists_cotangent_basis</code>, the coheight bound <code>AffineCover.coheight_le_of_smooth</code>, the algebra lemma <code>exists_linear_mod_sq</code>, and the linearity of ratios <code>fRatio_linear</code>. The finite projection keeps the level recorded in the previous subsection; the Sard step is read in the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets).

**Reading the formal proof.** Paths are relative to the root of archive A2 (Lean 4.33.1, joined SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>, Mathlib pinned at <code>0df444a360eaa60ab8c11dca51a86af692955474</code>).

| Node | A2 path and lines | Role and reading |
|---|---|---|
| <code>exists_forms_vanishing_complexPoints_fullJets</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFormsVanishingComplexPointsFullJetsStatement.lean:8–21</code> | Exported statement; delegates to <code>EtProj.Jets.exists_jet_forms</code>. R3 [Lean, read]. |
| <code>EtProj.Jets.exists_jet_forms</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFormsVanishingComplexPointsFullJets.lean:440–638</code> | The theorem: set-up 453–470, Step 1 471–482, Step 2 483–500, generic point 501–508, induction 509–569, Step 4 570–582, clauses 583–638. R3 [Lean, read]. |
| <code>ev_ratio_eq_zero_iff</code>, <code>frac_smul_n</code>, <code>fRatio_add_n</code>, <code>fRatio_smul_n</code>, <code>rat</code>, <code>rat_sub_const</code>, <code>basicOpen_app_frac</code>, <code>ratio_sq_mem</code> | same file, <code>:23–134</code> | Ratio calculus and Lemma 5. R3 [Lean, read]. |
| <code>eq_of_specializes</code>, <code>eq_zero_of_generic</code>, <code>pt_inj</code>, <code>exists_lin_sep</code>, <code>exists_sep</code> | same file, <code>:141–255</code> | Lemmas 1 and 2 and the point lemmas. R3 [Lean, read]. |
| <code>exists_lin_mul</code>, <code>exists_form_jet</code> | same file, <code>:262–338</code> | Lemma 3(b), (c). R3 [Lean, read]. |
| <code>vanS</code>, <code>mem_vanS</code>, <code>vanAt</code>, <code>evS</code>, <code>sqI</code>, <code>jet</code>, <code>jet_range</code> | same file, <code>:349–431</code> | Definitions and Lemma 4. R3 [Lean, read]. |
| <code>RatSpan.adjoin_fRatio_eq_top</code>, <code>RatSpan.ratio_span_cotangent</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AlgebraMapBasicOpen.lean:164–182,185–191</code> | Generation of the chart ring and Lemma 3(a). R3 [Lean, read]; <code>exists_linear_mod_sq</code> (<code>:17–20</code>) at statement level. |
| <code>Generic.lin</code>, <code>lin_mem</code>, <code>exists_X_notMem</code>, <code>exists_finite_gen</code>, <code>coheight_step</code>, <code>ev₀</code>, <code>fr</code>, <code>vv</code>, <code>Lm</code>, <code>ev₀_algebraMap</code>, <code>mkQ_eq_mkQ</code>, <code>Lm_apply'</code>, <code>Lm_apply</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsGenericForms.lean:21–121</code> | Component generic points, the coheight step, and the cotangent bookkeeping. R3 [Lean, read]; <code>fRatio_linear</code> at statement level. |
| <code>fOpen</code>, <code>fRatio</code>, <code>fRatio_self</code>, <code>mem_fOpen</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FRatioSelf.lean:16–29</code> | Definitions. Read. |
| <code>CxPts</code>, <code>ptsIn</code>, <code>ev</code>, <code>mem_ptsIn</code>, <code>evHom</code>, <code>ev_eq</code>, <code>mem_ptsIn_basicOpen</code> | <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/DetJacMatCoordsEqTransitionJacobianDet.lean:22,41–43,57,71–73,100–102</code> | Complex points and evaluation. Definitions read. |
| <code>CotDim.exists_cotangent_basis</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsCotangentBasis.lean:108–112</code> | Cotangent basis at a complex point of an affine open. Statement level [Lean]. |
| <code>AffineCover.coheight_le_of_smooth</code> | <code>src/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RingKrullDimLeOfQuasiFinite.lean:157–158</code> | Coheight at most $d$. Statement level [Lean]. |
| <code>EtProj.exists_form_genericPoint_cxPts</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsProjFormNonvanishingGenericPointComplexPoi.lean:32–34</code> | Form avoiding the generic point and $S$. R3 [Lean, read] in the [denominator and open-cover proof](#choosing-the-denominator-and-detecting-the-open-cover). |
| <code>EtProj.span_ratio_of_span_ratio</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/RatioSpanCotangentChangeDenominator.lean:47–138</code> | Change of denominator in the spanning clause. See the [change of denominator](#changing-the-denominator-in-cotangent-generation), scoped R3 [Lean, read]. |
| Actual call | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFormsTransversalAtComplexPoints.lean:99,119,163–171,188,197,202,211–225</code> | Consumer. Body read in the previous subsection; the uses of the four clauses rechecked here. |

Mathlib supplies <code>Submodule.exists_forall_notMem_of_forall_ne_top</code> (<code>Mathlib/Algebra/Module/Submodule/Union.lean:90</code>), <code>linearIndependent_fin_snoc</code> (<code>Mathlib/LinearAlgebra/LinearIndependent/Lemmas.lean:696</code>), <code>Order.coheight_add_one_le</code> (<code>Mathlib/Order/KrullDimension.lean:306</code>), <code>NoetherianSpace.exists_finite_set_isClosed_irreducible</code> (<code>Mathlib/Topology/NoetherianSpace.lean:176</code>), <code>ext_of_apply_closedPoint_eq</code> (<code>Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean:90</code>), <code>isClosedImmersion_of_comp_eq_id</code> (<code>Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:432</code>), <code>germ_injective_of_isIntegral</code> (<code>Mathlib/AlgebraicGeometry/FunctionField.lean:55</code>), <code>MvPolynomial.homogeneousSubmodule_one_pow</code> (<code>Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:194</code>), <code>Submodule.eq_of_le_of_finrank_eq</code> (<code>Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:261</code>), <code>finrank_span_eq_card</code> (<code>Mathlib/LinearAlgebra/Dimension/Constructions.lean:461</code>) and <code>Proj.isAffineOpen_basicOpen</code> (<code>Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:201</code>); all are cited at their statements.

The [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre), the [reduced-fibre trace](#from-the-finite-algebra-trace-to-the-reduced-fibre), the [global boundary](#from-fixed-point-vanishing-to-a-global-čech-boundary) and the [local Koszul weights](#from-a-finite-étale-chart-to-the-local-lefschetz-weight) keep the reading levels recorded there.

#### The Sard step: translation parameters that keep the jets

The [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre) chose its last $d$ forms as translates $F_j=g_j+c_jh$ of the [jet forms](#forms-with-prescribed-jets-at-finitely-many-points) and took one fact about the parameter $c\in\mathbb C^d$ as given: outside a Lebesgue-null set of parameters, every common zero of the $F_j$ in $D(h)$ is transversal. That fact is the statement <code>algebraicSard_shifted_functions_regularZeros</code>, whose producer is <code>GlobalTheory.AlgSard.main</code>. This subsection reads that producer and the bodies behind its three interfaces: <code>null_negEval_of_jacobian_det_eq_zero</code> (one chart), <code>ker_evalComplexPoint_le_span_jacobian</code> (from a Jacobian to the cotangent space) and <code>homeomorph_zeroSet</code> (countability). We explain how the bad parameters become the negatives of critical values, which Jacobian is complex and which is real, why countably many charts suffice, and how the consumer avoids the members that vanish identically while leaving the jets on $S$ untouched. The jet forms, the finite projection and the reduced fibre keep the readings recorded in the previous subsections; the finiteness of the transversal zeros is read in the [next subsection](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes).

**Motivation.** Fix the forms $h,g_1,\ldots,g_d$ supplied by the jet theorem. On the affine open $D(h)$ the ratios $\gamma_j=g_j/h$ are regular functions, and for every $c\in\mathbb C^d$
$$
\frac{F_j}{h}=\frac{g_j}{h}+c_j\qquad\text{on }D(h).
$$
So the common zeros of $F_1,\ldots,F_d$ in $D(h)$ are the complex points $z$ with $\gamma(z)=-c$, where $\gamma=(\gamma_1,\ldots,\gamma_d)$: they form the fibre $\gamma^{-1}(-c)$. Such a zero is transversal exactly when the differential of $\gamma$ at $z$ is invertible. The parameters to avoid are therefore the negatives of the critical values of $\gamma$. The sign is part of the statement: the archive's null set is made of the values $-\gamma(z)$ at critical points $z$.

Three gaps separate this observation from a proof.

- *Sard's theorem concerns maps between real spaces.* The complex points of $D(h)$ need charts in which $\gamma$ is holomorphic, and the measure must be Lebesgue measure on $\mathbb C^d=\mathbb R^{2d}$.
- *Charts are local.* Null sets obtained chart by chart add up to a null set only if countably many charts suffice.
- *Transversality is algebraic.* The consumer needs $\mathfrak m_z\subset(F_1/h,\ldots,F_d/h)+\mathfrak m_z^2$, an inclusion of ideals of $\Gamma(X,D(h))$. It has to be derived from the nonvanishing of an analytic Jacobian determinant.

The jets on $S$ need no new argument. The form $h$ vanishes to second order on $S$, so $S$ lies outside $D(h)$, and adding $c_jh$ does not change the first-order jet of $g_j$ at a point of $S$. The two examples below show the mechanism and the sign.

**Example (critical values of a cubic polynomial) [Expository].** Take $X=\mathbb A^1_{\mathbb C}$, $d=1$, $U=X$ and $\varphi=f(t)=t^3-3t+1$. The identity is a chart, with the étale coordinate $t$, and the chart Jacobian of $\varphi$ at $z$ is the $1\times1$ matrix $f'(z)=3z^2-3$.

- *Critical points and values.* $f'(z)=0$ exactly at $z=\pm1$, and $f(1)=-1$, $f(-1)=3$.
- *The bad parameters are the negatives.* The zeros of $f+c$ form $f^{-1}(-c)$. For $c=1$, $f+1=(t-1)^2(t+2)$; for $c=-3$, $f-3=(t+1)^2(t-2)$. The discriminant of $t^3-3t+(1+c)$ is $27(1-c)(3+c)$, so $1$ and $-3$ are the only parameters with a repeated zero. The critical value $-1$ itself is a harmless parameter: $f-1=t(t^2-3)$ has three simple zeros.
- *Transversality as an ideal inclusion.* For $c=-1$ and $z=0$ we have $t=-\tfrac13(f-1)+\tfrac13t^3$, so $t\in(f-1)+\mathfrak m_0^2$ and $\mathfrak m_0=(t)$ is contained in $(f-1)+\mathfrak m_0^2$. For $c=1$ and $z=1$ we have $f+1\in\mathfrak m_1^2=((t-1)^2)$, so $(f+1)+\mathfrak m_1^2=\mathfrak m_1^2$, which does not contain $t-1$.
- *Real and complex Jacobians.* Write $t=\xi+i\eta$, $f=u+iv$ and $f'=\alpha+i\beta$. By the Cauchy–Riemann equations the real Jacobian matrix of $(\xi,\eta)\mapsto(u,v)$ is $\begin{pmatrix}\alpha&-\beta\\ \beta&\alpha\end{pmatrix}$, of determinant $\alpha^2+\beta^2=|f'|^2$. At $z=1+i$ we get $f'(z)=-3+6i$ and the real matrix $\begin{pmatrix}-3&-6\\ 6&-3\end{pmatrix}$, of determinant $45=|f'(z)|^2$. At $z=1$ both vanish.
- *In the consumer's setting.* On $\mathbb P^1$ with $t=x_0/x_1$ and $S=\varnothing$, the forms $h=x_1^3$ and $g=x_0^3-3x_0x_1^2+x_1^3$ satisfy the four clauses of the jet theorem: $g$ is not identically zero, $h$ and $g$ have no common zero because $g(1:0)=1$, and the clauses at $S$ are empty. Here $D(h)$ is the affine line and $g/h=f$. No $c$ makes $g+ch$ vanish identically, so the archive puts $a_1=0$ (see the consumer below) and chooses $c$ outside a null set containing $1$ and $-3$, and with $c\ne0$. The value $0$ would be harmless, since $f$ has discriminant $81$, but it is avoided anyway.

For the identity chart, the null set $N_e$ of Lemma 3 below is exactly $\{1,-3\}$: the chart is all of $\mathbb C$, the auxiliary map is $H(w)=-f(w)$, and its real derivative is singular exactly at $w=\pm1$. The archive chooses its charts abstractly, so its own null set contains $\{1,-3\}$ and may be larger by a null set (see the remarks).

**Example (the plane cubic with parameter $c$) [Expository].** Return to the cubic $E\subset\mathbb P^2$ given by $y^2z=x^3-xz^2$, with $S=\{P_0\}$, $g=y$ and $h=x$, as in the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre). The line $x=0$ meets $E$ at $P_0=(0:0:1)$ twice and at the flex $O=(0:1:0)$, so $D(h)=E\setminus\{P_0,O\}$. This open lies in the chart $z=1$, where $E$ is $\Phi=y^2-x^3+x=0$ and $\varphi=g/h=y/x$.

- *Two étale charts cover $D(h)$.* On $U_1=D(h)\cap\{y\ne0\}$ the coordinate $x$ is étale, because $\partial\Phi/\partial y=2y$ is a unit. On $U_2=D(h)\cap\{3x^2\ne1\}$ the coordinate $y$ is étale, because $\partial\Phi/\partial x=1-3x^2$ is a unit. A point of $D(h)$ with $y=0$ has $x=\pm1$, where $3x^2-1=2$; hence $U_1\cup U_2=D(h)$.
- *The chart Jacobians.* Implicit differentiation along $E$ gives
  $$
  \frac{d\varphi}{dx}=\frac{x^2+1}{2xy}\ \text{ on }U_1,\qquad \frac{d\varphi}{dy}=\frac{x^2+1}{x(3x^2-1)}\ \text{ on }U_2 .
  $$
  On $U_1\cap U_2$ the two differ by the unit factor $dx/dy=2y/(3x^2-1)$: the Jacobian depends on the chart, its vanishing does not. At the two points $(\pm1,0)$ of $U_2\setminus U_1$ the second Jacobian equals $\pm1$.
- *Critical points and values.* Both Jacobians vanish exactly where $x^2=-1$, at the four points $(i,\pm(1-i))$ and $(-i,\pm(1+i))$. The values of $\varphi$ there are $\mp(1+i)$ and $\pm(i-1)$, the four roots of $s^4=-4$. This set is symmetric under $s\mapsto-s$, so the bad parameters $c=-s$ are again the roots of $c^4=-4$, the branch values found in the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre); here the sign is invisible.
- *Zeros of the translate.* The equation $\varphi+c=0$ means $y=-cx$. Substituting gives $x(x^2-c^2x-1)=0$ with $x\ne0$, and the quadratic has discriminant $c^4+4$. For $c=1+i$ it becomes $(x-i)^2$, with the single point $Q=(i,1-i)$ and $\varphi(Q)=-1-i=-c$. There $d\varphi/dx=0$ and $d^2\varphi/dx^2=1/y(Q)=(1+i)/2\ne0$, so $\varphi+c$ vanishes to order exactly two in the local coordinate $x-i$. This matches the fibre ring $\mathbb C\times\mathbb C[\varepsilon]/(\varepsilon^2)$ found in that subsection. For $c=1$ the zeros satisfy $x^2=x+1$, and there $d\varphi/dx=-(x+2)/(2(x+1))\ne0$, so both are transversal.
- *The jets at $S$.* Since $P_0\notin D(h)$, the Sard step says nothing about $P_0$. On $E$ we have $x=x^3-y^2$, so $x\in\mathfrak m_{P_0}^2$, and every $F_c/z=y+cx$ has the jet $y$ at $P_0$.
- *The excluded hyperplane.* No $c$ makes $y+cx$ vanish identically on $E$, so $a_1=0$. The archive chooses $c\ne0$ outside a null set that contains the four roots of $c^4=-4$; for transversality on $D(h)$ any $c$ with $c^4\ne-4$ would do.

All assertions in both examples, and in the characteristic-$p$ example below, are exact identities over $\mathbb Q(i)$ or $\mathbb F_p$, checked by `check_sard_shifts.py` in the run directory (119 assertions in its Parts A–C).

**Definitions.**

- *Complex points and their topology.* $X$ is a scheme over $\mathbb C$. A complex point is a $\mathbb C$-morphism $\operatorname{Spec}\mathbb C\to X$ (<code>CxPts p (RingHom.id ℂ)</code>). For an open $U$, $U(\mathbb C)$ is the set of complex points landing in $U$ (<code>ptsIn</code>), and $f(z)$ is the value of $f\in\Gamma(X,U)$ at $z\in U(\mathbb C)$ (<code>ev</code>, <code>evHom</code>). Morphisms $\operatorname{Spec}\mathbb C\to X$ carry the topology generated by the sets $\{z\in U(\mathbb C):f(z)\in O\}$, for $U$ open, $f\in\Gamma(X,U)$ and $O\subset\mathbb C$ open (<code>topology</code>, <code>basicSet</code>); complex points carry the subspace topology. Taking $f=1$ and $O=\mathbb C$ shows that each $U(\mathbb C)$ is open (<code>isOpen_ptsIn</code>), so this is the coarsest topology in which every $U(\mathbb C)$ is open and every regular function is continuous on it. For an algebraic variety in Serre's sense, which is separated, the Remark after Proposition 2 of GAGA describes the analytic topology as the coarsest one making the regular functions on Zariski-open sets continuous ([GAGA, §2, no. 5, pp. 8–9](https://doi.org/10.5802/aif.59)). The archive does not assume $X$ separated, and then the openness of the $U(\mathbb C)$ has to be part of the description. On the affine line with a doubled origin, pull back the topology of $\mathbb C$ along the map that identifies the two origins. A regular function defined near both origins takes the same value at them, so every regular function is continuous on its domain for this topology; but neither copy of $\mathbb A^1(\mathbb C)$ is open.
- *Algebraic charts.* An algebraic chart of dimension $d$ (<code>AlgChart p (RingHom.id ℂ) d</code>) consists of three pieces of data. First, an affine open $U$. Second, sections $x_1,\ldots,x_d\in\Gamma(X,U)$ such that $\mathbb C[T_1,\ldots,T_d]\to\Gamma(X,U)$, $T_a\mapsto x_a$, is étale. Third, a homeomorphism $e$ from an open set of complex points onto an open subset of $\mathbb C^d$. The conditions are: the source of $e$ lies in $U(\mathbb C)$; $e(z)=(x_1(z),\ldots,x_d(z))$; and for every open $W$ and every $f\in\Gamma(X,W)$, the function $f\circ e^{-1}$ is holomorphic on the part of the target that $e^{-1}$ sends into $W(\mathbb C)$.
- *The chart Jacobian.* For $\varphi_1,\ldots,\varphi_d\in\Gamma(X,W)$ and $z$ in the source of $e$ and in $W(\mathbb C)$, $J_\varphi(z)$ is the complex $d\times d$ matrix with entries $\partial(\varphi_a\circ e^{-1})/\partial w_b$ at $e(z)$ (<code>jacMat</code>). It is the holomorphic Jacobian of $\varphi$ in the coordinates $x_1,\ldots,x_d$. We call $z$ *critical* for $\varphi$ in the chart if $\det J_\varphi(z)=0$.
- *The measure.* The parameter space is $\mathbb C^d$ (<code>Fin d → ℂ</code>) with the measure <code>volume</code>, the product of the Lebesgue measures of the factors $\mathbb C\cong\mathbb R^2$. It is an additive Haar measure on the real vector space $\mathbb C^d\cong\mathbb R^{2d}$, so "null" means Lebesgue-null in $\mathbb R^{2d}$. Only the outer measure is required to vanish; a null set need not be measurable.
- *Transversal common zero.* As in the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre): $\psi_1,\ldots,\psi_d$ vanish at $z$ and $\mathfrak m_z\subset(\psi_1,\ldots,\psi_d)+\mathfrak m_z^2$, where $\mathfrak m_z$ is the kernel of evaluation at $z$. A constant $c\in\mathbb C$ stands for the section $c\cdot1$ (<code>algX p U c</code>).

**Theorem (Sard's lemma for shifted functions) [Lean, read].** Let $X$ be a scheme, smooth of relative dimension $d$ over $\mathbb C$, let $U\subset X$ be an affine open, and let $\varphi_1,\ldots,\varphi_d\in\Gamma(X,U)$. There is a set $N\subset\mathbb C^d$ of Lebesgue measure zero with the following property. If $c\notin N$ and $z\in U(\mathbb C)$ satisfies $\varphi_j(z)+c_j=0$ for all $j$, then
$$
\mathfrak m_z\subset(\varphi_1+c_1,\ldots,\varphi_d+c_d)+\mathfrak m_z^2\qquad\text{in }\Gamma(X,U).
$$
The set $N$ built in the proof (the archive's <code>E</code>) contains $-\varphi(z)$ whenever $z\in U(\mathbb C)$ is critical for $\varphi=(\varphi_1,\ldots,\varphi_d)$ in one of the charts used. Classically, criticality does not depend on the chart, because two chart Jacobians differ by the invertible Jacobian of the transition map; so these are the negatives of all critical values of $\varphi$. The proof itself never compares charts. The set may contain further points (see the remarks), which does no harm.

This is <code>GlobalTheory.AlgSard.main</code>; the exported statement <code>algebraicSard_shifted_functions_regularZeros</code> is the same sentence and delegates to it. Integrality, projectivity, separatedness and quasi-compactness of $X$ are not assumed. The affineness of $U$ is what makes the countability argument work. We prove four lemmas, all read in the archive.

**Lemma 1 (the complex points of an affine piece form a closed algebraic subset of $\mathbb C^k$) [Lean, read].** Let $U\subset X$ be affine with $\Gamma(X,U)$ a finitely generated $\mathbb C$-algebra. Choose a surjection $\pi:\mathbb C[T_1,\ldots,T_k]\to\Gamma(X,U)$ of $\mathbb C$-algebras and a finite set $G$ generating $\ker\pi$. Then
$$
\kappa:U(\mathbb C)\to Z(G)=\{w\in\mathbb C^k:P(w)=0\text{ for all }P\in G\},\qquad \kappa(z)=\bigl(\pi(T_1)(z),\ldots,\pi(T_k)(z)\bigr),
$$
is a homeomorphism. In particular $U(\mathbb C)$ is second countable.

*Proof.* This is <code>homeomorph_zeroSet</code>. The set $G$ exists because $\mathbb C[T_1,\ldots,T_k]$ is Noetherian (Hilbert's basis theorem). For $z\in U(\mathbb C)$, evaluation at $z$ composed with $\pi$ is the evaluation $P\mapsto P(\kappa(z))$, since both are $\mathbb C$-algebra maps that agree on the variables (<code>evHom_comp</code>). Hence $P(\kappa(z))=\pi(P)(z)=0$ for $P\in G$, and $\kappa(z)\in Z(G)$.

Conversely, let $w\in Z(G)$. Evaluation at $w$ kills $G$, hence $\ker\pi$, so it factors through $\pi$ as a ring map $\Gamma(X,U)\to\mathbb C$ that is the identity on constants (<code>homAt</code>, <code>homAt_comp</code>). Because $U$ is affine, this map is evaluation at the complex point $s(w):\operatorname{Spec}\mathbb C\to\operatorname{Spec}\Gamma(X,U)\cong U$ (<code>ofHom</code>, <code>ev_ofHom</code>). The coordinates of $s(w)$ are $\pi(T_i)(s(w))=T_i(w)=w_i$, so $\kappa(s(w))=w$. Also $s(\kappa(z))=z$: every section is some $\pi(P)$, both points give it the value $P(\kappa(z))$, and a complex point of the affine $U$ is determined by its values on $\Gamma(X,U)$ (<code>ext_of_valR</code>).

The map $\kappa$ is continuous because sections are continuous on $U(\mathbb C)$ (<code>continuousOn_ev</code>). For $s$, convergence to a point of the affine $U$ may be tested on the constants together with a set of ring generators of $\Gamma(X,U)$ (<code>PtsOver.tendsto_iff_of_generators</code>). Indeed, values of sums and products converge when the values of the factors do (<code>tendsto_valR_of_closure</code>), and convergence of all values on $U$ implies convergence of the points, because a neighbourhood $D(r)\subset V\cap U$ can be chosen and the values of $a/r^n$ converge where $r$ is a unit (<code>tendsto_of_isAffineOpen</code>). Here the generators are the $\pi(T_i)$, whose values at $s(w)$ are the coordinates $w_i$, which depend continuously on $w$. Finally, $Z(G)$ is a subspace of $\mathbb C^k$, which is second countable, and second countability passes along homeomorphisms (Mathlib's <code>Homeomorph.secondCountableTopology</code>). $\square$

**Lemma 2 (countably many charts cover an affine piece) [Lean, read].** Let $X$ be smooth of relative dimension $d$ over $\mathbb C$ and let $U\subset X$ be affine. There is a countable set $\mathcal A$ of algebraic charts of dimension $d$ whose sources cover $U(\mathbb C)$.

*Proof.* This is <code>countable_charts</code>. Smoothness gives local finite type, and $U$ is affine over the affine base $\operatorname{Spec}\mathbb C$, so $\Gamma(X,U)$ is a finitely generated $\mathbb C$-algebra (<code>LocallyOfFiniteType.finiteType_of_affine_subset</code>, composed with the isomorphism $\Gamma(\operatorname{Spec}\mathbb C)\cong\mathbb C$). By Lemma 1, $U(\mathbb C)$ is second countable. Every complex point lies in the source of some chart (<code>AlgChart.exists_mem_source</code>, discussed next). The traces of the chart sources on $U(\mathbb C)$ form an open cover of a second countable space, so countably many of them already cover it (<code>TopologicalSpace.isOpen_iUnion_countable</code>, the Lindelöf property). $\square$

The existence of charts has two parts, both read (<code>exists_etale_coords</code>, <code>exists_of_etale</code>). First, smoothness of relative dimension $d$ gives, around every point, an affine open on which the structure map is standard smooth, and then $d$ sections forming an étale map to $\mathbb A^d$ (Mathlib's <code>RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial</code>, a corollary of <code>Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial</code>; classically [Stacks Project, Lemma 29.37.21](https://stacks.math.columbia.edu/tag/054L)). Second, at a complex point the étale coordinates have a holomorphic local inverse whose composite with every section is holomorphic. This is a holomorphic implicit function theorem for étale algebras (<code>EtaleFamily.exists_holomorphic_sections</code>, read in [holomorphic local sections](#holomorphic-local-sections-of-étale-families)), followed by the passage from holomorphy on the affine $U$ to holomorphy of every section on every open (<code>CxPts.holo_of_affine</code>, read: write a section on a basic open as $a/r^n$). Classically, these charts express that a smooth point of a complex variety is a manifold point of the associated analytic space. In GAGA a point of an analytic space is *simple* when the space is isomorphic to $\mathbb C^n$ near it, equivalently when its analytic local ring is regular ([GAGA, §1, no. 4, p. 6](https://doi.org/10.5802/aif.59)), and the algebraic and analytic local rings of a variety have the same completion (§2, no. 6, Proposition 3, pp. 9–10). Serre's own *algebraic charts* are a different notion. They are biregular isomorphisms of Zariski-open sets onto locally closed subsets of an affine space, possibly singular, and Proposition 2 of §2, no. 5 (p. 8) makes them analytic using only that polynomials are holomorphic (Lemma 1 there), with no implicit function theorem. In this subsection they correspond to the embedding of Lemma 1, not to <code>AlgChart</code>.

**Lemma 3 (in one chart, the negatives of critical values form a null set) [Lean, read].** Let $e$ be an algebraic chart of dimension $d$, let $W$ be an open set and let $\varphi_1,\ldots,\varphi_d\in\Gamma(X,W)$. There is a null set $N_e\subset\mathbb C^d$ such that $-\varphi(z)=(-\varphi_1(z),\ldots,-\varphi_d(z))$ lies in $N_e$ for every $z$ in the source of $e$ and in $W(\mathbb C)$ with $\det J_\varphi(z)=0$.

*Proof.* This is <code>null_negEv_of_det_eq_zero</code>. Define $H:\mathbb C^d\to\mathbb C^d$ by $H(w)=-\bigl((\varphi_j\circ e^{-1})(w)\bigr)_j$, using the total functions that the archive attaches to $e^{-1}$ and to evaluation outside their natural domains. Let $\Sigma$ be the set of $w$ at which $H$ is differentiable as a map of real vector spaces with $\det_{\mathbb R}dH(w)=0$, and put $N_e=H(\Sigma)$. The equal-dimension Sard lemma for a Haar measure on a finite-dimensional real space says: if a map is differentiable at every point of a set, with singular derivative there, then the image of that set is null (Mathlib's <code>addHaar_image_eq_zero_of_det_fderivWithin_eq_zero</code>, used at its statement). Applied on $\mathbb C^d\cong\mathbb R^{2d}$, it shows that $N_e$ is null.

Let $z$ be in the source and in $W(\mathbb C)$ with $\det J_\varphi(z)=0$, and put $w=e(z)$. Each $\varphi_j\circ e^{-1}$ is complex differentiable at $w$ (<code>differentiableAt_ev</code>). Hence $H$ is complex differentiable at $w$, with derivative the complex-linear map $M=-J_\varphi(z)$. Since $\det J_\varphi(z)=0$, there is $v\ne0$ in $\mathbb C^d$ with $J_\varphi(z)v=0$ (<code>Matrix.exists_mulVec_eq_zero_iff</code>), so $Mv=0$. The real derivative of $H$ at $w$ is $M$ viewed as a real-linear map of $\mathbb R^{2d}$ (<code>HasFDerivAt.restrictScalars</code>), and $v$ is a nonzero vector in its kernel. So $\det_{\mathbb R}dH(w)=0$ (<code>LinearMap.det_eq_zero_iff_ker_ne_bot</code>), that is, $w\in\Sigma$. Finally $H(w)=-\varphi(e^{-1}(e(z)))=-\varphi(z)$. $\square$

Classically $\det_{\mathbb R}M=|\det_{\mathbb C}M|^2$ for a complex-linear $M$, so the real and complex determinants vanish together. The archive needs only one direction and gets it from a kernel vector, without computing a $2d\times2d$ determinant.

**Lemma 4 (a nonsingular chart Jacobian gives a transversal zero) [Lean, read].**

- (a) *Algebra.* Let $A$ be a $\mathbb C$-algebra, $\chi:A\to\mathbb C$ a ring map that is the identity on $\mathbb C$, and $\mathfrak m=\ker\chi$. Let $\delta_1,\ldots,\delta_d:A\to\mathbb C$ be additive maps with $\delta_b(fg)=\chi(f)\,\delta_b(g)+\chi(g)\,\delta_b(f)$ and $\delta_b(\mathbb C)=0$. Let $\theta_1,\ldots,\theta_d\in A$ be such that every $a\in\mathfrak m$ is congruent modulo $\mathfrak m^2$ to a $\mathbb C$-linear combination of the $\theta_k$. If $\varphi_1,\ldots,\varphi_d\in A$ and the matrix $\bigl(\delta_b(\varphi_a)\bigr)_{a,b}$ is invertible, then $\mathfrak m\subset(\varphi_1-\chi(\varphi_1),\ldots,\varphi_d-\chi(\varphi_d))+\mathfrak m^2$.
- (b) *Geometry.* Let $X$ be smooth of relative dimension $d$ over $\mathbb C$, $U$ affine, $e$ an algebraic chart, and $z$ in the source of $e$ and in $U(\mathbb C)$. If $\varphi_1,\ldots,\varphi_d\in\Gamma(X,U)$ and $\det J_\varphi(z)\ne0$, then $\mathfrak m_z\subset(\varphi_1-\varphi_1(z),\ldots,\varphi_d-\varphi_d(z))+\mathfrak m_z^2$.

*Proof.* (a) is <code>ker_le_span_sup</code>. The Leibniz rule kills $\mathfrak m^2$: for $f,g\in\mathfrak m$ it gives $\delta_b(fg)=0$, and $\delta_b$ is additive. Since $\delta_b$ kills constants, the Leibniz rule also makes it $\mathbb C$-linear. Put $\varphi'_a=\varphi_a-\chi(\varphi_a)\in\mathfrak m$ and choose $C_{ak}\in\mathbb C$ with $\varphi'_a-\sum_kC_{ak}\theta_k\in\mathfrak m^2$. Applying $\delta_b$ gives $\delta_b(\varphi_a)=\delta_b(\varphi'_a)=\sum_kC_{ak}\,\delta_b(\theta_k)$, that is,
$$
\bigl(\delta_b(\varphi_a)\bigr)_{a,b}=C\cdot\bigl(\delta_b(\theta_k)\bigr)_{k,b}.
$$
The left side has nonzero determinant, so $\det C\ne0$. Now let $a\in\mathfrak m$ and choose $\beta\in\mathbb C^d$ with $a-\sum_k\beta_k\theta_k\in\mathfrak m^2$. Let $\lambda=\beta C^{-1}$, a row vector, so that $\sum_j\lambda_jC_{jk}=\beta_k$. Then
$$
a-\sum_j\lambda_j\varphi'_j=\Bigl(a-\sum_k\beta_k\theta_k\Bigr)-\sum_j\lambda_j\Bigl(\varphi'_j-\sum_kC_{jk}\theta_k\Bigr)\in\mathfrak m^2 ,
$$
so $a\in(\varphi'_1,\ldots,\varphi'_d)+\mathfrak m^2$.

(b) is <code>ker_le_span_jac</code>. Take $A=\Gamma(X,U)$, $\chi=\mathrm{ev}_z$, and let $\delta_b(f)$ be the $b$-th partial derivative of $f\circ e^{-1}$ at $e(z)$. It is additive (<code>fderiv_add</code>). It satisfies the Leibniz rule at $z$ (<code>fderiv_mul</code>, together with $e^{-1}(e(z))=z$). It kills constants, because a constant section is locally constant near $e(z)$ on the open set that $e^{-1}$ sends into $U(\mathbb C)$ (<code>isOpen_over</code>, <code>mem_over</code>, <code>ev_algX</code>). The matrix $\bigl(\delta_b(\varphi_a)\bigr)$ is $J_\varphi(z)$ by definition. Smoothness supplies $\theta_1,\ldots,\theta_d\in\mathfrak m_z$ spanning $\mathfrak m_z$ modulo $\mathfrak m_z^2$ (<code>CotDim.exists_cotangent_basis</code>, used at its statement). Now apply (a). $\square$

Only the spanning property of the $\theta_k$ is used. Their independence is not needed, because the invertibility of $J_\varphi(z)$ already forces $\det C\ne0$. Classically, (b) says that $d$ functions whose differentials at $z$ are linearly independent have classes forming a basis of the cotangent space $\mathfrak m_z/\mathfrak m_z^2$, which has dimension $d$ at a smooth point ([Stacks Project, Lemma 10.140.1](https://stacks.math.columbia.edu/tag/00TR) and [Lemma 10.140.3](https://stacks.math.columbia.edu/tag/00TT)).

*Proof of the theorem.* We follow <code>AlgSard.main</code>, lines 49–67.

- *Charts.* Lemma 2 gives a countable set $\mathcal A$ of charts whose sources cover $U(\mathbb C)$.
- *The null set.* For each $e\in\mathcal A$, Lemma 3 with $W=U$ gives a null set $N_e$. Put $N=\bigcup_{e\in\mathcal A}N_e$. A countable union of null sets is null (<code>measure_biUnion_null_iff</code>). This is where countability is used.
- *Transversality.* Let $c\notin N$, and let $z\in U(\mathbb C)$ with $\varphi_j(z)+c_j=0$ for all $j$, so that $c=-\varphi(z)$. Choose $e\in\mathcal A$ whose source contains $z$. If $\det J_\varphi(z)=0$, Lemma 3 gives $c=-\varphi(z)\in N_e\subset N$, a contradiction. Hence $\det J_\varphi(z)\ne0$, and Lemma 4(b) gives $\mathfrak m_z\subset(\varphi_j-\varphi_j(z))_j+\mathfrak m_z^2$. Since $\varphi_j-\varphi_j(z)=\varphi_j+c_j$, this is the claim. $\square$

**The actual consumer [Lean, read].** The statement is used once, at line 101 of <code>exists_transversal_forms_first_separate</code>, the proof of Lemma 2 of the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre). Lines 100–160 run as follows.

1. *The affine open.* $D(h)=\iota^{-1}D_+(h)$ is affine, because $D_+(h)$ is an affine open of $\mathbb P^N$ (Mathlib's <code>Proj.isAffineOpen_basicOpen</code>) and its preimage under the closed immersion $\iota$ is affine (line 100). The theorem is applied with $U=D(h)$ and $\varphi_j=g_j/h$ (line 101).
2. *Members that vanish identically.* For each $j$ at most one $a_j\in\mathbb C$ makes $g_j+a_jh$ vanish at the generic point; if there is none, the archive sets $a_j=0$ (lines 102–122, using clause 1 of the jet theorem).
3. *Choice of $c$.* With $N$ the null set of the theorem, the set $N\cup\bigcup_j\{c:c_j=a_j\}$ is null. Each hyperplane $\{c_j=a_j\}$ is null for the product measure, because points of $\mathbb C$ are null (Mathlib's <code>Measure.pi_hyperplane</code>). The whole space $\mathbb C^d$ is open and nonempty, so its measure is positive (<code>IsOpen.measure_pos</code>). Hence some $c$ avoids the union (lines 123–137).
4. *The translates.* $F_j=g_j+c_jh$ is a form of degree $n$, and $F_j/h=g_j/h+c_j$ on $D(h)$ (lines 138–143, by <code>fRatio_add_smul</code> and $h/h=1$). If $z\in D(h)(\mathbb C)$ and every $F_j$ vanishes at $z$, then every $F_j/h$ vanishes at $z$, so $g_j/h(z)+c_j=0$, and the theorem gives $\mathfrak m_z\subset(F_1/h,\ldots,F_d/h)+\mathfrak m_z^2$ (lines 144–160, <code>htrh</code>).

The jets on $S$ are untouched. Every $y\in S$ satisfies $h/f_0\in\mathfrak m_y^2$ for each admissible $f_0$, so $h(y)=0$ and $y\notin D(h)$ (lines 195–201); the Sard step never looks at $S$. At $y$ the consumer writes $g_j/f_0=F_j/f_0-c_j\,h/f_0$ (lines 211–222), so the $F_j/f_0$ span $\mathfrak m_y/\mathfrak m_y^2$ because the $g_j/f_0$ do; this is clause 4 of the [jet forms](#forms-with-prescribed-jets-at-finitely-many-points). The finiteness of the transversal zeros (line 161) is read in the [next subsection](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes); the choice of $f_0$ (line 162) and the transport of transversality from $F_j/h$ to $F_j/f_0$ off $S$ (line 226) keep the readings of the previous subsections.

**Example (characteristic $p$: a purely inseparable translate) [Expository].** Let $k$ be an algebraically closed field of characteristic $p>0$, let $X=\mathbb P^1_k$ with $t=x_0/x_1$, let $S=\{(0:1)\}$, and put
$$
g=x_0x_1^{\,p},\qquad h=x_0^{\,p+1}.
$$
These forms satisfy the four clauses of the jet theorem, read over $k$; we check them directly. (The archive proves the jet theorem over $\mathbb C$ only. Besides the infinitude of the base field, its proof calls Mathlib's <code>ext_of_apply_closedPoint_eq</code> through <code>pt_inj</code>, at lines 167–169, 330 and 606 of the jet file, and that lemma is stated for an algebraically closed base field. Both properties hold for $k$, but the example does not rest on transporting the proof.) The form $g$ vanishes at $S$ and is not identically zero; $h$ vanishes only at $S$; and in the chart $x_1\ne0$, $g/x_1^{p+1}=t$ is a cotangent basis at $t=0$, while $h/x_1^{p+1}=t^{p+1}\in\mathfrak m^2$. On $D(h)=\{x_0\ne0\}$, with coordinate $u=x_1/x_0$,
$$
\frac gh=u^p,\qquad \frac{d}{du}\,u^p=p\,u^{p-1}=0,
$$
so every point of $D(h)$ is critical and the set of critical values is all of $k$. Indeed, for every $c\in k$, with $b^p=c$,
$$
g+ch=x_0\,(x_1+b\,x_0)^p ,
$$
so besides its transversal zero at $S$, every translate has a $p$-fold zero at $(1:-b)$. No parameter gives a reduced origin fibre. Neither a measure-zero argument nor a Zariski-generic one can rescue the step, because the bad set is everything. Over $\mathbb C$ the same forms give $d(u^p)/du=pu^{p-1}$, with the single critical value $0$, so only $c=0$ is bad.

The failure is exactly inseparability. A morphism of smooth curves has nonzero differential if and only if its function field extension is finite separable, and then it is étale on a nonempty open ([Stacks Project, Lemma 53.12.1](https://stacks.math.columbia.edu/tag/0C1C)). In characteristic $p$ every nonconstant morphism of proper smooth curves factors as a power of the relative Frobenius followed by a separable morphism ([Stacks Project, Proposition 53.13.7](https://stacks.math.columbia.edu/tag/0CD2)). The map $u\mapsto u^p$ is purely inseparable, its differential vanishes identically, and the conclusion of Sard's lemma fails for every parameter. In the archive the step is unavailable for a more basic reason as well: it uses the analytic topology, holomorphic charts and Lebesgue measure, all of which belong to $\mathbb C$.

**Remark (real and complex Jacobians, the sign, and the measure) [Expository].**

- *Two determinants.* The chart Jacobian $J_\varphi$ is complex: it is the matrix of holomorphic partial derivatives, and its determinant decides transversality in Lemma 4. Mathlib's Sard lemma is real: it concerns a map of a finite-dimensional real space to itself and the determinant of the real derivative. Lemma 3 passes from the first to the second through a kernel vector. In the first example the real determinant is $|f'|^2$.
- *The sign.* The archive's null set is built from $-\varphi$, because the consumer's condition is $\varphi_j(z)+c_j=0$. In the first example the critical values are $-1$ and $3$, and the bad parameters are $1$ and $-3$. On the cubic the set of critical values is symmetric, so the sign is invisible there.
- *What is null.* $N$ lives in the parameter space $\mathbb C^d$, not on $X$. It is null for the product Lebesgue measure, and nothing more is claimed: not that it is finite, closed, measurable or algebraic. In both examples it is finite. In general $N$ may contain values that are not negatives of critical values. The map $H$ of Lemma 3 is defined on all of $\mathbb C^d$, and outside the chart target it is built from whatever values the total function $e^{-1}$ takes there. Wherever $H$ happens to be differentiable with singular derivative, its values enter $N_e$ as well. This is harmless, because only the nullness of $N$ and the inclusion of the negative critical values are used.
- *Countability.* A union of null sets over an uncountable family need not be null; $\mathbb C^d$ is the union of its points. So Lemma 2 is not a formality. It uses the affineness of $U$ only through Lemma 1. Serre records the analogous fact for varieties: $X^h$ is covered by finitely many chart domains and is countable at infinity ([GAGA, §2, no. 5, p. 9](https://doi.org/10.5802/aif.59)).

**Remark (where each hypothesis is used) [Expository].**

- *Smoothness of relative dimension $d$.* It gives étale coordinates, hence a chart at every complex point (Lemma 2), and a spanning set of $d$ elements for the cotangent space (Lemma 4(b)). The number of functions equals the dimension, so the chart Jacobian is square.
- *The field $\mathbb C$.* It supplies the analytic topology, the holomorphic implicit functions behind the charts, the Lebesgue measure on $\mathbb C^d$, and the second countability of $\mathbb C^k$. Characteristic zero is never invoked separately, but the analytic method presupposes it, and the characteristic-$p$ example shows that the conclusion fails without it.
- *Affineness of $U$.* It gives a finitely generated coordinate ring (Lemma 1), and complex points of $U$ are determined by their values (<code>ext_of_valR</code>).
- *Not used.* Integrality, projectivity, separatedness and quasi-compactness of $X$, the forms $h$ and $g$, and the set $S$. The theorem concerns any $d$ functions on any affine open of any scheme smooth of relative dimension $d$ over $\mathbb C$.

**Remark (what is and is not claimed) [Expository].**

- The theorem is the equal-dimension case of Sard's theorem, which needs only first derivatives. Sard proved that for a $C^q$ map from a region of $\mathbb R^m$ to $\mathbb R^n$ with $q\ge1$ and $m\le n$, the critical values have $m$-dimensional measure zero ([Sard 1942, p. 883](https://doi.org/10.1090/S0002-9904-1942-07811-6)); here $m=n=2d$. Mathlib's lemma assumes less, namely differentiability at the points of the set, following Fremlin's treatment of the change of variables.
- Nothing is said about the structure of the bad set or about transversality outside $D(h)$. At $S$ transversality comes from the jets, and every other common zero of the $F_j$ lies in $D(h)$ by clause 3 of the jet theorem.
- The following are used at their statements and not read here: the cotangent basis <code>CotDim.exists_cotangent_basis</code>, the basic value lemmas of the point topology (<code>valR_add</code>, <code>valR_mul</code> and their companions), and the Mathlib lemmas listed below. The [change of denominator](#changing-the-denominator-in-cotangent-generation) reads the transport used by the projection. The jet forms keep their previous reading level. The [denominator and open-cover proof](#choosing-the-denominator-and-detecting-the-open-cover) reads the two inputs for choosing $f_0$ and checking coverage; <code>TransvZeros.finite_transv_zeros</code> is read in the [next subsection](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes).

**Reading the formal proof.** Paths are relative to the root of archive A2 (Lean 4.33.1, joined SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>, Mathlib pinned at <code>0df444a360eaa60ab8c11dca51a86af692955474</code>).

| Node | A2 path and lines | Role and reading |
|---|---|---|
| <code>algebraicSard_shifted_functions_regularZeros</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AlgebraicSardShiftedFunctionsRegularZerosStatement.lean:8–14</code> | Exported statement; delegates to <code>GlobalTheory.AlgSard.main</code>. R3 [Lean, read]. |
| <code>GlobalTheory.AlgSard.main</code>, <code>countable_charts</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AlgebraicSardShiftedFunctionsRegularZeros.lean:22–43,49–67</code> | The theorem and Lemma 2. R3 [Lean, read]. |
| <code>T.null_negEval_of_jacobian_det_eq_zero</code>, <code>ChartSard.null_negEv_of_det_eq_zero</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NullNegEvalOfJacobianDetEqZeroStatement.lean:11–15</code>, <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NullNegEvalOfJacobianDetEqZero.lean:13–57</code> | Lemma 3. R3 [Lean, read]. |
| <code>T.ker_evalComplexPoint_le_span_jacobian</code>, <code>JacSpan.ker_le_span_sup</code>, <code>JacSpan.ker_le_span_jac</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/KerEvalComplexPointLeSpanJacobianStatement.lean:11–17</code>, <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/KerEvalComplexPointLeSpanJacobian.lean:16–73,79–116</code> | Lemma 4. R3 [Lean, read]. |
| <code>AffCxPts.homeomorph_zeroSet</code>, <code>coords</code>, <code>evHom_comp</code>, <code>homAt</code>, <code>homAt_comp</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/HomeomorphZeroSet.lean:16–35,41–99</code> | Lemma 1. R3 [Lean, read]. |
| <code>CxPts</code>, <code>ptsIn</code>, <code>ev</code>, <code>isOpen_ptsIn</code>, <code>continuousOn_ev</code>, <code>evHom</code>, <code>ev_algX</code>, <code>ofHom</code>, <code>ev_ofHom</code>, <code>holo_of_affine</code> | <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/DetJacMatCoordsEqTransitionJacobianDet.lean:22,41–51,71–73,94–95,104–118,120–144</code> | Complex points, evaluation, points from ring maps, holomorphy from the affine chart. Definitions and bodies read. |
| <code>AlgChart</code>, <code>differentiableAt_ev</code>, <code>jacMat</code>, <code>exists_of_etale</code>, <code>exists_etale_coords</code>, <code>exists_mem_source</code> | <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/DetJacMatCoordsEqTransitionJacobianDet.lean:150–167,208–214,308–386</code> | Charts, the chart Jacobian, charts at every complex point. Definitions and bodies read. |
| <code>ext_of_valR</code>, <code>basicSet</code>, <code>topology</code>, <code>tendsto_iff</code>, <code>tendsto_valR_of_closure</code>, <code>tendsto_of_isAffineOpen</code>, <code>tendsto_iff_of_generators</code>, <code>PtsOver.tendsto_iff_of_generators</code> | <code>src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemRangeCompIffOfIsClosedImmersion.lean:116–121,181–182,205–207,228–244,366–386,390–418,420–426,428–440</code> | The analytic topology and convergence tested on generators. Definitions and bodies read. |
| <code>isOpen_over</code>, <code>mem_over</code> | <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/ChartMeasApplyOfSubset.lean:20–25</code> | Chart bookkeeping. Read. |
| <code>EtaleFamily.exists_holomorphic_sections</code> | <code>src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolomorphicSections.lean:74–205</code> | Holomorphic implicit functions for étale algebras. See [holomorphic local sections](#holomorphic-local-sections-of-étale-families), scoped R3 [Lean, read]. |
| <code>CotDim.exists_cotangent_basis</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsCotangentBasis.lean:108–112</code> | Cotangent basis at a complex point of an affine open. Statement level [Lean]. |
| Actual call | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFormsTransversalAtComplexPoints.lean:100–162,195–201,211–222,226</code> | Consumer. Body read in the reduced auxiliary projection; the Sard call and the choice of $c$ rechecked here. |

Mathlib supplies <code>addHaar_image_eq_zero_of_det_fderivWithin_eq_zero</code> (<code>Mathlib/MeasureTheory/Function/Jacobian.lean:645</code>), <code>measure_biUnion_null_iff</code> (<code>Mathlib/MeasureTheory/OuterMeasure/Basic.lean:107</code>), <code>TopologicalSpace.isOpen_iUnion_countable</code> (<code>Mathlib/Topology/Bases.lean:914</code>), <code>Homeomorph.secondCountableTopology</code> (<code>Mathlib/Topology/Homeomorph/Lemmas.lean:37</code>), <code>Matrix.exists_mulVec_eq_zero_iff</code> (<code>Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean:163</code>), <code>LinearMap.det_eq_zero_iff_ker_ne_bot</code> (<code>Mathlib/LinearAlgebra/Determinant.lean:359</code>), <code>HasFDerivAt.restrictScalars</code> (<code>Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:56</code>), <code>Algebra.FiniteType.iff_quotient_mvPolynomial''</code> (<code>Mathlib/RingTheory/FiniteType.lean:174</code>), <code>MvPolynomial.isNoetherianRing</code> (<code>Mathlib/RingTheory/Polynomial/Basic.lean:935</code>), <code>LocallyOfFiniteType.finiteType_of_affine_subset</code> (<code>Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:51</code>), <code>RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial</code> and <code>Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial</code> (<code>Mathlib/RingTheory/RingHom/StandardSmooth.lean:253,200</code>), <code>MeasureTheory.Measure.pi_hyperplane</code> (<code>Mathlib/MeasureTheory/Constructions/Pi.lean:409</code>) and <code>IsOpen.measure_pos</code> (<code>Mathlib/MeasureTheory/Measure/OpenPos.lean:47</code>); all are cited at their statements.

The [jet forms](#forms-with-prescribed-jets-at-finitely-many-points), the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre), the [reduced-fibre trace](#from-the-finite-algebra-trace-to-the-reduced-fibre), the [global boundary](#from-fixed-point-vanishing-to-a-global-čech-boundary) and the [local Koszul weights](#from-a-finite-étale-chart-to-the-local-lefschetz-weight) keep the reading levels recorded there.

#### Holomorphic local sections of étale families

**Motivation.** The [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets) needs a coordinate neighborhood of each complex point of a smooth scheme of fixed relative dimension. Its coordinates are values of regular functions, and every other regular function must become holomorphic in these coordinates. An algebraic presentation supplies equations in auxiliary variables. The analytic task is to solve those equations on a neighborhood of a specified solution, with the coefficients and coordinates allowed to vary.

**Example 1 (a finite étale double cover).** Consider $x\mapsto w=x^2$ on $\mathbb C^\times$. Its ring presentation is $\mathbb C[w,w^{-1}][x]/(x^2-w)$, free with basis $1,x$ by monic division. In the quotient $x$ is a unit with inverse $x/w$, so the relative Jacobian $2x$ is a unit. Take $V=\{|w-1|<1/2\}$ and $s(w)=\sum_{k\ge0}\binom{1/2}{k}(w-1)^k$. The series converges for $|w-1|<1$, has square $w$ by the binomial identity and takes value $1$ at $1$. Its real part stays positive on $V$: a purely imaginary square root would have square on the nonpositive real axis, while $\Re w>1/2$. Thus the two source neighborhoods are $U_\pm=\{x:x^2\in V,\ \pm\Re x>0\}$. Every $w\in V$ has exactly one root in each, namely $s_\pm(w)=\pm s(w)$. The forward derivative at $x$ is $2x$, and differentiating $s_\pm(w)^2=w$ gives $s_\pm'(w)=1/(2s_\pm(w))$, with values $\pm1/2$ at $1$.

**Example 2 (a nonlinear two-dimensional chart).** Let $H(x,y)=(x+y,x^2+y)$ at $(1,0)$, whose image is $(1,1)$. Write $(u,v)=H(x,y)$. Then $y=u-x$ and $(2x-1)^2=1+4(v-u)$. On
$$
V=\{(u,v):|u-1|<1/16,\ |v-1|<1/16\}
$$
we have $|4(v-u)|<1/2$. With the positive-real-part branch from Example 1, set $r=s(1+4(v-u))$. The inverse is $x=(1+r)/2$, $y=u-(1+r)/2$. Substitution gives $x+y=u$ and $x^2+y=u+(r^2-1)/4=v$. Conversely on $H^{-1}(V)\cap\{\Re(2x-1)>0\}$ the branch recovers $2x-1$, hence both source coordinates. The forward and inverse derivatives, with the latter evaluated at $(u,v)$ and $x=(1+r)/2$, are
$$
DH=\begin{pmatrix}1&1\\2x&1\end{pmatrix},\qquad
D(H^{-1})=\frac1{1-2x}\begin{pmatrix}1&-1\\-2x&1\end{pmatrix}.
$$
Indeed $dr=2(dv-du)/r$, so $dx=(dv-du)/r$ and $dy=du-dx$. The product of the matrices is the identity, and the forward determinant at $(1,0)$ is $-1$.

**Definitions and algebraic input.** Let $A$ be a commutative ring, $S=A[X_1,\ldots,X_g]$, and $\psi:S\to R$ an étale ring map. Étale means smooth of relative dimension zero. Smoothness means local finite presentation and formal smoothness. The latter is the local lifting property across square-zero thickenings. Equivalently, a smooth morphism is locally of finite presentation, flat, and has geometrically regular fibers. Relative dimension is the dimension of its geometric fibers. In the square presentation used by the archive, $R=S[Y_1,\ldots,Y_k]/(P_1,\ldots,P_k)$ with the determinant of the matrix of auxiliary partial derivatives invertible in $R$. The archive invokes the standard-smooth presentation theorem for the étale algebra. A smooth morphism of fixed relative dimension $d$ has, locally at each point, a standard-smooth presentation with $d$ free coordinates after choosing the variables matched to the relations by an invertible Jacobian minor. This gives an étale coordinate map to relative affine $d$-space over the base. Over $\mathbb C$ these affine neighborhoods provide the charts below. Smoothness refers to the structure map when constructing a chart. An arbitrary map out of that smooth scheme requires its own derivative check. [Stacks Project, square presentation](https://stacks.math.columbia.edu/tag/00U9) · [Smooth local coordinates](https://stacks.math.columbia.edu/tag/039Q)

Let $B\subset\mathbb C^m$ be open, and let $\phi_b:A\to\mathbb C$ be a family of ring maps such that $b\mapsto\phi_b(a)$ is holomorphic on $B$ for every $a$. Let $e:R\to\mathbb C$ extend $\phi_{b_0}$ on $A$, for $b_0\in B$. Write $q=(b,x)\in B\times\mathbb C^g$ and $q_0=(b_0,(e(\psi(X_i)))_i)$. The family of complex solutions consists of pairs $(b,h)$ with $b\in B$ and $h:R\to\mathbb C$ extending $\phi_b$. Give this space the topology tested by $b$ and by evaluations on generators over $A$. It agrees with testing all evaluations, since each element is polynomial in the generators and the coefficient evaluations are continuous. Here the number of auxiliary variables equals the number of relations, while $g$ counts the free coordinates. With constant base $A=\mathbb C$ and $m=0$ this is the affine complex-point topology: further Zariski opens impose local nonvanishing conditions and sections on principal opens are fractions with continuous nonvanishing denominator. This description is local on a scheme. Serre constructs the analytic space of a complex variety using affine polynomial equations and the induced topology. [Serre, GAGA, §2, no. 5, Proposition 2 and the remark following it, pp. 8–9](https://doi.org/10.5802/aif.59)

**Lemma (the parameter-preserving analytic inverse) [Lean, read].** Suppose the coefficients of a finite square system $P$ of polynomial relations in $y$ are holomorphic functions of $q$ near $q_0$. If $M=D_yP(q_0,y_0)$ is invertible, then $F(q,y)=(q,P(q,y))$ is a homeomorphism between open neighborhoods of $(q_0,y_0)$ and $F(q_0,y_0)$, with holomorphic inverse.

*Proof.* Each relation is analytic by polynomial induction. A constant coefficient gives a holomorphic function of $q$ pulled back along the first projection, addition preserves analyticity, and multiplication by a variable multiplies by a holomorphic coordinate. On the line $t\mapsto(q_0,y_0+tv)$ the derivative of the $r$th relation at zero is $\sum_j v_j\partial P_r/\partial y_j(q_0,y_0)$. For a product $Qy_i$ the derivative is $Q(q_0,y_0)v_i+y_{0,i}\sum_j v_j\partial Q/\partial y_j(q_0,y_0)$, which is the polynomial partial derivative formula. The chain rule identifies this line derivative with the full derivative applied to $(0,v)$. Hence, with $C=D_qP(q_0,y_0)$,
$$
DF(q_0,y_0)(h,v)=(h,Ch+Mv),\qquad
DF(q_0,y_0)^{-1}(h,w)=(h,M^{-1}(w-Ch)).
$$
In the archive the rows of the auxiliary matrix index variables via a bijection from the relation indices. The derivative formula is written as row-vector multiplication by this matrix, so nonvanishing of its determinant gives injectivity. The equality of finite dimensions then gives surjectivity. In particular, the determinant concerns the auxiliary block; it requires no invertibility of $C$.

<span id="strict-inverse-chart-for-etale-local-sections"></span>

Analyticity gives a strict derivative at the specified point. The strict-derivative inverse theorem produces an open partial homeomorphism. Shrink its source to the open neighborhood on which $F$ remains analytic and $DF$ remains an isomorphism, using continuity of the derivative and openness of the invertible matrices. At every point of this smaller source the inverse has derivative $DF^{-1}$ evaluated at that source point, where this notation means the inverse linear operator. To see the analytic step in finite dimensions, the real differentiable inverse on these open sets has complex-linear derivative, since $DF$ and its inverse are complex linear. It satisfies the complex differentiability criterion throughout the open target, hence is holomorphic there. The formal body applies the corresponding analytic inverse lemma pointwise on the target of the restricted homeomorphism. This is <code>AnalyticLineDerivative.main</code>, the direct producer invoked by <code>EtaleFamily.exists_local_inverse</code>. $\square$

**Theorem (holomorphic sections of an étale family) [Lean, read].** Under the hypotheses above, there is an open neighborhood $N$ of $q_0$ and a section $q\mapsto\sigma_q:R\to\mathbb C$ with $\sigma_q\circ\psi|_A=\phi_b$ and $\sigma_q(\psi(X_i))=x_i$. Every evaluation $q\mapsto\sigma_q(r)$, for $r\in R$, is holomorphic on $N$. There are finitely many test elements $f_j\in R$ and an open neighborhood $O$ of $(b_0,(e(f_j))_j)$ in the space of their values with the base parameter. For every solution $(b,h)$ having $(b,(h(f_j))_j)\in O$, the pair $q=(b,(h(\psi(X_i)))_i)$ belongs to $N$ and $h=\sigma_q$.

*Proof.* Present $R$ as above and write $y_0=(e(Y_j))_j$, with $Y_j$ now evaluated via their images. Evaluate the coefficients of each relation in $S$ using $\chi_q:S\to\mathbb C$ defined by $\phi_b$ and $X_i\mapsto x_i$. Each coefficient evaluation is holomorphic by polynomial induction. At $(q_0,y_0)$ the relations vanish because the evaluation of the presentation agrees with $e$. The determinant evaluates to a nonzero number because the algebraic determinant is a unit and $e$ is unital. Apply the lemma and write $U,V$ for the open source and target of the resulting inverse.

Set $N=\{q\in B\times\mathbb C^g:(q,0)\in V\}$. This open set contains $q_0$. The inverse at $(q,0)$ has first component $q$, so write it as $(q,y(q))$. The relations vanish at this pair. Evaluation therefore annihilates the ideal generated by all relations and gives a unique ring map $\sigma_q$ on the quotient. This evaluation takes the prescribed values on $A$ and the $X_i$, and every $a\in R$ has a polynomial lift whose evaluation in $\chi_q$ and $y(q)$ is holomorphic. The lift formula also gives $\sigma_{q_0}=e$.

Take the $f_j$ to be the combined list of images of the $X_i$ and $Y_j$. In these coordinates $O$ is $U$ intersected with $b\in B$, with coordinates regrouped as $(b,x,y)$. If $h$ lies in that open test set, its presentation point has image $(q,0)$ under $F$ because all relations evaluate to zero. The inverse identity on $U$ recovers its auxiliary values as $y(q)$. Agreement on coefficients and generators gives $h=\sigma_q$. Conversely every $\sigma_q$ on $N$ lies in that test set by construction from the inverse. Thus projection to $q$ and the section identify the open solution neighborhood with $N$. In the archive the ring-map function is total, with an arbitrary value used away from the zero-slice domain. The section identities and all analytic assertions are on the indicated opens. $\square$

**Remarks.** In <code>AlgChart.exists_of_etale</code> the parameter dimension is $m=0$, $A=\mathbb C$, and $g=d$. Evaluations give the forward coordinate map. The finitely many tests defining $O$ make its source open in the affine complex-point topology. The recovery identity gives the left inverse on this open source. The coordinate identities give the right inverse on the part of $N$ whose section lies in the chosen source. This target is open by continuity of the section. Each affine evaluation composed with the inverse is holomorphic. A regular section on another open is locally a fraction on principal subopens of the affine chart, so its pullback is holomorphic wherever defined. Smoothness of relative dimension $d$ supplies the $d$ étale coordinates at each point. The Sard proof then takes a countable subcover on the affine piece and applies real Sard to the coordinate expression of the $d$ regular functions, viewing source and target as open domains in real dimension $2d$. A singular complex derivative is singular as a real linear map, so its critical values yield a null set of bad translation parameters after negating them. The separate cotangent comparison turns an invertible chart Jacobian into $\mathfrak m_z\subseteq(\varphi_1+c_1,\ldots,\varphi_d+c_d)+\mathfrak m_z^2$, where $\mathfrak m_z$ is the kernel of evaluation in the affine ring. At the projection call, the functions are $g_j/h$ and the parameter is $c$, with the common zero condition $g_j/h=-c_j$. The resulting containment for $F_j/h$ transfers at a common zero in $D(h)\cap D(f_0)$ by the audited same-degree ratio-ideal implication in the [change of denominator](#changing-the-denominator-in-cotangent-generation). For this transfer the immersion is closed, the degree is positive, the numerators and both denominators have that same degree, and the point belongs to both denominator opens. The differential formula at such a zero follows independently from the product rule, since $F_j/f_0=(h/f_0)(F_j/h)$ and $F_j/h$ vanishes there.

If the Jacobian hypothesis is dropped, $x\mapsto x^2$ on $\mathbb A^1_\mathbb C$ at $0$ is a finite map between smooth curves with zero derivative at the branch point. A holomorphic section there would satisfy $s(w)^2=w$, $s(0)=0$ and hence $2s(0)s'(0)=1$, a contradiction. On $\mathbb C^\times$ Example 1 provides local sections at every point by rescaling, but no continuous global section: on the unit circle a putative section has modulus one and the composite with squaring has winding number twice the winding number of the section, whereas the identity has winding number one. The source neighborhood and choice of starting point are therefore essential to the conclusion.

**Reading the formal proof.** In archive A2 (SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>), the new R3 readings are <code>ModuliProofs/ExistsHolomorphicSections.lean:18–205</code> and its direct supplier <code>ModuliProofs/Imports.lean:9–148</code> in <code>src/Development/AbelianVarietyTheory/Proofs/</code>. The former passes from the unit Jacobian to the inverse, descends evaluation through the presentation and proves the finite-test recovery clause. The latter proves the analytic and derivative formulas and constructs the restricted inverse. The standard-smooth presentation theorem, the library strict-derivative and analytic inverse lemmas, and the complex differentiability-to-analyticity interface are used at their statements. The Sard, jet, finite-avoidance and ratio-ideal arguments retain their scoped readings. The comparison of analytic and algebraic sheaves in GAGA and Lean kernel verification are outside this reading.

The [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre) carries the resulting origin fibre into the [local Lefschetz weight](#from-a-finite-étale-chart-to-the-local-lefschetz-weight). The chart inverse here supplies the Sard argument along that route. The weight computation itself uses the cochain, exterior trace and Koszul identities given in its own subsection. See the [source ledger](../sources/SOURCES.md#chapter-12-1244-holomorphic-local-sections-of-étale-families) for the direct calls and the inherited geometric inputs.

#### A positive radius for the inverse series

**Motivation.** The [strict inverse chart used for the étale local sections](#strict-inverse-chart-for-etale-local-sections) supplies the local inverse as a map. To represent it by a convergent series, start with a formal inverse of the expansion of the forward map. An inverse coefficient of degree $n$ is a finite sum, but a convergent inverse needs a single scale that works for every $n$. The order of composition matters for finding that scale. In the left inverse recursion, the degree-$n-1$ inverse coefficient can occur in $n-1$ positions, with one quadratic input and the remaining inputs linear. In the right inverse recursion the same degree can occur only in the two ordered splits $(1,n-1)$ and $(n-1,1)$ for $n>2$. We estimate the right inverse first.

**Example 1 (a scalar quadratic).** Let $f(z)=z+\alpha z^2$ on $\mathbb C$, where $\alpha\ne0$. In the centered inverse $g(w)=\sum_{n\ge1}b_n w^n$, the equation $g+\alpha g^2=w$ gives $b_1=1$ and
$$
b_n=-\alpha\sum_{j=1}^{n-1} b_j b_{n-j}.
$$
In succession this gives $b_2=-\alpha$, $b_3=2\alpha^2$, $b_4=-5\alpha^3$ and $b_5=14\alpha^4$. Writing $b_n=(-\alpha)^{n-1}c_{n-1}$ gives $c_0=1$ and $c_m=\sum_{j=0}^{m-1}c_jc_{m-1-j}$. Thus the formal series $H(t)=\sum_{m\ge0}c_m t^m$ satisfies $H=1+tH^2$. The root with constant term $1$ is $(1-\sqrt{1-4t})/(2t)$, interpreted formally. The coefficient of $t^m$ is
$$
-\frac12\binom{1/2}{m+1}(-4)^{m+1}=\frac{(2m)!}{m!(m+1)!}.
$$
These numbers also count ordered full binary trees with $m$ internal vertices. The two subtrees of the root give the displayed recurrence. Since $c_m\le 4^m$, every $b_n$ satisfies $|b_n|\le(4|\alpha|)^{n-1}$. The binomial series gives $g(w)=(\sqrt{1+4\alpha w}-1)/(2\alpha)$ near $0$. There is a holomorphic branch on $|w|<1/(4|\alpha|)$. At $w_*=-1/(4\alpha)$ a holomorphic extension would give a holomorphic square root $1+2\alpha g(w)$ of a function with a simple zero, which is impossible because the square of a holomorphic function has even zero order. Hence the true radius is $1/(4|\alpha|)$. For the general bound below one may take $C=1/|\alpha|$, $r=|\alpha|$ and $I=1$. It gives $1/(8|\alpha|)$, half the true radius. The binary-tree bound recovers the true radius here.

**Example 2 (two matrix variables).** Let $A=M_2(\mathbb C)$ with the maximum absolute row-sum norm, and give $A^2$ the maximum of its two component norms. Take $f(X,Y)=(X+XY,Y+XY)$. Its bilinear coefficient is $B((X,Y),(X',Y'))=(XY',XY')$ and $\|B\|=1$ by submultiplicativity and evaluation on identity matrices. For target $(U,V)$, write the inverse as $(U+H,V+H)$ with $H$ of order at least two. The right inverse equation is $H=-(U+H)(V+H)$. Equating degrees in order gives
$$
\begin{aligned}
H_2&=-UV,\\
H_3&=-UH_2-H_2V=U^2V+UV^2,\\
H_4&=-UH_3-H_3V-H_2H_2
     =-U^3V-2U^2V^2-UV^3-UVUV .
\end{aligned}
$$
The factor order is the order of matrix multiplication. With $U=E_{11}$ and $V=E_{12}$, where $E_{ij}$ are the matrix units, $UV=V$ and $VU=V^2=0$, so $H_2=-V$, $H_3=V$ and $H_4=-V$. The inputs are noncommuting and all three degrees are nonzero. On independent input slots the recurrence uses consecutive blocks and applies $B$ to the two block outputs. Consequently the operator norms of its inverse coefficients $q_n$ obey $\|q_1\|=1$ and $\|q_n\|\le\sum_{j=1}^{n-1}\|q_j\|\|q_{n-j}\|$. Induction with the recurrence in Example 1 gives $\|q_n\|\le c_{n-1}\le 4^{n-1}$ for every $n\ge1$. This proves absolute convergence on the open ball of radius $1/4$. The general bound below with $C=r=I=1$ gives radius at least $1/8$.

**Definitions.** Let $E,F$ be normed spaces over a nontrivially normed field. A formal multilinear series $p$ from $E$ to $F$ has continuous $n$-linear coefficients $p_n:E^n\to F$, with $p_0$ a constant. Its operator-norm radius is the supremum of $s\ge0$ for which $\|p_n\|s^n$ is bounded over $n$. For a composition of degree $k$, choose an ordered list of positive integers $(d_1,\ldots,d_j)$ with sum $k$. Group the $k$ inputs into consecutive blocks of these lengths, evaluate the inner coefficients on their respective blocks, and apply the outer coefficient of degree $j$ to the resulting ordered tuple. This is centered composition, which ignores the inner constant. The left inverse is the series on the outside in $q\circ p$, and the right inverse is on the inside in $p\circ q$. The stored inverse constant $x\in E$ accounts for the source base point. When $p_1=L$ in one-slot form, the pinned formal inverse identities give $q_L\circ p=\operatorname{id}_{E,x}$ and $p\circ q_R=\operatorname{id}_{F,p_0}$, where $\operatorname{id}_{E,x}$ has constant $x$, linear term the identity and all higher terms zero. The notation for $F$ is analogous. The library identifies the two formal inverses using associativity. The next section proves the associativity used at that step. [Inverse.lean:49–291](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Inverse.lean#L49)

**Lemma 1 (enlarging the set of ordered blocks) [Expository].** For any integer $n\ge0$, nonnegative real numbers $u_k$ for $k\ge0$, and $r,t\ge0$, one has
$$
\sum_{k=2}^n t^k
 \sum_{\substack{j\ge2, d_1+\cdots+d_j=k\\d_i\ge1}}
 r^j\prod_{i=1}^j u_{d_i}
\le
\sum_{j=2}^n \left(r\sum_{d=1}^{n-1}t^d u_d\right)^j .
$$
Sums with empty index sets are zero.

*Proof.* For $n<2$ the outer sums are empty. Otherwise the weight for each ordered composition equals $\prod_{i=1}^j (rt^{d_i}u_{d_i})$ because the block lengths sum to $k$. Its length satisfies $2\le j\le n$. Each block has length at most $k-1\le n-1$, because some other block has positive length. The map from a degree and its composition to $(j,(d_1,\ldots,d_j))$ is injective since the sum of the tuple recovers the degree. The image consists exactly of tuples in $\{1,\ldots,n-1\}^j$ of total at most $n$. Enlarge to that entire Cartesian power using nonnegativity. Its product sum factors by finite distributivity into $\bigl(\sum_{d=1}^{n-1} rt^d u_d\bigr)^j$. Summing over lengths proves the inequality. $\square$

**Lemma 2 (from coefficients to partial sums) [Expository].** For any such $p$, supplied continuous linear isomorphism $L:E\to F$, and $x\in E$, let $q$ be the series constructed by the right inverse recursion with $L$. Put $I=\|L^{-1}\|$. Suppose $C,r,t\ge0$ and $\|p_j\|\le Cr^j$ for every $j\ge0$. Set $S_n(t)=\sum_{k=1}^{n-1}t^k\|q_k\|$ for $n\ge1$. Then for every $n\ge1$,
$$
S_{n+1}(t)\le It+IC\sum_{j=2}^n(rS_n(t))^j .
$$

*Proof.* The degree-one coefficient is $L^{-1}$, with norm $I$. For $k\ge2$ the recursion sets
$$
q_k=-L^{-1}\sum_{\substack{j\ge2, d_1+\cdots+d_j=k\\d_i\ge1}}
            p_j(q_{d_1},\ldots,q_{d_j}),
$$
where each term is the ordered block substitution defined above. Indeed, the definition computes $p\circ q$ with all degrees from $k$ onward zeroed in its inner series. The length-one composition is then zero, and every block in a longer composition has degree strictly below $k$. This gives a finite recursion with a unique coefficient at each degree. For any input tuple, the norm of a substituted term is at most $\|p_j\|\prod_i\|q_{d_i}\|$ times the product of the norms of the $k$ original inputs, since the blocks partition the slots. Applying $L^{-1}$ multiplies this bound by at most $I$. Take operator norms and sum with weights $t^k$. Lemma 1, with $u_d=\|q_d\|$, gives the claimed estimate. No equality between $p_1$ and $L$ is needed for this estimate on the recursively defined series. $\square$

**Proposition (a uniform positive radius) [Expository].** In Lemma 2 assume $C,r>0$. Put $K=I+1$ and
$$
t_0=\frac{1}{\max(2rK, 2ICr^2K^2)} .
$$
Then $t_0>0$ and $\sum_{k\ge1}t_0^k\|q_k\|\le Kt_0$. In particular $\operatorname{rad}(q)\ge t_0$. If $p_1=L$, the same statement holds for the left inverse. If $E$ is complete, the resulting inverse series converges absolutely and uniformly on the closed target ball $\|v\|\le t_0$, evaluated on the diagonal $(v,\ldots,v)$.

*Proof.* The hypotheses make the denominator positive even when $I=0$. Write $t=t_0$. The empty sum gives $S_1(t)=0$. If $S_n(t)\le Kt$, then $0\le rS_n(t)\le1/2$. For $0\le z\le1/2$, the finite sum of powers of $z$ from $2$ to $n$ is at most $2z^2$. By Lemma 2,
$$
S_{n+1}(t)\le It+2IC(rS_n(t))^2
\le \bigl(I+2ICr^2K^2 t\bigr)t\le Kt .
$$
Thus every partial sum has the same upper bound. The real partial sums increase, so they converge and give the asserted bound at $t_0$. In particular every single weighted coefficient is bounded at that scale. The zero-degree term has finite norm and makes no difference to the radius. If the input is given only by $\operatorname{rad}(p)>0$, choose a positive $s$ below that radius. The weighted norms at $s$ are bounded by a positive constant $C$, so one can take $r=s^{-1}$.

Under $p_1=L$, the inherited formal inverse identities identify the two series with the same stored constant, so the bound transfers coefficient by coefficient. For evaluation, each diagonal term has norm at most $t_0^k\|q_k\|$ throughout the ball, and the tail of that scalar series tends to zero. This gives uniformly Cauchy partial sums whose limits belong to $E$ by completeness. The continuous linear isomorphism transports completeness between $E$ and $F$, so the Banach-space formulation also allows evaluation of the forward series in $F$. The coefficient estimates and the formal radius itself use only normed spaces. The analytic inverse representation on a neighborhood uses the [recovery of the outer sum](#ordered-composition-of-multilinear-power-series) below. $\square$

**Boundary cases.** For $p(z)=z^2$ with zero center the forward radius is infinite. Every centered formal candidate $q$ has $q^2$ of degree at least two (or identically zero), so the degree-one equation for a right inverse fails. The matching invertible linear coefficient is essential to the inverse interpretation. A supplied isomorphism alone still defines the recursion of Lemma 2.

Completeness matters at the step of taking a sum in the specified space. Equip the space $c_{00}$ of finitely supported complex sequences with the $\ell^1$ norm, let $T e_j=e_{j+1}$ on its unit vectors, and set $p(v)=v-v_1Tv$. This is a polynomial with linear coefficient the identity and bilinear coefficient $(u,v)\mapsto-u_1Tv$. Its formal inverse on input $te_1$ has first term $te_1$ and degree-$n$ diagonal term $t^n e_n$. Indeed the right inverse equation is $q=te_1+q_1^{\mathrm{coord}}Tq$, where the first coordinate $q_1^{\mathrm{coord}}$ is $t$ since $(Tq)_1=0$. For $0<|t|<1$ the terms are absolutely summable in norm, but a limit in $c_{00}$ would have the infinitely supported coordinate list $(t,t^2,\ldots)$ by continuity of each coordinate. The normed-space radius bound still applies.

A finite truncation has finite weighted norm sum at every finite scale. Even a specified finite prefix can be followed by a factorial tail, for which the weighted terms fail to tend to zero at every positive scale. It is the cutoff-independent bound in the induction that pays for a positive radius.

**Production notes [Lean, read].** The first auxiliary lemma is named <code>radius_right_inv_pos_of_radius_pos_aux1</code>. It expresses the ordered block sum as a sum over pairs of a degree and a composition, extends the finite index set by positivity, and uses the bijection <code>compChangeOfVariables_sum</code> to pass to all tuples of lower block degrees. The last equality expands the product of sums. The second lemma, <code>radius_rightInv_pos_of_radius_pos_aux2</code>, isolates the degree-one term, expands <code>rightInv_coeff</code>, bounds the norm of the outer linear composition and the norm of the sum, and uses <code>compAlongComposition_norm</code> on each summand before calling the first lemma. The pinned wrapper chooses a sufficiently small positive scale and uses the partial-sum induction to give an eventual coefficient bound at that scale. The explicit $t_0$ and the sum at $t_0$ above record what the same inequalities give in prose. The wrapper's next consumer uses coincidence with the left inverse under the degree-one matching hypothesis, and the analytic inverse proof consumes the resulting positive radius in its convergent-composition step. [Inverse.lean:363–478,482–558,656–668](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Inverse.lean#L363) · [Composition.lean:300–322,540–644](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Composition.lean#L540)

Gouëzel credits Jürgen Pöschel for the finite-sum technique in the file commentary. In Pöschel's proof of Theorem 5.2, the inversion argument bounds each Taylor cutoff in a derivative seminorm before passing to all orders. Here the cutoff controls a weighted sum of multilinear operator norms. The archive A2 (SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>) uses the analytic wrapper in its local section construction, at <code>src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/Imports.lean:125–148</code>. [Pöschel, §5, p. 16](https://arxiv.org/abs/1702.03691)

#### Ordered composition of multilinear power series

**Motivation.** The [formal inverse identities and radius estimate](#a-positive-radius-for-the-inverse-series) supply a candidate inverse series of positive radius. Two steps connect these facts to analytic inversion. The formal calculation must preserve the order of the inputs even for coefficients that are sensitive to permutations. The analytic calculation must recover the sum of the outer series from a known expansion of the composite. That direction is needed because the outer function is the inverse whose analyticity is being proved.

**Example 1.** Let $p,q,r$ be three copies of $\phi(t)=\sum_{j\ge1}t^j=t/(1-t)$ over $\mathbb C$. In degree $n\ge1$, every composition of $n$ contributes $1$ to $q\circ p$. Cutting at any subset of the $n-1$ internal gaps gives $2^{n-1}$ terms, so $q\circ p=t/(1-2t)$. In the three-layer computation each gap has three possibilities: no cut, a cut between fine blocks within one coarse block, or a cut between coarse blocks. Thus the coefficient is $3^{n-1}$. In degree two the three choices give $1+1+1$. In degree three the fine partitions $(3),(1,2),(2,1),(1,1,1)$ give $1+2+2+4=9$. Starting with the coarse partition gives $4+2+2+1=9$. In degree four the contributions by number of fine blocks are $1+3\cdot2+3\cdot4+8=27$. In both parenthesizations the constant is zero and the linear coefficient is one. The resulting function is $t/(1-3t)$ on $|t|<1/3$. On this disk $|\phi(t)|<1/2$ and $|\phi(\phi(t))|<1$, so each substitution is within the domain of its geometric series. For the recovering direction take $f(t)=\phi(t)$ and $g(u)=u/(1-2u)$ near zero. The known composite $t/(1-3t)$ then recovers $\sum_{j\ge1}2^{j-1}f(t)^j=g(f(t))$ locally.

**Example 2.** Set $A=M_2(\mathbb C)$ and let
$$
P(X,Y)=(X+XY,Y),\qquad Q(X,Y)=(X,Y+YX),\qquad R(X,Y)=(X+XY,Y)
$$
on $A^2$ with a product matrix norm. For slots $u=(X,Y)$ and $v=(X',Y')$, use the ordered coefficients $P_2(u,v)=R_2(u,v)=(XY',0)$ and $Q_2(u,v)=(0,YX')$. All three linear coefficients are identities. First $Q(P(X,Y))=(X+XY,Y+YX+YXY)$, so applying $R$ adds $(X+XY)(Y+YX+YXY)$ to the first coordinate. The six products in this rectangle are $XY,XYX,XYXY,XYY,XYYX,XYYXY$. In the other parenthesization $R(Q(X,Y))=(X+XY+XYX,Y+YX)$, using the ordered ternary term $X_1Y_2X_3$. Substitution into that ternary term gives
$$
(X+XY)Y(X+XY)=XYX+XYXY+XYYX+XYYXY.
$$
The linear term supplies $X+XY$ and the quadratic term supplies $XY+XYY$. The second coordinate in either case is $Y+YX+YXY$. Grouping every contribution by degree gives

| Degree | First coordinate | Second coordinate |
|---|---|---|
| 0 | $0$ | $0$ |
| 1 | $X$ | $Y$ |
| 2 | $2XY$ | $YX$ |
| 3 | $XYX+XYY$ | $YXY$ |
| 4 | $XYXY+XYYX$ | $0$ |
| 5 | $XYYXY$ | $0$ |

All higher coefficients vanish. Each word in this table prescribes the corresponding slotwise product, in order, even for distinct slot inputs. For example the two degree-four terms are $X_1Y_2X_3Y_4$ and $X_1Y_2Y_3X_4$. With matrix units $X=E_{11}$ and $Y=E_{12}$, $XY=E_{12}$ and $YX=0$. The degree-five word is genuinely present, for instance at $X=Y=I_2$. All series here are polynomials with infinite radius. The products illustrate why interchanging slots would change the formal identity.

**Definition.** Work over a nontrivially normed field $K$ with normed $K$-spaces $E,F,G,H$. A formal multilinear series $p$ from $E$ to $F$ is a sequence of continuous $K$-multilinear maps $p_n:E^n\to F$. Write $p_n[y]=p_n(y,\ldots,y)$ and $p_0[\,]$ for evaluation at the unique empty tuple. An ordered composition $c$ of $n$ is a list $(c_0,\ldots,c_{\ell-1})$ of positive integers with sum $n$. Put $s_c(i)=\sum_{j<i}c_j$. For $q$ from $F$ to $G$, define
$$
T_c(v)=q_\ell\bigl(p_{c_i}((v_{s_c(i)+j})_{0\le j<c_i})\bigr)_{0\le i<\ell},
\qquad
(q\circ p)_n=\sum_{c\text{ of }n}T_c.
$$
Here the parenthesized family is the argument tuple of $q_\ell$. Each input appears in one block, so linearity in that slot follows first from the relevant $p_{c_i}$ and then from $q_\ell$. Continuity follows from the finite product of the block maps and continuity of $q_\ell$. There are $2^{n-1}$ compositions for $n>0$, by the gap argument, and one empty composition for $n=0$. Thus every coefficient is a finite sum. At degree zero the result is $q_0[\,]$. In Mathlib this is <code>q.comp p</code>, a total operation ignoring $p_0$. The analytic substitution into an expansion centered at $f(x)$ uses the zero-constant increment $f(x+y)-f(x)$, while the stored $p_0[\,]$ equals $f(x)$.

**Lemma 1 (formal associativity).** For every $p:E\to F$, $q:F\to G$ and $r:G\to H$ understood as formal series, $(r\circ q)\circ p=r\circ(q\circ p)$ as sequences of multilinear maps.

*Proof.* Fix $n$ and an arbitrary tuple $v$ of length $n$. Expanding the left side indexes its terms by a fine composition $a$ of $n$ and a composition $b$ of the length of $a$. The list $b$ partitions the list of fine blocks into consecutive nonempty groups. Let $d_i$ be the sublist of $a$ in group $i$ and let $c_i$ be its sum. Then $c$ is a composition of $n$, and each $d_i$ is a composition of $c_i$. Conversely concatenate the $d_i$ to recover $a$ and record their lengths to recover $b$. Positivity ensures that the concatenated list and all group lengths are valid, and the prefix lengths cut the concatenation back at exactly the original group boundaries. At $n=0$ both index sets have one element with all lists empty.

On the right, expanding each slot of $r$ by multilinearity gives precisely the sum over $(c,(d_i)_i)$. The two terms agree at every level. The outer arity is the number of groups, middle arity in group $i$ is $b_i$, and inner arity for fine block $j$ in group $i$ is $(d_i)_j=a_{s_b(i)+j}$. The input at offset $k$ in that block is the same on both sides since
$$
s_a(s_b(i)+j)+k=s_c(i)+s_{d_i}(j)+k.
$$
Indeed the fine blocks before this slot consist of all previous groups followed by the first $j$ blocks in group $i$. Reindexing the finite sums now gives equality at the arbitrary tuple $v$ and hence equality of the maps. The proof uses no convergence or symmetry. Lean names the equivalence <code>Composition.sigmaEquivSigmaPi</code> and uses this prefix identity after transporting each of the three arities. $\square$ [Composition.lean:962–1289](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Composition.lean#L962)

**Lemma 2 (absolute summability of the block family).** If $p,q$ have positive radius, there exists a real $\rho>0$ with $\sum_{n,c}\|T_c\|\rho^n<\infty$, where $c$ ranges over compositions of $n$.

*Proof.* Choose real radii $0<u,v<1$ strictly below the radii of $p,q$ respectively. The operator-norm radius gives bounds $\|p_j\|u^j\le C_p$ and $\|q_j\|v^j\le C_q$ for all $j$, with $C_p\ge1$ and $C_q>0$. Apply the multilinear norm bound first to the inner maps, then to the outer map. Each slot contributes once, yielding $\|T_c\|\le \|q_\ell\|\prod_i\|p_{c_i}\|$. With $\rho=uv/(4C_p)$ the weighted bound is
$$
\|T_c\|\rho^n
\le C_q v^{n-\ell} C_p^{\ell-n}4^{-n}
\le C_q4^{-n},
$$
since $\ell\le n$. The degree-zero contribution is finite. At positive $n$, multiplying the estimate by $2^{n-1}$ gives a geometric bound with ratio $1/2$. For $\|y\|\le\rho$, the same summable family bounds the norms of $T_c(y,\ldots,y)$. $\square$ [Composition.lean:300–326,449–506](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Composition.lean#L449)

**Lemma 3 (recovering the outer sum).** For any functions $f:E\to F$ and $g:F\to G$, any $p,q$ as above and any $x\in E$, assume that $g\circ f$ has expansion $q\circ p$ at $x$, that $f$ has expansion $p$ at $x$, and that $q$ has positive radius. There exists a neighborhood of $0$ in $E$ such that for every $y$ in it,
$$
\operatorname{HasSum}\bigl(n\mapsto q_n[f(x+y)-f(x)],\,g(f(x+y))\bigr).
$$
An expansion at $x$ means that some positive ball radius, at most the series radius, gives the asserted diagonal sum at every increment in that ball. Here $\operatorname{HasSum}$ means convergence of the net of sums over finite subsets, directed by inclusion.

*Proof.* Choose $y$ in a positive ball on which both given expansions hold and with $\|y\|<\rho$ from Lemma 2. Also require $\|f(x+y)-f(x)\|<\operatorname{rad}(q)$ throughout a possibly smaller neighborhood. This follows from continuity of $f$ at $x$ and positivity of the outer radius. Write $L=g(f(x+y))$ and $z=f(x+y)-f(x)$.

The block sum over a finite set of pairs $(n,c)$ is a Cauchy net: given $\varepsilon>0$, include enough terms of the summable norm bound that the norm sum outside them is less than $\varepsilon$. Two finite sums containing this set differ by at most that tail. The sets consisting of all compositions of degrees $<N$ eventually contain any prescribed finite set, and their sums tend to $L$ by the given composite expansion. Consequently the full net tends to $L$. Explicitly, include a sufficiently late set from this family so its sum is close to $L$, and use the Cauchy estimate to compare every sufficiently large finite sum to that sum. This is the finite-fibre regrouping used by <code>HasSum.of_sigma</code>.

Write $q^{<M}(w)=\sum_{k<M}q_k[w]$ and $p^{<N}$ similarly. Finite multilinearity gives
$$
q^{<M}\left(\sum_{1\le j<N}p_j[y]\right)
=\sum_{\substack{(n,c):\ \ell(c)<M\\ c_i<N\text{ for every }i}}
T_c(y,\ldots,y).
$$
The tuple of inner degrees in each expanded term is exactly the ordered list $c$; its sum recovers $n$ and its length recovers the outer arity. This proves the reindexing in both directions, including the empty list when $M>0$. As $M,N$ grow independently, the sets on the right contain every prescribed finite subset once $M$ exceeds all its lengths and $N$ all its block sizes. They therefore give a joint limit $L$. For $N\ge1$ the argument on the left is $p^{<N}(y)-p_0[\,]$ and tends to $z$ by the expansion of $f$.

For fixed $M$, continuity of the polynomial $q^{<M}$ gives the corresponding limit $q^{<M}(z)$ as $N\to\infty$. To pass from joint convergence to convergence of these limits, take any closed neighborhood $U$ of $L$ and an open neighborhood inside $U$. The joint limit puts the rectangle $M\ge M_0$, $N\ge N_0$ inside the open neighborhood. For each $M\ge M_0$, closedness puts $q^{<M}(z)$ in $U$. Closed neighborhoods form a basis, so $q^{<M}(z)\to L$. Finally, strictly inside the radius of $q$, the scalar series $\sum_n\|q_n[z]\|$ converges by comparison with a weighted norm series at a radius strictly between $\|z\|$ and $\operatorname{rad}(q)$. Its finite-subset net is Cauchy, and its degree cutoffs converge to $L$. The same tail comparison gives the claimed $\operatorname{HasSum}$. $\square$ [Inverse.lean:567–651](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Inverse.lean#L567) · [Composition.lean:540–694](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Composition.lean#L540)

**Completeness and the local inverse.** In a complete target, a summable norm bound produces an actual sum for any family under consideration. In Lemma 3 the two given expansions and the joint truncation limit already supply the limits needed to identify the Cauchy nets, so the pinned lemma has normed-space hypotheses alone. When starting with a positive-radius series and defining its function by summation, completeness of its target supplies existence on each smaller ball. If a formal identity identifies its coefficients with those of an existing local expansion, evaluation and uniqueness of limits identify the two functions there. In the inverse application the identity series already expands the identity function. On the open source of the partial homeomorphism, this is an expansion of the inverse composed with the forward map. Lemma 3 therefore recovers the candidate inverse sum on increments in the forward image. The open target and continuity of the inverse turn this into a neighborhood of the target point.

| Consumer | Exact inputs and use |
|---|---|
| <code>leftInv_eq_rightInv</code>, Inverse.lean:283–291 | Matching invertible linear coefficient and the inherited one-sided formal identities with their stored constants. <code>comp_assoc</code> reassociates the three series at line 289 before the identity laws cancel the outside factors. |
| <code>hasFPowerSeriesAt_symm</code>, Inverse.lean:656–668 | Open partial homeomorphism $f$, $a$ in its source, expansion $p$ of $f$ at $a$, and $p_1$ the one-slot form of a continuous linear equivalence $i$. Set $q=p.\mathrm{leftInv}(i,a)$. The inherited left identity and openness supply an expansion of $f^{-1}\circ f$ by $q\circ p$ at $a$. The inherited positive radius of $q$ and the given expansion of $f$ give the other two inputs to Lemma 3. |
| Inverse.lean:669–694 | Translate the input increment by $a$, restrict to the open source and simplify the left inverse. Pull the eventual sum back through the continuous inverse at $f(a)$, restrict to the open target and simplify the right inverse. Intersect a ball in this target neighborhood with the radius of $q$ to obtain the inverse expansion. |
| <code>analyticAt_symm'</code> and <code>analyticAt_symm</code>, FDeriv/Analytic.lean:414–429 | Analyticity at the source point supplies $p$. The derivative formula identifies $p_1$ with the given equivalence. The target version assumes target membership at $b$, applies the source version at $f^{-1}(b)$ and rewrites $f(f^{-1}(b))=b$. |
| Archive A2, ModuliProofs/Imports.lean:125–148 | The equivalence $i$ represents $L$ and analyticity upgrades the derivative to a strict derivative at $a_0$. The strict-inverse chart is restricted to an open $U$ on which $F$ is analytic and each derivative is a continuous linear equivalence. For every $b$ in the restricted target, its inverse image lies in $U$, supplying the exact analyticity and derivative premises of <code>analyticAt_symm</code>. |

**Notes on hypotheses and uniqueness.** A nonzero inner constant can make ordinary formal substitution undefined. For $p(t)=1+t$ and $q(t)=\sum_{k\ge0}t^k$, the literal constant coefficient of $q(p(t))$ would sum infinitely many ones, and even the coefficient of $t$ would sum the integers $k\ge1$. Positivity of every block size is what bounds the arity by the degree. The pinned total operation still works by ignoring the inner constant. Analytically one must expand at the correct center and substitute the zero-constant increment.

A proposed exchange of two sums without absolute summability can give different limits even when both iterated sums exist. On $i,j\ge0$ take $a_{ij}=\mathbf 1_{j=i}-\mathbf 1_{j=i+1}$. Every row sums to zero. Column zero sums to one and all other columns sum to zero. The two iterated sums are zero and one, and the sum of absolute values is infinite. This is a boundary for the reindexing argument involving all degrees. The finite identity at each degree still holds.

Finally, a diagonal function germ determines the diagonal homogeneous terms of its convergent expansion, over the nontrivially normed field in the lemmas. To see this, subtract two expansions and fix any vector $v$. If $m$ is the first index with nonzero diagonal difference $d_m[v]$, evaluate at $tv$, divide the zero sum by $t^m$ and let $t$ tend to zero through nonzero scalars. The higher terms tend to zero: choose $s>0$ with $s\|v\|$ below both radii. For $0<|t|\le s$, the tail norm after division is bounded by $|t|s^{-m-1}\sum_{n>m}s^n\|d_n[v]\|$. Nontriviality gives such scalars tending to zero, forcing $d_m[v]=0$. The argument applies at each $v$. The multilinear maps themselves can differ, even over $\mathbb C$: on $\mathbb C^2$ the bilinear map $(u,v)\mapsto u_1v_2-u_2v_1$ is nonzero and vanishes on all diagonals. Adding it in degree two leaves every diagonal evaluation unchanged. This is why Lemma 1 proves equality on arbitrary tuples.

**Source scope [Lean, read].** The two producers and their ordered-block and truncation proofs are read locally at Mathlib pin <code>0df444a360eaa60ab8c11dca51a86af692955474</code>. Composition.lean credits Sébastien Gouëzel and Johan Commelin. The archive application is in A2, joined SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>. The book contributes the exposition, computations and boundary examples. The [preceding radius section](#a-positive-radius-for-the-inverse-series) supplies the recursion and majorants. The [open inverse chart](#strict-inverse-chart-for-etale-local-sections) supplies the identities and neighborhood transport used in the analytic application. [Sources](../sources/SOURCES.md#chapter-12--ordered-composition-of-multilinear-power-series)

#### Forward composition on restricted sets

**Motivation.** Once an inverse chart is analytic, composing it with a linear inclusion gives an analytic parametrization of a slice. For general nonlinear inner maps and restricted outer expansions there is a further issue. The image of the inner function can lie in the outer set while the polynomial approximations to the inner function leave that set. The outer partial sums must converge at these moving arguments.

**Example 1 (scalar, at nonzero centers).** Over $\mathbb R$ take $x=2$, $s=(2,9/4)$, $t=(3,7/2)$ and
$$
f(2+h)=3+\frac{h}{1-h},\qquad g(3+w)=7+\frac{w}{1-2w}.
$$
Assign arbitrary values at the poles to make total functions. The scalar coefficients act by multiplying the product of the slot inputs. The geometric series give $p_0=3$, $p_j=1$ for $j>0$, and $q_0=7$, $q_k=2^{k-1}$ for $k>0$, with radii $1$ and $1/2$. For $0<h<1/4$, the inner increment lies in $(0,1/3)$, so $f(s)\subset t$.

A positive degree $n$ has $\binom{n-1}{k-1}$ compositions of length $k$, each contributing $2^{k-1}$. Thus its coefficient is $3^{n-1}$ by the binomial theorem. The constant is $7$, and the first three positive coefficients are $1,3,9$. Direct substitution gives
$$
g(f(2+h))=7+\frac{h/(1-h)}{1-2h/(1-h)}=7+\frac{h}{1-3h}.
$$
The resulting series has radius $1/3$, and the restricted identity holds for every $0\le h<1/4$. At $h=1/8$, the argument increment of the outer expansion is $1/7$ and the composite value is $36/5$.

**Example 2 (a two-dimensional curve).** Use the maximum norm on $\mathbb R^2$. Set $x=(1,-1)$, $b=(2,3)$ and $d=(5,-2)$. Define $f(x+(u,v))=b+(A,B)$ with $A=u+v^2$, $B=v+uv$, and let $g(b+(a,c))=d+(a+ac,c+a^2)$. Use
$$
s=\{x+(u,2u):0<u<1/4\},\qquad
t=\{b+(u+4u^2,2u+2u^2):0<u<1/4\}.
$$
Here $f(s)=t$. For slots $U=(u_1,v_1)$ and $V=(u_2,v_2)$ take $p_1=q_1=\mathrm{id}$, $p_2(U,V)=(v_1v_2,u_1v_2)$ and $q_2(U,V)=(u_1v_2,u_1u_2)$. The stored constants are $b$ and $d$. Both series are finite with infinite radius. Witness radii $1/2$ and $1$ suffice since the input increment has norm $2u<1/2$ and the output increment has norm less than $5/8$.

| Degree | Contributing compositions | Diagonal value |
|---|---|---|
| 0 | empty | $(5,-2)$ |
| 1 | $(1)$ | $(u,v)$ |
| 2 | $(2),(1,1)$ | $(v^2+uv,uv+u^2)$ |
| 3 | $(1,2),(2,1)$ | $(u^2v+v^3,2uv^2)$ |
| 4 | $(2,2)$ | $(uv^3,v^4)$ |

All higher coefficients vanish. The two cubic contributions are $(u^2v,uv^2)$ and $(v^3,uv^2)$ in the indicated order. Direct multiplication gives $AB=uv+u^2v+v^3+uv^3$ and $A^2=u^2+2uv^2+v^4$, accounting for every term in $d+(A+AB,B+A^2)$. At $(u,v)=(1/8,1/4)$ the inner increment is $(3/16,9/32)$ and the composite is $(2683/512,-431/256)$. The linear truncation restored to center $b$ lies outside $t$ for every point of $s$. Its increment has second coordinate twice the first. On $t$ the difference of the second coordinate increment and twice the first is $-6u^2$.

**Definition.** Let $K$ be any nontrivially normed field and $E,F,G$ normed $K$-spaces. Write $s_x=s\cup\{x\}$ and $B(x,R)=\{z:\|z-x\|<R\}$ for extended radius $R\in[0,\infty]$. An expansion of $f:E\to F$ by a formal multilinear series $p$ at $x$ within $s$ means that some $0<R_f\le\operatorname{rad}(p)$ satisfies
$$
\forall y\in B(0,R_f),\quad x+y\in s_x\implies
\operatorname{HasSum}(n\mapsto p_n[y],f(x+y)).
$$
Here $p_n[y]$ evaluates on $n$ copies of $y$, and $\operatorname{HasSum}$ means convergence of the net of finite subsums. At $y=0$, every positive-degree evaluation vanishes, so $p_0[\,]=f(x)$ even when $x\notin s$. Use the ordered block maps $T_c$ of the preceding subsection, indexed by a degree $n$ and an ordered composition $c$ of $n$. The degree $n$ coefficient of $q\mathbin{\mathrm{comp}}p$ is the finite sum of those maps at that degree. [Basic.lean:80–99,433–436](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Basic.lean#L80)

**Lemma (moving partial sums).** Suppose $g:F\to G$ has expansion $q$ at $b$ within $t$ with witness $R_g$. If $\|z\|<R_g$ and $b+z\in t_b$, then $Q_N(w)=\sum_{k<N}q_k[w]$ converges to $g(b+z)$ jointly as $N\to\infty$ and $w\to z$ in $F$.

*Proof.* Choose a finite $a$ with $\|z\|<a<R_g$. The scalar series $\sum_k\|q_k\|a^k$ converges by the operator-norm radius estimate. For $N\ge m$ and $\|w\|<a$ the difference $Q_N(w)-Q_N(z)$ has norm at most
$$
\|Q_m(w)-Q_m(z)\|+2\sum_{k\ge m}\|q_k\|a^k.
$$
Choose $m$ to make the tail small and use continuity of $Q_m$ to make the first term small on a neighborhood of $z$. At $z$, the supplied sum implies $Q_N(z)\to g(b+z)$. The inequality holds throughout the chosen neighborhood, including arguments $w$ with $b+w$ outside $t_b$. $\square$ [Basic.lean:607–669](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Basic.lean#L607)

**Theorem (forward composition within a set) [Lean, read].** For every $f:E\to F$, $g:F\to G$, $s\subseteq E$, $t\subseteq F$, $x\in E$ and formal series $p,q$ of the matching types, assume $f$ has expansion $p$ at $x$ within $s$, $g$ has expansion $q$ at $b=f(x)$ within $t$, and $f(s)\subseteq t$. There exists $0<R\le\operatorname{rad}(q\mathbin{\mathrm{comp}}p)$ such that for every $y\in B(0,R)$ with $x+y\in s_x$,
$$
\operatorname{HasSum}\bigl(n\mapsto(q\mathbin{\mathrm{comp}}p)_n[y],g(f(x+y))\bigr).
$$

*Proof.* Fix witnesses $R_f,R_g$. The inherited block majorant supplies a finite $r>0$ with $C=\sum_{n,c}\|T_c\|r^n<\infty$. For each degree the triangle inequality gives $\|(q\mathbin{\mathrm{comp}}p)_n\|r^n\le C$, hence $r\le\operatorname{rad}(q\mathbin{\mathrm{comp}}p)$ by the operator-norm characterization.

The expansion of $f$ gives continuity at $x$ within $s_x$. Indeed, the moving partial sums lemma at increment zero makes every sufficiently late truncation close to $f(x)$ throughout a neighborhood of zero. At each allowed increment in that neighborhood the known limit is $f(x+y)$, so it lies within the closed ball of the same tolerance. Arbitrarily small tolerances give continuity. The pinned proof obtains it from local uniform convergence on the translated restricted ball. On $s_x$, the mapping hypothesis and $f(x)=b$ give $f(s_x)\subseteq t_b$. The target $t_b\cap B(b,R_g)$ is a neighborhood within $t_b$. Continuity and the mapping property pull it back to a neighborhood of $x$ within $s_x$, so some $\delta>0$ satisfies
$$
f(s_x\cap B(x,\delta))\subseteq t_b\cap B(b,R_g).
$$
Set $R=\min(R_f,\delta,r)$. It is positive and bounded by the composite radius.

Fix an arbitrary allowed $y$. Put $z=f(x+y)-b$ and $P_N=\sum_{1\le j<N}p_j[y]$. For $N\ge1$, $P_N$ is the inner partial sum minus $p_0[\,]=b$, so $P_N\to z$. The transported conditions give $\|z\|<R_g$ and $b+z\in t_b$. The moving partial sums lemma along $(N,P_N)$ gives $Q_N(P_N)\to g(f(x+y))$.

The inherited finite truncation identity at equal cutoffs identifies $Q_N(P_N)$ with the sum of $T_c(y,\ldots,y)$ over pairs $(n,c)$ with $\ell(c)<N$ and all block sizes $<N$. These finite sets eventually contain each finite set of pairs. Since $\|y\|<r$, the scalar majorant $\|T_c\|r^n$ makes the net of finite subsums Cauchy. Given a tolerance, choose a finite set beyond which Cauchy differences are small. Choose a late cutoff containing it with sum close to $g(f(x+y))$. Every finite subsum containing the initial set is close to that cutoff sum. Thus the full net has the known limit. For finite sets of degrees, their unions of fibres are finite and eventually contain each finite set of pairs. Taking that net yields the degree sum with the same limit. This is the finite-fibre case of <code>HasSum.sigma</code>. For every $v\in s_x\cap B(x,R)$ take $y=v-x$. Uniqueness of the sum gives equality of the functions $v\mapsto (q\mathbin{\mathrm{comp}}p).\mathrm{sum}(v-x)$ and $v\mapsto g(f(v))$ on this whole domain. $\square$ [Composition.lean:508–520,703–820](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Composition.lean#L703)

**Constants and locality.** For any constant vector $d_0\in F$, translating the inner function to $f+d_0$ changes its stored constant to $p_0+d_0$. Translating the outer function to $g(\cdot-d_0)$ moves its center to $b+d_0$ and its set to $t+d_0$ with the same coefficients. These statements follow by adding $d_0$ to the inner sum and by evaluating the outer sum at the same increment. The pointwise composite and every formal composite coefficient stay fixed, since positive block sizes omit the inner constant. If only $f$ is translated and $g$ is kept fixed, the outer expansion must be taken at the new image center. For $g(w)=w^2$, the outer constant and linear coefficient change from $b^2,2b$ to $(b+d_0)^2,2(b+d_0)$. The convention on the formal operation permits any stored inner constant.

The proof only uses the image condition close to $x$. If it holds on $s_x\cap B(x,\eta)$ for some $\eta>0$, apply the theorem with $s\cap B(x,\eta)$ and shrink the resulting radius to at most $\eta$. Without the local image condition the conclusion can fail. Take $x=1$, $s=(1,2)$, $f(1+h)=2+h$, $t=\{2\}$ and $g(2)=7$, $g(w)=8$ for $w\ne2$. The inner affine expansion and the outer constant expansion within $t$ both have infinite radius. Their formal composite is constant $7$. For every $R>0$ and every $0<h<\min(R,1)$ the function composite is $8$. It is discontinuous within $s_x$ and hence has no expansion there. The original hypotheses are inhabited by both worked examples, and also admit $s=\varnothing$, when insertion still tests the center.

**Completeness and consumers.** The forward theorem and the moving partial sums lemma require normed spaces. They use real scalar norm sums, the supplied function sums and comparison to an explicitly identified limit. When starting with a positive-radius formal series alone, completeness of its target is used to produce a sum from the absolute norm bound. The corresponding declarations are <code>FormalMultilinearSeries.summable</code>, <code>hasSum</code> and <code>hasFPowerSeriesOnBall</code>. The separate inverse proof at Inverse.lean:656–694 starts with the identity expansion on the open source and uses the [recovery lemma for a known composite](#ordered-composition-of-multilinear-power-series). Its derivative wrapper identifies the first coefficient via <code>HasFPowerSeriesAt.fderiv_eq</code> at the given center (FDeriv/Analytic.lean:109–111,137–139), which also works in normed spaces. Differentiation at a shifted point by the change-of-origin expansion is a separate completeness-dependent interface (lines 193–196). The [strict inverse chart construction](#strict-inverse-chart-for-etale-local-sections) uses completeness of the forward domain in its closed-ball iteration.

In the archive's <code>RegularLocalRings/AnChart.lean:64–95</code>, the inverse theorem supplies analyticity of the inverse chart near the chart image. To restrict it to a slice, the proof then uses <code>AnalyticAt.comp</code> with $w\mapsto(w,0)$, analytic as a product of the identity and a constant. Membership in the chart target and the chart's right-inverse law give membership of the slice point in the neighborhood where the inverse is analytic. This call uses the unrestricted wrapper of the within theorem. The setwise wrapper uses the mapping premise to select the outer expansion at each image point. In A2, <code>AtlasIndep.lean:45–58,75–83</code> uses the unrestricted <code>AnalyticAt.comp</code> on a holomorphic function in chart coordinates and an analytic transition. The left-inverse identity on the open overlap supplies the eventual equality that identifies the resulting germ. [Pinned wrappers](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Composition.lean#L822) · [Sources](../sources/SOURCES.md#chapter-12--forward-composition-on-restricted-sets)

#### Derivative cancellation for a given inverse chart

**Motivation.** The chain rule gives a necessary formula for the derivative of an inverse. To prove the inverse differentiable, we first need to bound increments in the inverse coordinates. The known derivative of the composite supplies that bound after we transfer the lower estimate from the outer map.

**A triangular chart.** Take $f(x,y)=(2x,3y+x^2)$ on $\mathbb R^2$ with the maximum norm. The center $(1,2)$ maps to $(2,7)$. Its polynomial inverse is $g(u,v)=(u/2,(v-u^2/4)/3)$. In $f(g(u,v))$ the square $(u/2)^2$ cancels $-u^2/4$. In $g(f(x,y))$ the second coordinate becomes $(3y+x^2-x^2)/3=y$ and the first becomes $x$. The forward increment at $(1,2)$ is $(2h,2h+3k+h^2)$. Its linear part is $A(h,k)=(2h,2h+3k)$, with inverse $B(p,q)=(p/2,(q-p)/3)$. The inverse increment at $(2,7)$ is
$$
g(2+p,7+q)-g(2,7)=(p/2,(q-p)/3-p^2/12).
$$
The error has maximum norm $p^2/12$. For two source offsets of norms at most $\delta$, the forward error after subtracting the linear difference has second coordinate $(h_1+h_2)(h_1-h_2)$, bounded by $2\delta$ times their distance. This verifies strict differentiability as well. For a within example, $g$ takes the target half-plane $u\ge 2$ into the source half-plane $x\ge 1$, and the target center belongs to its half-plane.

**Definition.** For normed spaces over a nontrivially normed field $\mathbb K$, the two-point derivative predicate $\operatorname{HasFDerivAtFilter}(m,M,\mathcal L)$ says that for every $\varepsilon>0$, eventually in the filter $\mathcal L$ on input pairs $(x,y)$,
$$
\|m(x)-m(y)-M(x-y)\|\le\varepsilon\|x-y\|.
$$
In particular the definition includes pairs of equal points. For the ordinary derivative the filter is $\mathcal N(a)\times\operatorname{pure}(a)$, where the pure filter fixes the second coordinate at $a$. For the within derivative replace the first factor by $\mathcal N_s(a)$, the neighborhood filter restricted to $s$. The strict derivative uses the neighborhood of $(a,a)$.

**Theorem (cancelling an outer derivative) [Lean, read].** For every nontrivially normed field $\mathbb K$, normed $\mathbb K$-spaces $E,F,G$ (in particular Banach spaces), maps $g:E\to F$, $f:F\to G$, $h:E\to G$, filters $\mathcal L_E$ on $E^2$ and $\mathcal L_F$ on $F^2$, and continuous linear maps $A:F\to G$, $B:G\to F$, $H:E\to G$, assume the following.

1. The pair map $(x,y)\mapsto(g(x),g(y))$ tends from $\mathcal L_E$ to $\mathcal L_F$.
2. The two-point derivatives of $f$ along $\mathcal L_F$ and of $h$ along $\mathcal L_E$ are $A$ and $H$, respectively.
3. Eventually in $\mathcal L_E$, both $f(g(x))=h(x)$ and $f(g(y))=h(y)$.
4. $BA=\operatorname{id}_F$ on all of $F$.

Then $g$ has two-point derivative $BH$ along $\mathcal L_E$.

**Proof.** Put $C=\max(1,\|B\|)$. For $(u,v)$ along $\mathcal L_F$, write $w=u-v$ and $R_f=f(u)-f(v)-Aw$. Use tolerance $1/(2C)$ and $BAw=w$ to obtain, eventually,
$$
\|w\|\le C\|f(u)-f(v)\|+C\|R_f\|
       \le C\|f(u)-f(v)\|+\tfrac12\|w\|.
$$
Thus $\|w\|\le 2C\|f(u)-f(v)\|$. This is the lower comparison furnished in the pinned proof by the embedding induced by $A$. Pull it back by the pair map, set $d=x-y$, $w=g(x)-g(y)$, and use the composite equality at both endpoints. We get $\|w\|\le 2C\|\Delta h\|$, where $\Delta h=h(x)-h(y)$. Put $R_h=\Delta h-Hd$ and $M=\|H\|+1$. The derivative of $h$ at tolerance $1$ bounds $\|\Delta h\|$ by $M\|d\|$, so eventually $\|w\|\le 2CM\|d\|$.

Given any $\varepsilon>0$, pull back the outer remainder bound with tolerance $\varepsilon/(4C^2M)$ and intersect with the eventual bound $\|R_h\|\le\varepsilon\|d\|/(2C)$. Now $R_f$ denotes the remainder evaluated on the transported pair. On this intersection,
$$
w-BHd=B(Aw-Hd)=B(R_h-R_f).
$$
Its norm is at most $C(\varepsilon/(2C)+2CM\varepsilon/(4C^2M))\|d\|=\varepsilon\|d\|$. The source first uses the two-sided asymptotic comparison for the forward increment, then pulls back the outer $o$ estimate, and lastly applies the bounded map $B$ to the difference of remainders. The tolerance proof spells out these operations with norms. It includes the zero space and uses no completeness. [Kudryashov, Mathlib OfCompLeft.lean:50–81](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean#L50)

**Corollaries for neighborhood filters.** For the ordinary derivative, continuity at $a$ moves the first factor to $\mathcal N(g(a))$ and the fixed factor goes to $\operatorname{pure}(g(a))$. Eventual equality in $\mathcal N(a)$ also holds at $a$. For strict differentiability, continuity transports both moving coordinates, and taking the product of the eventual equality with itself supplies the two equalities. For the within theorem, choose any $s\subseteq E$, $t\subseteq F$ and $a\in s$, and give the two within derivatives and the eventual equality on $\mathcal N_s(a)$. The transport required is from $\mathcal N_s(a)$ to $\mathcal N_t(g(a))$. For instance, continuity at $a$ along $s$ plus eventual membership of $g(x)$ in $t$ yields this transport by intersecting the preimages of target neighborhoods with that membership condition. The fixed factor again goes to $\operatorname{pure}(g(a))$. The explicit membership $a\in s$ ensures the equality at the fixed endpoint. No uniqueness of within derivatives or membership $g(a)\in t$ is asked for separately. [Mathlib OfCompLeft.lean:83–107](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean#L83)

**Inverse derivative.** In the cancellation theorem let $G=E$ and $h=\operatorname{id}_E$. Its derivative is the identity because the remainder vanishes. For a continuous linear equivalence $A:F\to E$, use $B=A^{-1}$. Each neighborhood version gives the corresponding derivative $A^{-1}$ of $g$ when $f(g(y))=y$ eventually and its continuity or transport premise is supplied. In chart notation $f:X\to Y$, put $a=f(x_0)$ with $x_0$ in the open source and let $g$ be the chart inverse. The source identity gives $g(a)=x_0$. On the open target $f(g(y))=y$, so the equality is eventual. Continuity on the open target gives continuity at $a$. The ordinary and strict derivative conclusions follow from the matching derivatives of $f$ at $x_0$. These steps apply to a chart already given. [Mathlib OfCompLeft.lean:159–218](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean#L159)

**A coupled chart and its slice.** Set $u=x+y^2$ and $f(x,y)=(u,y+u^2)$. The center $(1,1)$ maps to $(2,5)$. The inverse is $g(u,v)=(u-Y^2,Y)$ with $Y=v-u^2$. On applying $f$ to $g$ the first coordinate is $u-Y^2+Y^2=u$ and the second is $Y+u^2=v$. At a forward image $Y=y$ and $u-Y^2=x$. For source increments $(h,k)$ put $p=h+2k+k^2$. The forward increment is $(p,k+4p+p^2)$. Its error after subtracting the linear part $(h+2k,4h+9k)$ is $(k^2,4k^2+p^2)$. With $r=\|(h,k)\|_\infty\le1$, we have $|p|\le4r$ and error norm at most $20r^2$. The linear part and its inverse are
$$
A=\begin{pmatrix}1&2\\4&9\end{pmatrix},
\qquad B=\begin{pmatrix}9&-2\\-4&1\end{pmatrix}.
$$
Both products are the identity, with diagonal entries $9-8$ and off-diagonal entries zero. For target increments $(p,q)$ put $m=q-4p$ and $k=m-p^2$. The inverse increment is $(p-2k-k^2,k)$, so its error after subtracting $B(p,q)$ is $(2p^2-k^2,-p^2)$. For $r=\|(p,q)\|_\infty\le1$, we have $|k|\le6r$ and error norm at most $38r^2$. The slice $(2+p,5)$ has inverse tangent $(9,-4)$ by setting $q=0$. In general a zero-slice inclusion $j(w)=(w,0)$ has derivative $Jv=(v,0)$. Substituting $Jv$ into the inverse derivative remainder proves $D(g\circ j)(w_0)=A^{-1}J$ at a slice center $j(w_0)=a$, since $\|Jv\|\le\|J\|\|v\|$.

**Failure tests.** With $f=h=\operatorname{id}_{\mathbb R^2}$ and $g(p,q)=(|p|,q)$, transport and the linear left inverse are available at zero. The two scalar slopes of the first component are $-1$ and $1$, and the missing premise is the eventual composite equality. With $f(x,y)=(x^3,y)$ and $g(u,v)=(\sqrt[3]{u},v)$, continuity and both inverse identities hold. The derivative $A(h,k)=(0,k)$ at zero has no linear left inverse, and the inverse quotient in the first coordinate is $u^{-2/3}$ for $u>0$. The continuity premise is substantive too. On $\mathbb R$, take $f(t)=t$ for $|t|<1/4$, $f(t)=t-1$ for $|t-1|<1/4$, and $f(t)=0$ elsewhere. Set $g(0)=0$ and $g(y)=1+y$ for $y\ne 0$. Then $f(g(y))=y$ near zero and the forward derivative at $g(0)$ is $1$, while $g$ jumps at zero.

**Remark (approximation and the chart consumers).** For two points in a source where $\|\Delta f-Ad\|\le c\|d\|$, put $N=\|A^{-1}\|$ in the nonzero case. If $c<N^{-1}$, then $\|\Delta f\|\ge(N^{-1}-c)\|d\|$. On the image this bounds the inverse increment, yielding inverse continuity. Applying $A^{-1}$ to the forward remainder gives an inverse approximation constant $Nc/(N^{-1}-c)$. The zero space is handled separately. Openness in the [strict inverse construction](#strict-inverse-chart-for-etale-local-sections) uses the cited closed-ball covering theorem with source completeness. The differential consumer <code>HasStrictFDerivAt.to_localInverse</code> calls <code>OpenPartialHomeomorph.hasStrictFDerivAt_symm</code>, which uses cancellation. If a supplied $g$ satisfies $g\circ f=\operatorname{id}$ near the source, transport this equality along the constructed continuous inverse and use the target identity to identify their germs. This is the direction used by <code>HasStrictFDerivAt.to_local_left_inverse</code>. [Mathlib ApproximatesLinearOn.lean:312–399](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean#L312) · [Mathlib InverseFunctionTheorem/FDeriv.lean:145–198](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean#L145)

In A2, <code>AnChart.lean:29–68</code> constructs the polynomial coordinate map $\Psi$, computes its derivative $L_m$, proves injectivity by the gradient criterion, obtains surjectivity by equal finite dimensions and packages the equivalence as $\mathrm{Le}$. Analyticity supplies the strict derivative and <code>toOpenPartialHomeomorph</code> constructs $\Phi$. These data imply the inverse derivative $\mathrm{Le}^{-1}$ at $\Phi(p)$ and the slice derivative $\mathrm{Le}^{-1}J$ at the slice center. The actual call at line 68 is <code>analyticAt_symm'</code> for inverse analyticity. FDeriv/Analytic.lean:414–430 identifies the first coefficient by the forward derivative and calls <code>hasFPowerSeriesAt_symm</code>. That proof uses the [positive inverse radius](#a-positive-radius-for-the-inverse-series) and [composite sum recovery](#ordered-composition-of-multilinear-power-series), with the source and target inverse identities and transport by inverse continuity. At <code>AnChart.lean:86–95</code>, the archive composes the analytic inverse with the analytic zero-slice inclusion. The differential calculation above is a consequence of the chart data. The analytic call follows the series route. The [étale-section producer](#holomorphic-local-sections-of-étale-families) also follows that route: <code>Imports.lean:141–148</code> restricts the chart and invokes <code>analyticAt_symm</code> pointwise at its target. [Mathlib FDeriv/Analytic.lean:414–430](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean#L414) · [Mathlib Inverse.lean:656–694](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Inverse.lean#L656) · [A2 source record](../sources/SOURCES.md#chapter-12--derivative-cancellation-for-a-given-inverse-chart)

#### Jacobian cuts and dual-number tangent injectivity

**Motivation.** Suppose a complex affine algebraic set is given by an ideal $K$ in $n$ variables. At a point $p$ its local ring is regular of dimension $e$, and we are given $e$ polynomial functions that generate the local maximal ideal. To use the analytic inverse theorem, we need $n$ functions on the ambient space. Which $n-e$ equations should we add, why does their common zero set agree locally with the original one, and why is the combined derivative invertible? A cotangent computation supplies the equations. A denominator clears the remaining relations near $p$. Evaluating at $p+\epsilon v$, with $\epsilon^2=0$, tests the derivative before we invoke the analytic inverse.

##### Two calculations

**A reducible curve and an unwanted line.** In $\mathbb C^2$, take the two lines $y=0$ and $y=1$ and put $p=(0,0)$. Their ideals are comaximal since $y-(y-1)=1$. Thus their union has ideal $K=(q)$ with $q=y(y-1)$. Choose $F=(y-2)q\in K$ and $J=(F)$. Its gradient at $p$ is $(0,2)$. Its zero set also contains the line $y=2$, where $q=2$. In particular $q\notin J$. More precisely, if $hq\in J$, write $hq=b(y-2)q$ for some polynomial $b$. Cancelling $q$ in the polynomial domain gives $h=b(y-2)$. The choice $h=y-2$ has $h(p)=-2$ and gives $hK=J$. For this choice of $F$, the denominator removes a genuine extra branch.

In the local ring at $p$, both $y-2$ and $y-1$ are units, so $J$ and $K$ both extend to $(y)$. The quotient local ring is $\mathbb C[x]_{(x)}$, regular of dimension one, and $r_1=x$ generates its maximal ideal. The derivative of $(r_1,F)$ at $p$ is the diagonal matrix with entries $1,2$. On a polydisc $|x|,|y|<1/2$, the zero slice of $F$ gives exactly $y=0$ and the parametrization is $w\mapsto(w,0)$ for $|w|<1/2$. A global choice $F=q$ would allow $h=1$ in this example. The calculation shows why the gradient test alone on the chosen $F$ only supplies a local cut.

**A smooth curve in three variables.** Take $K=(F_1,F_2)$ with $F_1=y-x^2$, $F_2=z-xy$, and $p=(1,1,1)$. Eliminating $y$ and $z$ identifies the quotient with $\mathbb C[x]$, by substitution $(x,y,z)=(x,x^2,x^3)$. The kernel is exactly $K$: one can first replace $z$ by $xy$ modulo $F_2$, then replace $y$ by $x^2$ modulo $F_1$. At $p$ the local ring is $\mathbb C[x]_{(x-1)}$, and $r_1=x-1$ generates its maximal ideal. Here $h=1$ works. The cotangent relations are $[y-1]=2[x-1]$ and $[z-1]=[x-1]+[y-1]=3[x-1]$. To compute the tangent, substitute
$$
(x,y,z)=(1+\epsilon a,1+\epsilon b,1+\epsilon c).
$$
The equations evaluate to $\epsilon(b-2a)$ and $\epsilon(c-a-b)$. Their common kernel consists of $(a,2a,3a)$, and $r_1$ evaluates to $\epsilon a$. Hence annihilating all three entries forces $a=b=c=0$. The matrix of $(r_1,F_1,F_2)$ at $p$ has rows $(1,0,0),(-2,1,0),(-1,-1,1)$ and determinant one. In fact its inverse at $(w,s,t)$ is obtained by setting
$$
X=1+w,\qquad Y=X^2+s,\qquad Z=XY+t.
$$
Substitution gives $(r_1,F_1,F_2)(X,Y,Z)=(w,s,t)$, and solving in the same order also recovers the input on a forward image. On the zero slice the inverse is $g(w)=(1+w,(1+w)^2,(1+w)^3)$ with $Dg(0)(a)=(a,2a,3a)$.

##### Definitions and the cotangent dimension lemma

Let $A=\mathbb C[X_1,\ldots,X_n]$, $M=\ker(\operatorname{ev}_p)$ and $S=A\setminus M$. Put $B=A_M$, $R_K=B/KB$ and write $\psi:A\to R_K$ for the composite map. Assume $R_K$ is a nonzero local ring. Then $K\subseteq M$, because an element of $K$ with nonzero evaluation becomes a unit in $B$ and makes the quotient zero. The ideal $M$ is generated by $X_j-p_j$, as is seen by expanding in the shifted variables. Evaluation extends to $R_K$ by $a/s\mapsto a(p)/s(p)$, is surjective via constants, and has kernel $\mathfrak m=MR_K$. Thus the residue field is $\mathbb C$. The cotangent space at the point is $\mathfrak m/\mathfrak m^2$. Write $\nabla_p f=(\partial_j f(p))_j$ and $W_K=\operatorname{span}_{\mathbb C}\{\nabla_p f:f\in K\}$.

**Lemma (cotangent dimension).** The linear map
$$
\Phi:\mathbb C^n\longrightarrow\mathfrak m/\mathfrak m^2,
\qquad c\longmapsto\left[\psi\left(\sum_j c_j(X_j-p_j)\right)\right]
$$
is surjective with kernel $W_K$. Consequently $\dim_{\mathbb C}(\mathfrak m/\mathfrak m^2)+\dim_{\mathbb C} W_K=n$.

**Proof.** Expansion in shifted variables gives
$$
f-f(p)-\sum_j\partial_j f(p)(X_j-p_j)\in M^2.
$$
For $f\in M$ this gives $[\psi(f)]=\Phi(\nabla_p f)$, the identity <code>toCot_psi</code>. Every element of $\mathfrak m$ is represented by $a/s$ with $a\in M$ and $s(p)\ne0$. In $\mathfrak m/\mathfrak m^2$, multiplying by the inverse of $\psi(s)$ acts by $s(p)^{-1}$, because the difference between the inverse and its residue belongs to $\mathfrak m$. This proves surjectivity.

If $f\in K$, its image is zero, so $W_K\subseteq\ker\Phi$. Conversely, for $c\in\ker\Phi$ let $\ell=\sum_j c_j(X_j-p_j)$. Then $\psi(\ell)\in\mathfrak m^2$. Lifting to $B$ puts $\ell/1$ in $(M^2+K)B$. The contraction rule for localization gives $s\in S$ with $s\ell=q+k$, $q\in M^2$, $k\in K$. This rule follows by writing the localized ideal element as a single fraction with numerator in the ideal and clearing denominators in the equality. The product rule gives $\nabla_p(s\ell)=s(p)c$ because $\ell(p)=0$. Every element of $M^2$ has zero gradient by the same rule, so $s(p)c=\nabla_p k$. Division by the nonzero scalar $s(p)$ gives $c\in W_K$.

Rank–nullity first gives the formula over $\mathbb C$. The archive's <code>finrank_residueField</code> identifies $1$ as a basis of the residue field over $\mathbb C$: the class of any element equals the class of its evaluation. The scalar tower and dimension multiplication then give <code>finrank_cot_eq</code> over the residue field.

##### The local Jacobian cut

**Lemma.** Suppose $R_K$ is regular local of Krull dimension $e$. Then $e\le n$ and there are $n-e$ polynomials $F_i\in K$ with independent gradients at $p$ and a polynomial $h$ satisfying
$$
h(p)\ne0,\qquad hK\subseteq J=(F_1,\ldots,F_{n-e}).
$$
In particular $K$ and $J$ extend to the same ideal in $A[1/h]$, and their common zero sets agree on $h\ne0$.

**Proof.** A Noetherian local ring is regular when its Krull dimension equals its embedding dimension, the dimension of its maximal ideal modulo its square over the residue field. Nakayama identifies this last dimension with the minimum number of generators of the maximal ideal. The cotangent dimension lemma gives $\dim W_K=n-e$. Choose a basis from the gradients of elements of $K$, and choose a polynomial $F_i$ for each basis member. Since $J\subseteq K$ and all these gradients are in $W_J$, we have $W_J=W_K$. The ring $R_J=B/JB$ is Noetherian and local since $J\subseteq M$. The surjection $R_J\to R_K$, the local dimension bound by embedding dimension, and the cotangent dimension calculation give
$$
e=\dim R_K\le\dim R_J\le
\dim_{\mathbb C}(MR_J/(MR_J)^2)=e.
$$
Thus $R_J$ is regular local. Use the regular-local domain theorem <code>ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain</code> to conclude that it is a domain. The production proof and the general dimension-drop input are given in [Why a regular local ring is a domain](#why-a-regular-local-ring-is-a-domain). The [height subsection](#how-krulls-height-theorem-bounds-local-dimension) supplies the bound used to establish regularity at the preceding step.

If $KB/JB$ were a nonzero ideal of $R_J$, choose a nonzero element $u$ in it. The quotient $R_J/(u)$ surjects onto $R_K$. Since $u$ is a nonzerodivisor, the input <code>ringKrullDim_quotient_succ_le_of_nonZeroDivisor</code> gives
$$
e+1\le\dim(R_J/(u))+1\le\dim R_J=e,
$$
a contradiction. In this domain case the dimension loss can also be seen by lifting a prime chain from $R_J/(u)$ and prepending the zero prime. Thus $JB=KB$.

For each $g\in K$, contraction supplies $s_g\in S$ with $s_g g\in J$. Hilbert's basis theorem gives a finite generating set $g_1,\ldots,g_m$ of $K$. Take $h=\prod_i s_{g_i}$, with empty product $1$. Its value at $p$ is nonzero, and $hg_i\in J$ for every generator. If $g=\sum_i a_i g_i$, then $hg=\sum_i a_i(hg_i)\in J$. Inverting $h$ proves equality of the extended ideals. At an ordinary point with $h(y)\ne0$, each equality $h(y)g(y)=0$ can be divided by $h(y)$. This gives the asserted equality of zero sets there.

**Remark.** <code>JacChartB.lean</code> uses the inequalities $n-e\le\dim W_J$ and $\dim_{\mathbb C}(MR_J/(MR_J)^2)\le e$ in this squeeze. <code>JacChartC.lean</code> supplies the converse regularity criterion under a separate minimal-prime height hypothesis. The forward cut uses the already-assumed regularity of $R_K$.

##### Dual numbers and tangent injectivity

Write $D=\mathbb C[\epsilon]/(\epsilon^2)$. The algebra map <code>dualEv</code> sends $X_j$ to $p_j+\epsilon v_j$. In Lean it has type `MvPolynomial (Fin n) ℂ →ₐ[ℂ] DualNumber ℂ`. The constant and nilpotent components are
$$
\operatorname{dualEv}_{p,v}(f)=f(p)+\epsilon\sum_j\partial_j f(p)v_j.
$$
Indeed, the formula holds on constants and on $X_j$. It is additive, and multiplying two such expressions gives the product rule since $\epsilon^2=0$. In particular all pairings here are complex bilinear, with no conjugates. An element $a+\epsilon b$ is a unit exactly when $a\ne0$: its inverse is $a^{-1}-\epsilon b a^{-2}$, and reduction modulo $\epsilon$ proves necessity.

**Lemma (tangent injectivity).** Suppose $R_K$ is local and $F_i\in K$, $h(p)\ne0$, and $hK\subseteq(F_i)$. Suppose the images of the $r_i\in A$ generate $MR_K$. If $\nabla_p F_i\cdot v=0$ and $\nabla_p r_i\cdot v=0$ for all indices, then $v=0$. The lemma works for any number of $F_i$ and requires only the stated ideal containment.

**Proof.** Each $F_i$ lies in $M$ by the unit argument for a nonzero local quotient. Its dual evaluation therefore has both components zero, so the evaluation kills $(F_i)$. For $k\in K$, it kills $hk$, and $\operatorname{dualEv}_{p,v}(h)$ is a unit. Hence it kills $K$. Every $s\in S$ also has unit dual evaluation. The universal properties of localization and quotient now give the ring map
$$
\chi_v:R_K\longrightarrow D,
\qquad [a/s]\longmapsto
\operatorname{dualEv}_{p,v}(a)\operatorname{dualEv}_{p,v}(s)^{-1}.
$$

The archive also constructs $\chi_0$, the lift at the zero vector. This map sends $[a/s]$ to the scalar $a(p)/s(p)$ and kills $MR_K$. Each image $\psi(r_i)$ belongs to that ideal by the generation hypothesis, so $\chi_0(\psi(r_i))=r_i(p)=0$. The assumed derivative equations then give $\chi_v(\psi(r_i))=0$. Its kernel is an ideal and contains all of $MR_K$ by generation. In particular it kills every $\psi(X_j-p_j)$. Evaluating there gives $\epsilon v_j=0$, which implies $v_j=0$ by taking the nilpotent coefficient. Equivalently, a tangent vector of the algebraic germ is a dual-number lift of the residue map, and it is determined by its values on the local maximal ideal generators.

##### Closing the holomorphic chart

**Theorem.** Keep the regular local hypotheses of the cut lemma, and take $e$ polynomials $r_1,\ldots,r_e$ whose images generate $MR_K$. There are an ambient open neighborhood $U$ of $p$, an open neighborhood $V$ of $0$ in $\mathbb C^e$, and a holomorphic parametrization $g:V\to\mathbb C^n$ bijective onto $U\cap Z(K)$. Its inverse on that set is $y\mapsto r(y)=(r_i(y))_i$.

**Proof.** Use the cut to construct
$$
\Psi(y)=(r(y),F(y))\in\mathbb C^e\times\mathbb C^{n-e}.
$$
Both blocks vanish at $p$. The derivative has rows $\nabla_p r_i$ and $\nabla_p F_i$. Its kernel is zero by the tangent injectivity lemma. Since $e+(n-e)=n$, the derivative is a complex linear isomorphism. Polynomial analyticity gives the strict derivative at $p$. Apply the already published strict and analytic inverse construction to obtain a local open chart with inverse $I$ holomorphic on an open target neighborhood $T_0$ of $(0,0)$. The archived call is <code>analyticAt_symm'</code>. Shrink the source to the intersection of the inverse chart's source, $\{h\ne0\}$, and $\Psi^{-1}(T_0)$, and call it $U$. Let $T$ be the image of $U$ under the chart. It is open, $I$ is analytic on it, and $\Psi$ and $I$ have both inverse identities there. [Strict inverse chart](#strict-inverse-chart-for-etale-local-sections) · [Positive radius](#a-positive-radius-for-the-inverse-series) · [Ordered composition](#ordered-composition-of-multilinear-power-series)

The set $V=\{w:(w,0)\in T\}$ is open since it is the preimage under $j(w)=(w,0)$. It contains $0$. Define $g=I\circ j$ on $V$. Composition gives holomorphy on $V$. From $\Psi(g(w))=(w,0)$ we get $F(g(w))=0$ and $r(g(w))=w$. Since $h(g(w))\ne0$, the cut gives $g(w)\in Z(K)$. Conversely, if $y\in U\cap Z(K)$ then $F(y)=0$, so $(r(y),0)=\Psi(y)\in T$. The source identity gives $g(r(y))=y$. These identities establish the claimed bijection. The inherited inverse derivative gives $Dg(0)v=D\Psi(p)^{-1}(v,0)$. [Forward composition on restricted sets](#forward-composition-on-restricted-sets) · [Inverse-chart derivative](#derivative-cancellation-for-a-given-inverse-chart)

At <code>AtlasA.lean:97</code>, <code>AlgRes.exists_goodChart</code> provides $K$, $p$ and the regularity and dimension from the ambient algebraic model of an existing patch. It pulls the ambient parametrization back along the patch's embedding into $Z(K)$. On the chart source the forward map is evaluation of $r$ in those ambient coordinates, and the returned ambient inverse is $g$. The downstream chart can be restricted to a specified open neighborhood of the original point. [Declaration and consumer map](../sources/SOURCES.md#chapter-12-jacobian-cuts-and-dual-number-tangent-injectivity)

##### Remarks on the hypotheses and source scope

- **Singularity.** For $K=(xy)$ at the origin of $\mathbb C^2$, the two coordinate axes have local dimension one. The gradient of every element of $K$ vanishes there by the product rule, so the cotangent space has dimension two. There is no independent gradient for the required one-equation cut. Even the supplied function $r=x+y$ has the nonzero common null vector $(1,-1)$ with $F=xy$. The single image of $r$ cannot generate the maximal ideal because its cotangent space is two-dimensional. On each axis, points arbitrarily close to the origin give the same small value of $r$, preventing a chart with that coordinate.
- **A vanishing multiplier.** At the origin let $K=(y)$, $F=xy$, $h=x$ and $r=x$. The local ring is regular of dimension one, the image of $r$ generates its maximal ideal, and $hK=(F)$. But $h(0)=0$. For $v=(0,1)$ the dual evaluations of $F,r,h$ vanish while that of $y$ is $\epsilon\ne0$. Thus descent fails and the extra axis of $Z(F)$ passes through $p$. In the regular setting, if the full required number of $F_i$ already have independent gradients, the dimension argument above supplies a new multiplier that is a unit at $p$. This example isolates the missing unit hypothesis in the tangent lemma.
- **Insufficient coordinate generators.** Keep $K=(y)$ at the origin and take $F=y$, $h=1$, $r=x^2$. In $\mathbb C[x]_{(x)}$, $(x^2)$ is strictly smaller than $(x)$: $x=x^2 a/s$ would imply $s=xa$ with $s(0)\ne0$. The direction $(1,0)$ kills $F$ and $r$ under dual evaluation, although it sends $x$ to $\epsilon$. On the line, $x$ and $-x$ have the same $r$-value in every neighborhood of zero.

**Source scope [Lean, read].** The cut, the dual-number proof and the chart assembly have author-level local R3 proof-body readings. The [algebra subsection](#why-a-regular-local-ring-is-a-domain) reads the production bodies of the regular-local domain theorem and the general nonzerodivisor dimension-drop theorem. The earlier analytic inputs retain their individual reviews, and the formal chain's kernel replay and independent review of this subsection are separate verification steps. The calculations and failure tests are textbook deductions. [Source and attribution record](../sources/SOURCES.md#chapter-12-jacobian-cuts-and-dual-number-tangent-injectivity)

#### Why a regular local ring is a domain

In the [Jacobian cut](#the-local-jacobian-cut), $B$ is the complex polynomial ring localized at the evaluation ideal of $p$, and $J\subseteq K$ are the cut and original ideals. The cut produces a regular local ring $R_J$ whose dimension already agrees with that of the intended local ring $R_K$. To rule out a nonzero kernel of $R_J\to R_K$, it needs every nonzero element of $R_J$ to be a nonzerodivisor. The archive proves this by cutting a regular local ring by one parameter, applying induction to the smaller ring, and using Nakayama's lemma on a minimal prime of the original ring.

##### Two local rings by hand

**The plane at the origin.** Let $k$ be any field, $A=k[x,y]_{(x,y)}$, and $\mathfrak m=(x,y)A$. This is local Noetherian, by localization and the Hilbert basis theorem. Write $s=s_0+s_1+\cdots$ in homogeneous pieces with $s_0\ne0$. Modulo $\mathfrak m^2$, the inverse denominator is $s_0^{-1}-s_0^{-2}s_1$, so the first-order part of $f/s$ for $f\in(x,y)$ is $f_1/s_0$. The first-order map kills precisely $\mathfrak m^2$, and sends $x,y$ to the two coordinate vectors. Thus $\dim_k\mathfrak m/\mathfrak m^2=2$. The chain $(0)\subsetneq(x)A\subsetneq\mathfrak m$ has length two since the polynomial ring is a domain and $A/(x)\simeq k[y]_{(y)}$. The height theorem applied to the two generators of $\mathfrak m$ gives the upper bound two. Hence $A$ is regular.

The parameter $u=x+y$ can replace $x$ in the cotangent basis. Substituting $x=-y$ passes through localization because denominators keep their nonzero constant term. It identifies $A/(u)$ with $k[y]_{(y)}$, of dimension and cotangent dimension one. Every nonzero element of the latter is a unit times a power of $y$, so its only primes are $(0)$ and $(y)$. For a check on zero divisors in $A$ itself, take nonzero fractions $f/s,g/t$ with lowest nonzero homogeneous parts $f_a,g_b$. The lowest part of the product is $f_ag_b/(s_0t_0)$ in degree $a+b$, which is nonzero in $k[x,y]$. For example
$$
\frac{x+2y^2}{1-y}\frac{y+x^2}{1+x}
$$
has first nonzero homogeneous part $xy$ in degree two, in every characteristic. This calculation uses ordinary polynomial multiplication in this particular ring.

**A discrete valuation ring.** In $D=k[[t]]$, any nonzero series $f$ has a first nonzero coefficient $a_i$ and factors as $t^iv$, with $v$ invertible by recursively solving for its inverse coefficients. The product of series with first nonzero terms $a_it^i$ and $b_jt^j$ starts with $a_ib_jt^{i+j}$. For instance $t^2(1-t)\,t^3(1+t)=t^5-t^7$. Each nonzero ideal contains a series of least order $r$, hence contains $t^r$, and every member is divisible by $t^r$. Thus every nonzero ideal is $(t^r)$. This proves Noetherianity, locality with maximal ideal $(t)$, and the discrete valuation description. The zero ideal is prime by the product computation. The only other prime is $(t)$, since a prime containing a power of $t$ contains $t$. The chain has length one and $t\bmod t^2$ gives a one-dimensional cotangent space. The parameter $t$ gives the field $D/(t)=k$. By comparison $D/(t^2)$ has dimension zero, cotangent dimension one, and the nonzero square-zero class of $t$. A nonzero nonunit in a regular local ring can lower dimension while giving a nonregular quotient.

##### Definitions and the dimension bounds

All rings in the proof are commutative with identity. A local ring $R$ has a unique maximal ideal $\mathfrak m$ and residue field $\kappa=R/\mathfrak m$. Chain length counts strict inclusions. Write $\mu_R(\mathfrak m)$ for the least cardinality of an ideal generating set, which is finite for Noetherian $R$. The pinned Mathlib class <code>IsRegularLocalRing R</code> extends locality and Noetherianity, and its field <code>spanFinrank_maximalIdeal</code> equates this number with $\dim R$. In particular a regular local ring has finite dimension. The residue field acts on $\mathfrak m/\mathfrak m^2$ because $\mathfrak m$ kills that quotient. Images of ideal generators span it. Conversely, if elements span it after reduction, the ideal $L$ they generate satisfies $\mathfrak m=L+\mathfrak m^2$. The finite module $\mathfrak m/L$ equals $\mathfrak m(\mathfrak m/L)$, and Nakayama gives $\mathfrak m=L$. Thus
$$
\mu_R(\mathfrak m)=\dim_\kappa\mathfrak m/\mathfrak m^2.
$$
Lifts of a cotangent basis in a regular local ring form a regular system of parameters. This description of the generators is available at the start of the proof. [Stacks 00KU](https://stacks.math.columbia.edu/tag/00KU) · [Nakayama, Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV)

The two height bounds apply to Noetherian local rings with possible zero divisors. They give $\dim R\le\mu_R(\mathfrak m)$ and $\dim R\le\dim(R/(F))+|F|$ for $F\subseteq\mathfrak m$ finite. Here $F=\{u\}$. The [height subsection](#how-krulls-height-theorem-bounds-local-dimension) proves both bounds along the pinned Mathlib chain, beginning with the principal ideal theorem.

##### Lemma. Cutting by a cotangent basis element

Let $R$ be regular local and $u\in\mathfrak m\setminus\mathfrak m^2$. Then $S=R/(u)$ is regular local and $\dim S+1=\dim R$.

Indeed, $(u)\subseteq\mathfrak m$, so $S$ is a nonzero Noetherian local ring with maximal ideal $\mathfrak n=\mathfrak m/(u)$ and residue field $\kappa$. Let $d=\mu_R(\mathfrak m)=\dim R$. Express the nonzero class of $u$ in a basis $b_1,\ldots,b_d$ of the cotangent space. If its $j$-th coefficient is $c_j\ne0$, solve for $b_j=c_j^{-1}(\overline u-\sum_{i\ne j}c_i b_i)$. Lift the surviving basis vectors to $\mathfrak m$. Together with $u$, their lifts generate $\mathfrak m$ by Nakayama. The surviving images in $S$ generate $\mathfrak n$, so $\mu_S(\mathfrak n)+1\le d$. Combining the two dimension inputs gives
$$
d\le\dim S+1\le\mu_S(\mathfrak n)+1\le d.
$$
All numbers here are finite and $S\ne0$, so every inequality is equality. This is the argument of <code>spanFinrank_quotient_eq_and_ringKrullDim_add_one</code>. Its quotient bound establishes the first inequality for an element of the maximal ideal before any claim about multiplication by $u$.

##### Theorem. A Noetherian regular local ring is a domain

Use induction on $\mu_R(\mathfrak m)$, with the induction hypothesis available for every regular local ring having smaller generator number. If $\mathfrak m=\mathfrak m^2$, Nakayama on the finite module $\mathfrak m$ gives $\mathfrak m=0$, and $R$ is a field. This covers generator number zero. In the other case the maximal ideal is not a minimal prime. Indeed, if a minimal prime contains $\mathfrak m$, it must equal $\mathfrak m$. Every prime is then equal to $\mathfrak m$ by minimality and locality. This forces $\dim R=0$, so the cotangent space has dimension zero by regularity and $\mathfrak m=\mathfrak m^2$.

There are finitely many minimal primes in a Noetherian ring. One way to see the finiteness is to choose an ideal $I$ maximal among ideals with infinitely many minimal primes above them. Such an ideal is proper and nonprime, so there are $a,b\notin I$ with $ab\in I$. Every prime minimal over $I$ contains $a$ or $b$, and is then minimal over $I+(a)$ or $I+(b)$, respectively. Both larger ideals have finitely many minimal primes, a contradiction. Apply finite prime avoidance to these minimal primes of $R$ and the one extra ideal $\mathfrak m^2$. The prime avoidance lemma allows this extra ideal even though it may be nonprime. The ideal $\mathfrak m$ is contained in none of the listed ideals. For this variant of prime avoidance, discard any listed ideal contained in another. If a minimal sublist still covers $\mathfrak m$, it must have at least two members. For two members add an element exclusive to each, which gives an element outside both. For a list of at least three, choose a prime member $P$. Minimality of the cover gives $a\in\mathfrak m$ in $P$ alone. Take $b\in\mathfrak m\setminus P$ and multiply it by one element of each other member outside $P$. The product lies in every other member and outside $P$ by primality. Adding it to $a$ escapes the entire cover. Hence there is a single $u\in\mathfrak m\setminus\mathfrak m^2$ outside every minimal prime. [Finiteness, Stacks 00FR](https://stacks.math.columbia.edu/tag/00FR) · [Prime avoidance, Stacks 00DS](https://stacks.math.columbia.edu/tag/00DS)

The lemma gives a regular local quotient $S=R/(u)$ with $\mu_S(\mathfrak n)=\mu_R(\mathfrak m)-1$. By induction $S$ is a domain, so $(u)$ is prime. Choose a minimal prime $\mathfrak p\subseteq(u)$ of $R$. Every prime contains a minimal prime, by applying Zorn's lemma to the primes below it using intersections of descending chains. For $z\in\mathfrak p$ write $z=uw$ since $\mathfrak p\subseteq(u)$. Primality and $u\notin\mathfrak p$ imply $w\in\mathfrak p$, proving $\mathfrak p=u\mathfrak p$. Noetherianity makes $\mathfrak p$ finitely generated and $u\in\mathfrak m$ belongs to the Jacobson radical. Nakayama now gives $\mathfrak p=0$. The primality of the zero ideal now gives the desired alternative. If $ab=0$, one of $a,b$ is zero. This is the production proof in <code>ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain</code>. [Minimal primes under a given prime, Stacks 00E0](https://stacks.math.columbia.edu/tag/00E0) · [Source and consumer map](../sources/SOURCES.md#chapter-12-regular-local-rings-and-principal-dimension-drop)

**A classical comparison.** Stacks Lemma 10.106.2 proves the same theorem using the polynomial associated graded ring from Lemma 10.106.1 and Krull intersection. In that proof a nonzero element has a finite last degree of membership in the powers of $\mathfrak m$, because their intersection is zero. For a product of two nonzero elements the leading classes multiply to a nonzero class in the sum of the two degrees. The A2 proof above gets the required vanishing by applying Nakayama to one finitely generated prime satisfying $\mathfrak p=u\mathfrak p$. Iterating divisibility by $u$ alone would require a separation theorem to give the same conclusion. [Associated graded, Stacks 00NO](https://stacks.math.columbia.edu/tag/00NO) · [Krull intersection, Stacks 00IP](https://stacks.math.columbia.edu/tag/00IP) · [Domain theorem, Stacks 00NP](https://stacks.math.columbia.edu/tag/00NP)

##### The distinct dimension drop used by the Jacobian cut

For any commutative ring $T$ and any nonzerodivisor $v\in T$, the pinned <code>ringKrullDim_quotient_succ_le_of_nonZeroDivisor</code> gives
$$
\dim(T/(v))+1\le\dim T.
$$
For a proper $(v)$, lift a chain from $T/(v)$ to primes of $T$ containing $v$. Below the first prime choose a minimal prime of $T$. It avoids $v$. Indeed, localizing at that minimal prime leaves just one prime, whose elements are all nilpotent there. Multiplication by $v$ stays injective after localization, and a nilpotent element of a nonzero ring cannot act injectively. Thus the minimal prime strictly precedes the lifted chain. Taking the supremum of chain lengths yields the bound. If $v$ is a unit, the quotient has empty spectrum and Mathlib uses dimension $\bot$, with $\bot+1=\bot$. A proper quotient and finite $\dim T$ give an ordinary strict inequality. This proof of the successor bound uses neither locality nor Noetherianity. [Pinned successor bound, lines 37–55](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean#L37-L55)

In <code>JacChartB.lean:227–239</code>, the domain theorem applies to the already regular $R_J$. If the kernel $\mathfrak a=KB/JB$ of $R_J\to R_K$ is nonzero, choose $v\ne0$ in $\mathfrak a$. The domain hypothesis converts nonzero to nonzerodivisor. The nonzero local ring $R_K$ makes $\mathfrak a$ proper, so $v$ is a nonunit. The surjection $R_J/(v)\to R_K$ then gives
$$
e+1=\dim R_K+1\le\dim(R_J/(v))+1\le\dim R_J=e.
$$
The contradiction eliminates the kernel. Here Noetherianity entered the regularity criterion and the production domain proof. Finite dimension $e$ permits the final comparison. The consumer uses the successor bound after proving the domain property, whereas the induction uses the height-theorem bound to establish regularity of the smaller quotient. [Return to the Jacobian cut](#the-local-jacobian-cut)

##### Hypothesis tests

**The crossing.** In $C=k[x,y]_{(x,y)}/(xy)$, every prime contains the image of $x$ or $y$. The axis quotients $k[y]_{(y)}$ and $k[x]_{(x)}$ each have just two primes. Thus the full prime set consists of $(\bar x),(\bar y),(\bar x,\bar y)$, with the first two incomparable and strictly below the last. The dimension is one. Since $xy\in(x,y)^2$, the quotient has exactly the same first-order classes of $x,y$ as the plane, of dimension two. The two nonzero classes $\bar x,\bar y$ survive in opposite axis quotients and multiply to zero. In particular the nonzero nonunit $\bar x$ gives $C/(\bar x)\simeq k[y]_{(y)}$ of the **same** dimension. The nonzerodivisor condition on the successor bound matters even in a reduced Noetherian local ring. The intersection of the two axis ideals in the plane local ring is $(xy)$, by divisibility by the distinct prime elements $x,y$, which proves reducedness of $C$.

**The double point.** In $E=k[\epsilon]/(\epsilon^2)$, an element $a+b\epsilon$ is a unit precisely when $a\ne0$, with inverse $a^{-1}-a^{-2}b\epsilon$. The finite-dimensional $k$-algebra is Noetherian, with sole prime $(\epsilon)$ because every prime contains the nilpotent $\epsilon$ and the quotient by it is $k$. Hence its dimension is zero. The maximal ideal has square zero and cotangent dimension one. The nonzero element $\epsilon$ annihilates itself. In both controls the ring is local and Noetherian, but the cotangent generator count exceeds the Krull dimension.

**Where finiteness enters.** Dropping Noetherianity and keeping the numerical cotangent equality alone can give a false criterion. Take the union of $k[t_n]/(t_n^{2^n})$, for $n\ge1$, along the injective substitution $t_n\mapsto t_{n+1}^2$. Injection follows from the distinct surviving even powers. Every element has a well-defined constant term, and every element of zero constant term is nilpotent, since it belongs to one finite stage. The common kernel of the constant-term map is the sole prime and maximal ideal $\mathfrak m$. It is nonzero and equals $\mathfrak m^2$, because each $t_n=t_{n+1}^2$ and each element of $\mathfrak m$ is divisible by some $t_n$ in its stage. Thus both numerical dimensions are zero, and $t_1\ne0$ satisfies $t_1^2=0$. The ideal $\mathfrak m$ cannot be finitely generated, by Nakayama. This tests the cotangent reformulation with its Noetherian hypothesis removed. Locality is also essential to the domain conclusion from regularity at points: $k\times k$ has field localizations at both primes and $(1,0)(0,1)=0$.

**Reading scope [Lean, read].** The local R3 reading covers the A2 induction from the cotangent replacement through zero primality and the pinned Mathlib successor bound through the chain argument. The classical height theorem has its own [proof and reading scope](#how-krulls-height-theorem-bounds-local-dimension). Verification of the deeper dependency cone and Main kernel replay remain [Open]. The earlier chart proof retains its separate review record. [Pinned sources and attribution](../sources/SOURCES.md#chapter-12-regular-local-rings-and-principal-dimension-drop)

#### How Krull's height theorem bounds local dimension

The [regular-local domain proof](#why-a-regular-local-ring-is-a-domain) needs two dimension inequalities before it can use its induction hypothesis. One bounds the dimension of a local ring by the number of generators of its maximal ideal. The other bounds the dimension lost on passing to a quotient. Both come from heights of primes minimal over generated ideals. We follow the proofs in pinned Mathlib, including the passage from prime heights in the quotient back to dimension in the original ring. [Reading guide](../notes/outline.md#krull-height-supply) · [Proof map](../notes/proof-map.md#krull-height-supply) · [Sources and declarations](../sources/SOURCES.md#chapter-12-krull-height-and-dimension)

##### Two parameter cuts

Let $A=k[x,y]_{(x,y)}$. Killing $x+y$ leaves $k[y]_{(y)}$. The primes containing $(x+y)$ form a chain of length one, whereas $(0)\subsetneq(x+y)\subsetneq(x,y)A$ has length two. A second cut by $y$ leaves $k$. This is the expected behavior of two parameters in a plane.

Now impose $xy=0$ before making the cuts. In $B=k[x,y]_{(x,y)}/(xy)$, killing $x$ leaves the $y$-axis with its dimension intact. Killing $x+y$ instead leaves a ring supported at the origin, with a nonzero square-zero element. The generator bound applies to both cuts. The comparison in the other direction, from the dimension of the quotient plus one to that of the original ring, uses the separate nonzerodivisor input in the [Jacobian cut](#the-local-jacobian-cut). We compute the heights below.

##### Heights, localization and the two chain tests

Write $(F)$ for the ideal generated by a finite set $F$, and $\mu(I)$ for the least number of generators of a finitely generated ideal $I$. For a prime $p$, $\operatorname{ht}p$ is the supremum of lengths of finite strict prime chains ending at $p$. Length counts inclusions. The height of a general ideal $I$ is the infimum of heights of the primes minimal over $I$. A proper ideal has such a prime below any specified prime containing it. In a Noetherian ring the minimal primes over each ideal are finite, by the ACC argument in the [minimal-prime finiteness subsection](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes). In the order proof, a nonempty descending chain of primes containing $I$ has prime intersection containing $I$. Indeed, if both factors of a product are missing somewhere in the chain, a smaller member misses both. Zorn's lemma gives a minimal prime below the specified prime. [Height.lean:30–51](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/Height.lean#L30-L51) · [MinimalPrime/Basic.lean:75–96](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean#L75-L96)

Here are the order operations used throughout the proof.

- For $A=S^{-1}R$, every ideal $L\subseteq A$ is the extension of its contraction. If $a/s\in L$, multiplication by the unit $s/1$ puts $a$ in the contraction, and division by that same unit recovers $a/s$. Thus contraction reflects inclusion of localized ideals. Extension and contraction give inverse order maps on primes of $A$ and primes of $R$ disjoint from $S$. Clearing a localization denominator proves that extension of a prime disjoint from $S$ contracts to itself. Every prime below a prime disjoint from $S$ is disjoint from $S$ as well. Restricting the order isomorphism to the primes below a given prime preserves height. It also transports minimality over an extended ideal, since each smaller competing prime on the original side lies below the contraction and hence survives localization. In particular, localization at $p$ preserves $\operatorname{ht}p$ and sends a prime minimal over $I$ to the maximal ideal minimal over $IR_p$. The quotient and localization of a Noetherian ring are Noetherian by pulling ideals back and using finite generators of the pullback. [Localization/Ideal.lean:112–237](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Localization/Ideal.lean#L112-L237) · [MinimalPrime/Localization.lean:180–203](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean#L180-L203) · [Height.lean:383–424](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/Height.lean#L383-L424)
- For $R\to R/I$, the inverse order maps identify quotient primes with the primes containing $I$. More generally, the inverse image of the image of an ideal $J$ under this quotient is $J+I$. Minimality over a generated ideal in the quotient therefore pulls back to minimality over the ideal generated by its lifts together with $I$. [MinimalPrime/Basic.lean:178–187](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean#L178-L187) · [MinimalPrime/Localization.lean:135–172](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean#L135-L172)
- To show $\operatorname{ht}p\le n$, it suffices to show $\operatorname{ht}q<n$ for every prime $q\subsetneq p$. Appending $p$ increases the length of a chain ending at $q$ by one. Conversely, a chain of length at least $n+1$ ending at $p$ already has a predecessor of height at least $n$. In a Noetherian ring, one may restrict the test to primes *covered* by $p$, meaning there is no prime strictly between them and $p$. Every prime strictly below $p$ is below a maximal member of the primes strictly below $p$, by ACC, and height is monotone on primes. A prime has height zero exactly when it is a minimal prime of the ring. [Height.lean:317–336](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/Height.lean#L317-L336)

The height values lie in $\mathbb N\cup\{\infty\}$. In particular the unit ideal has height $\infty$, the infimum of an empty family. Ring dimension is the supremum over prime chains, in $\{\bot\}\cup\mathbb N\cup\{\infty\}$, with the empty spectrum assigned $\bot$ and $\bot+n=\bot$ for finite $n$. We use arithmetic of natural numbers only after finiteness and nonemptiness have been established. [Height.lean:126–149](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/Height.lean#L126-L149) · [KrullDimension/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/KrullDimension/Basic.lean)

##### The principal ideal bound [Lean, read]

**Lemma (Krull).** In a Noetherian commutative ring, if $p$ is minimal over $(a)$, then $\operatorname{ht}p\le1$.

**Proof.** Localize at $p$ using the first order operation above. We can work in a Noetherian local ring $(R,\mathfrak m)$ with $\mathfrak m$ minimal over $I=(a)$. Every prime of $R/I$ contracts to a prime containing $I$ and lying below $\mathfrak m$. Minimality forces that prime to be $\mathfrak m$. Consequently $R/I$ is Artinian.

Here is the dimension-zero input used in Lean. In a commutative Noetherian ring of dimension at most zero, all primes are maximal and minimal. There are finitely many, and their intersection is both the Jacobson radical and the nilradical. The nilradical is finitely generated by nilpotents, so a sufficiently high power vanishes. The Chinese remainder theorem identifies the quotient by this intersection with the finite product of residue fields. Its modules are semisimple, and finitely generated ones have finite length. The layers of the nilpotent radical filtration of the ring are such modules. The filtration therefore gives the descending chain condition. This is the specialization of Mathlib's semiprimary-ring argument. In a nonzero Noetherian local ring, dimension zero, Artinianness and nilpotence of the maximal ideal are equivalent. The unique prime in dimension zero is the nilradical, and a nilpotent maximal ideal is contained in every prime. This last equivalence will be used in $R_q$. [HopkinsLevitzki.lean:104–108,161–191](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/HopkinsLevitzki.lean#L161-L191) · [KrullDimension/Zero.lean:85–109](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/KrullDimension/Zero.lean#L85-L109)

Fix a prime $q\subsetneq\mathfrak m$. Then $a\notin q$ by minimality. Put $\mathfrak n=qR_q$ and contract its powers to ideals $C_j=\{b\in R:b/1\in\mathfrak n^j\}$. The images of $C_j$ form a descending chain in $R/I$, so some consecutive images agree. Pulling back this equality gives $C_j+I=C_{j+1}+I$. For $b\in C_j$, write $b=c+ad$ with $c\in C_{j+1}$. Localizing at $q$ puts $ad/1$ in $\mathfrak n^j$, and $a/1$ is a unit. Thus $d\in C_j$. We have proved $C_j\subseteq C_{j+1}+IC_j$. The inherited [Nakayama lemma](#why-a-regular-local-ring-is-a-domain) applies to $C_j/C_{j+1}$, a finite $R$-module, since $I\subseteq\mathfrak m=\operatorname{Jac}R$. Thus $C_j=C_{j+1}$. By the inclusion-reflecting contraction in the first order operation, $\mathfrak n^j=\mathfrak n^{j+1}$. Apply the same Nakayama lemma to $\mathfrak n^j$ over $R_q$ to conclude $\mathfrak n^j=0$.

It follows that $\dim R_q=0$, so $\operatorname{ht}q=0$. The third order operation gives $\operatorname{ht}\mathfrak m\le1$, as required. The argument uses a unit after localization and finite modules for Nakayama. The generator $a$ may annihilate elements in the original ring. [KrullsHeightTheorem.lean:48–116](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean#L48-L116) · [Nakayama.lean:118–149](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Nakayama.lean#L118-L149)

##### From one generator to a finite set [Lean, read]

**Lemma (Krull).** If $R$ is Noetherian and $p$ is minimal over $(F)$, then $\operatorname{ht}p\le |F|$.

**Proof.** Use strong induction on the cardinality, uniformly over Noetherian commutative rings. For $F=\varnothing$, $p$ is a minimal prime of the ring and has height zero. At a positive stage of bound $n+1$, localize at $p$. Localization sends $F$ to a set with at most $n+1$ elements and preserves the hypotheses and height. As in Lean, we can perform the positive stage in the local case under the same cardinality bound, with $p=\mathfrak m$. If there is no prime strictly below $p$, its height is already zero.

Take a prime $q$ covered by $p$. Some $x\in F$ is outside $q$, by the minimality of $p$ over $(F)$. Set $F'=F\setminus\{x\}$. Every prime containing $q+(x)$ strictly contains $q$, hence equals $p$. Thus $F'\subseteq p=\sqrt{q+(x)}$. For each $s\in F'$ choose an exponent and a decomposition
$$
s^{a_s}=t_s+xb_s,\qquad t_s\in q.
$$
The set $T=\{t_s:s\in F'\}$ has at most $n$ members. It lies in $q$, and $F'\subseteq\sqrt{(T)+(x)}$. The radical step uses the intersection of the primes containing an ideal, and the compression uses one coefficient in $q$ for each $s$. [Operations.lean:932,1480–1490](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/Operations.lean#L1480-L1490)

Pass to $R/(T)$. The images $\bar q\subsetneq\bar p$ are prime. Any prime below $\bar p$ containing $\bar x$ pulls back to a prime containing $(T)+(x)$ and hence its radical, so it contains $F'$ as well as $x$. Minimality over $(F)$ forces the pullback to be $p$. Thus $\bar p$ is minimal over $(\bar x)$. By the principal bound $\operatorname{ht}\bar p\le1$. Appending $\bar p$ to a chain ending at $\bar q$ forces $\operatorname{ht}\bar q=0$. Pulling this minimality back shows that $q$ is minimal over $(T)$. Induction gives $\operatorname{ht}q\le|T|\le n$. The test by covered primes gives $\operatorname{ht}p\le n+1$. [KrullsHeightTheorem.lean:145–244](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean#L145-L244)

Taking a generating set of least cardinality gives the pinned bound in terms of the span rank. In a Noetherian ring this is finite and agrees with $\mu(I)$ (Lean's <code>spanFinrank</code>). Taking the infimum over the minimal primes of a proper $I$ gives $\operatorname{ht}I\le\mu(I)$. In particular every prime of a Noetherian ring has finite height. The bounds over all primes together can still have infinite supremum. [KrullsHeightTheorem.lean:239–284](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean#L239-L284)

##### Finding generators from a prime height [Lean, read]

**Lemma.** Let $R$ be Noetherian and $p$ a prime of height $d$. There is a finite set of $d$ elements of $p$ over whose span $p$ is minimal.

**Proof.** The proof first constructs, for each natural number $r\le\operatorname{ht}I$, an ideal $J\subseteq I$ generated by at most $r$ elements with $\operatorname{ht}J\ge r$. For $r=0$ take $J=(0)$. For the step, assume $r+1\le\operatorname{ht}I$ and take $J$ from the stage $r$. The primes minimal over $J$ that have height $r$ form a finite set by Noetherian minimal-prime finiteness. None contains $I$, by monotonicity of ideal height. Finite [prime avoidance](#why-a-regular-local-ring-is-a-domain) gives $z\in I$ outside all of them. This also permits an empty family, in which case any element of $I$ suffices.

Replace $J$ by $J+(z)$. A minimal prime $Q$ over the new ideal has height at least $r$ since it contains $J$. If its height were $r$, choose a prime $P\subseteq Q$ minimal over $J$. Its height is at least $r$ and a strict inclusion would increase height by at least one. Thus $P=Q$, and $Q$ would be one of the primes avoided by $z$. Every minimal prime over $J+(z)$ therefore has height at least $r+1$, giving the claimed construction. Monotonicity for general ideals here follows by taking a minimal prime of the smaller ideal below each minimal prime of the larger one. [Height.lean:131–137,213–221,444–485](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/Height.lean#L444-L485) · [MinimalPrime/Noetherian.lean:26–44](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean#L26-L44)

Apply the construction with $I=p$ and $r=d$. As $p$ contains $J$ and has height $d\le\operatorname{ht}J$, the same minimal-prime comparison forces $p$ to be minimal over $J$. The generalized bound gives $d\le\mu(J)$, while the construction gives $\mu(J)\le d$. A smallest generating set of $J$ is the desired set. In this proof the ideal has $p$ among its minimal primes. In a local ring with $p$ maximal it has radical $p$, since every prime lies below $p$. [KrullsHeightTheorem.lean:286–327](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean#L286-L327)

##### The two dimension bounds [Lean, read]

**Quotient bound.** Let $R$ be a Noetherian commutative ring and $I$ an ideal contained in $\operatorname{Jac}R$, the intersection of its maximal ideals. Then
$$
\dim R\le \dim(R/I)+\mu(I).
$$
In particular for any finite set $F\subseteq\operatorname{Jac}R$,
$$
\dim R\le\dim(R/(F))+|F|.
$$

**Proof.** First take any prime $p\supseteq I$. In $R/I$, choose a set of $\operatorname{ht}(p/I)$ generators over whose span $p/I$ is minimal, using the last lemma for the Noetherian quotient. Lift each chosen element once to $p$. Distinct elements have distinct lifts. Adjoin a least generating set of $I$ to the lifts. The quotient prime correspondence shows that $p$ is minimal over the ideal generated by this union. Apply the generalized bound and count the union to obtain
$$
\operatorname{ht}p\le \operatorname{ht}(p/I)+\mu(I)\le\dim(R/I)+\mu(I).
$$
The first inequality is a bound on two specified prime heights, with no Jacobson condition needed once $p\supseteq I$. To pass to dimension, the Jacobson hypothesis ensures that every maximal ideal contains $I$. Every prime chain ends at a prime below some maximal ideal, so dimension is the supremum of the heights of maximal ideals, with the empty-supremum convention. This proves the bound for $I$. For $I=(F)$, the generator count satisfies $\mu(I)\le|F|$. In Lean the finite-set version goes through the wrapper with extended set cardinality <code>encard</code>, which agrees with the finite cardinality here. [KrullsHeightTheorem.lean:329–412](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean#L329-L412) · [Height.lean:363–381](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/Height.lean#L363-L381)

**Maximal-ideal bound.** If $(R,\mathfrak m)$ is Noetherian local, then $\dim R\le\mu(\mathfrak m)$.

**Proof.** The unique maximal ideal is the greatest prime, so $\dim R=\operatorname{ht}\mathfrak m$. It is minimal over itself. Apply the generalized bound to a least generating set of $\mathfrak m$. Its size is a natural number, which also proves finiteness of the local dimension. [KrullsHeightTheorem.lean:254–284,490–494](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean#L490-L494) · [Height.lean:288–293](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/Height.lean#L288-L293)

**Range.** The quotient bound works for nonlocal rings and takes values in the extended dimension order. If $R=0$, both dimensions are $\bot$. If $R\ne0$, an ideal in the Jacobson radical is proper, so $R/I$ has a prime and its dimension is nonnegative. The quotient dimension is at most the original dimension by pullback of chains. Thus for $R\ne0$ either both dimensions are finite or both are infinite. In the latter case the quotient inequality reads $\infty\le\infty$, and yields no finite numerical difference. The local statement deals with a genuine maximal ideal and finite dimension.

##### Computing the prime chains

For $A=k[x,y]_{(x,y)}$, the maximal ideal $\mathfrak m=(x,y)A$ has two generators and its height is at most two by the theorem. Put $u=x+y$. The quotient by $(u)$ is $k[y]_{(y)}$ by substitution $x=-y$. Denominators retain their nonzero constant term. The latter ring has exactly $(0)$ and $(y)$ as primes, because each nonzero element is a unit times a power of $y$. Hence the entire interval of primes containing $(u)$ consists of $(u)$ and $\mathfrak m$. The interval below $(u)$ consists of $(0)$ and $(u)$ by the principal bound and the strict inclusion from the zero prime of this domain. The chain $(0)\subsetneq(u)\subsetneq\mathfrak m$ gives heights $0,1,2$. More generally every nonzero prime strictly below $\mathfrak m$ has height one by this same dimension bound and inclusion of $(0)$. Equivalently those primes are generated by irreducibles of $k[x,y]$ vanishing at the origin. Such a prime contains an irreducible factor of a nonzero numerator, and its prime principal ideal must equal the given height-one prime.

The quotient by $(u,y)=\mathfrak m$ is $k$, with a single prime of height zero. Thus the heights of $(0),(u),(u,y)$ as ideals are $0,1,2$ and their quotient dimensions are $2,1,0$. The three choices $F=\varnothing,\{u\},\{u,y\}$ give equality in the quotient bound. The classes of $x,y$ in $\mathfrak m/\mathfrak m^2$ are linearly independent by taking the degree-one part of a numerator divided by the denominator's constant term. The inherited generator–cotangent comparison gives $\mu(\mathfrak m)=2$, so the maximal-ideal bound is equality too. [Regular-local example and cotangent comparison](#why-a-regular-local-ring-is-a-domain)

In the Noetherian local ring $B=k[x,y]_{(x,y)}/(xy)$ write $x,y$ for their images and $\mathfrak n=(x,y)$. Each is nonzero, as seen in the quotient by the other, and $xy=0$. Every prime contains $x$ or $y$. The two quotients by these elements are $k[y]_{(y)}$ and $k[x]_{(x)}$, each with precisely two primes. Consequently the complete set of primes is $(x),(y),\mathfrak n$, and the two maximal chains are
$$
(x)\subsetneq\mathfrak n,\qquad (y)\subsetneq\mathfrak n .
$$
The branch primes have height zero, and $\operatorname{ht}\mathfrak n=\dim B=1$. The relation has degree two, so the classes of $x,y$ remain independent in $\mathfrak n/\mathfrak n^2$ and $\mu(\mathfrak n)=2$. Thus the maximal-ideal bound can be strict. For $F=\{x\}$ the unique prime minimal over $(x)$ has height zero, and the quotient has dimension one. For $F=\{x+y\}$, substitution identifies $B/(x+y)$ with $k[y]_{(y)}/(y^2)$. The sole prime of this quotient is $(y)/(y^2)$, since every prime contains the nilpotent $y$. It has height zero and pulls back to $\mathfrak n$, of height one. The principal and quotient bounds are equalities for this choice. Indeed, the map to the product of the two localized axes is injective because $(x)\cap(y)=(xy)$ in $A$. On the axes $x+y$ acts by the nonzero parameter of each domain, so it is a nonzerodivisor in $B$. For $F=\varnothing$ the ideal height is zero and the quotient dimension is one. For $F=\{x,y\}$ the ideal height is one and the quotient is $k$. This ring also exhibits the need for the nonzerodivisor hypothesis in the reverse comparison: $\dim B/(x)+1=2>1=\dim B$.

##### Hypotheses and the exact consumers

**Noetherianity.** Take the valuation ring $V$ in $k((u))((t))$ associated to the lexicographic value $(\operatorname{ord}_t f,\operatorname{ord}_u a)$, where $a$ is the first nonzero $t$-coefficient of $f$. Include zero in $V$ and take the nonnegative values. Multiplication adds values, addition has value at least the smaller summand value, and each nonzero field element or its inverse lies in $V$. In $V$ divisibility of nonzero elements is comparison of values. Its maximal ideal $\mathfrak m_V$ consists of elements of positive value and is $(u)$, since $(0,1)$ is the smallest positive value. The ideal $P$ of elements with positive first coordinate, together with zero, is prime, since first coordinates in $V$ are nonnegative and add under multiplication. The primes are exactly $0,P,\mathfrak m_V$. A prime containing a nonzero element of value $(0,b)$ with $b>0$ contains $u$ by the power test for primes. A prime containing an element of positive first coordinate contains all of $P$, since any element of $P$ has a power divisible by the given element. The chain is strict, witnessed by $t\in P$ and $u\in\mathfrak m_V\setminus P$. Hence $\operatorname{ht}(u)=\dim V=2$, $\mu(\mathfrak m_V)=1$ and $\dim V/(u)=0$. This violates the principal bound and both dimension bounds, even though $V$ is a local domain with a principal maximal ideal and $u$ lies in its Jacobson radical. The ideals $(t/u^j)$ for $j=0,1,2,\ldots$ form a strictly ascending chain by the values $(1,-j)$.

**Jacobson radical and locality.** In the nonlocal Noetherian ring $R=k[x,y]\times k$, let $F=\{(1,0)\}$. This element is a nonunit and lies outside the maximal ideal $(x,y)\times k$. Killing it leaves the field $k$, whereas the primes $(0)\times k$, $(x)\times k$, $(x,y)\times k$ have two strict inclusions. The quotient bound with right side one fails. The same example shows why a bound on the generators of one maximal ideal does not give the global maximal-ideal bound without locality. The maximal ideal $k[x,y]\times0$ is principal and the chain on the other factor has length two. In a local ring any proper generated ideal lies in the Jacobson radical. Dropping that containment permits a unit generator, as in $F=\{1\}$ over a field, where the right side is $\bot+1=\bot$.

**Minimality.** Being prime and containing $(F)$ alone cannot suffice. The prime $(x,y)A$ contains $(x+y)$ and has height two. The weaker bound on the height of a *proper generated ideal* still follows by taking the infimum over its minimal primes. The unit ideal is excluded from that version.

**A2 parameter quotient.** In <code>RingKrullDimQuotientSpanSingletonAddOne.lean:143–180</code>, $R$ is regular local, $u\in\mathfrak m\setminus\mathfrak m^2$, and $S=R/(u)$ is local as assumed there. It is also Noetherian. At lines 160–170, locality puts $\{u\}$ in the Jacobson radical and the finite-set bound gives $\dim R\le\dim S+1$. At line 171, the maximal-ideal bound gives $\dim S\le\mu(\mathfrak m_S)$. With the inherited cotangent replacement estimate at line 159 and regularity of $R$, the chain is
$$
\dim R\le\dim S+1\le\mu(\mathfrak m_S)+1\le\mu(\mathfrak m)=\dim R .
$$
The finite-number step at lines 172–180 yields the two equalities, regularity in the generator form for $S$ and $\dim S+1=\dim R$. This is the input to the already established [domain induction](#why-a-regular-local-ring-is-a-domain).

**Jacobian cut.** In <code>JacChartB.lean:215–216</code>, the ring is the Noetherian local quotient $R_J$. The maximal-ideal bound followed by the generator–cotangent comparison gives $\dim R_J\le\dim_{k_J}(\mathfrak m_J/\mathfrak m_J^2)$, where $k_J$ is its residue field. Lines 217–226 combine it with the inherited cotangent bound by $e$ and the surjection onto the given local ring $R_K$ of dimension $e$. The regularity constructor also uses the maximal-ideal bound for its converse inequality. Line 227 consumes the domain theorem. Lines 237–244 then use the nonzerodivisor successor bound in $R_J$ and the quotient maps to $R_K$, as in the [cut proof](#the-local-jacobian-cut). The successor bound enters only at that later step.

**Provenance and reading scope.** The principal and generalized bounds are Krull's classical theorems. Stacks derives the principal and generalized bounds using the dimension and length-growth characterization of a Noetherian local ring. The source reading here follows the pinned Mathlib argument with zero divisors allowed from the start, its covered-prime induction, and its construction of height-sized generators for individual quotient primes. The reading covers these bodies and the two dimension consumers. The inherited domain induction and Jacobian proof retain their own reviews. The algebraic examples are textbook calculations. Kernel replay of the new reading window and of Main remains [Open]. [Krull, principal proof, pp. 9–10](https://digi.hadw-bw.de/view/sbhadwmnkl_1928_7/0009) · [Krull, generalized proof, pp. 11–12](https://digi.hadw-bw.de/view/sbhadwmnkl_1928_7/0011) · [Stacks, principal bound](https://stacks.math.columbia.edu/tag/00KV) · [Stacks, generalized bound](https://stacks.math.columbia.edu/tag/0BBZ) · [Stacks §10.60](https://stacks.math.columbia.edu/tag/00KD) · [Pinned declaration map](../sources/SOURCES.md#chapter-12-krull-height-and-dimension)

#### Why the transversal zeros are finite: Nakayama and minimal primes

The [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre) used one more fact about the translated forms, in step 5 of its Lemma 2: in the affine open $D(h)$, the transversal common zeros of $F_1/h,\ldots,F_d/h$ form a finite set $T$. Step 6 then chooses a single denominator $f_0$ that vanishes at no point of $S\cup T$, and this is possible only because $S\cup T$ is finite. The fact is the statement <code>finite_complexPoints_transversal_zeros</code>, whose producer is <code>GlobalTheory.TransvZeros.finite_transv_zeros</code>. This subsection reads that producer and the lemmas of its file, together with the two Mathlib proofs that carry the weight: Nakayama's lemma in the form "a finitely generated idempotent ideal is generated by an idempotent", and the finiteness of the minimal primes over an ideal of a Noetherian ring. We say which step pays for quasi-compactness, for closedness, for the residue field and for zero-dimensionality, and why the argument has to be algebraic. The Sard step, the jet forms, the holomorphic implicit functions and the cotangent basis keep the readings recorded in the previous subsections.

**Motivation.** After the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets), every common zero $z$ of the $F_j/h$ in $D(h)$ is transversal: the classes of $F_1/h,\ldots,F_d/h$ span $\mathfrak m_z/\mathfrak m_z^2$. A transversal zero is an isolated point of the zero set (this follows from Lemma 2 below), and it is tempting to conclude that there are only finitely many of them. That step, "discrete, hence finite", is wrong. The entire function $\sin z$ has a simple zero at every $n\pi$. These zeros are isolated, they are transversal in the sense used here (see the counterexamples below), and there are infinitely many. A discrete set is finite when it is closed in a compact space. The complex points of an affine open such as $\mathbb A^1$ do not form a compact space, and the transversal zeros need not be all the zeros.

The archive argues algebraically, in four moves. Put $A=\Gamma(X,U)$ and $I=(\varphi_1,\ldots,\varphi_k)$, so that the common zeros of the $\varphi_j$ are the complex points of the closed subscheme $Z=\operatorname{Spec}(A/I)$ of the affine $U$.

1. A complex point $z$ gives a maximal ideal $\mathfrak m_z$ of $A$ with residue field $\mathbb C$, and $z$ is a common zero exactly when $I\subseteq\mathfrak m_z$.
2. Transversality, $\mathfrak m_z\subseteq I+\mathfrak m_z^2$, says that the image of $\mathfrak m_z$ in $A/I$ is an idempotent ideal. By Nakayama's lemma it is generated by an idempotent, and then no prime lies strictly between $I$ and $\mathfrak m_z$. So $\mathfrak m_z$ is a minimal prime over $I$, and the point $z$ is an irreducible component of $Z$.
3. A Noetherian ring has only finitely many minimal primes over an ideal, and $A$ is Noetherian because $X$ is locally of finite type over $\mathbb C$.
4. A complex point of the affine $U$ is determined by its maximal ideal.

So $z\mapsto\mathfrak m_z$ injects the transversal zeros into a finite set.

**Example (simple roots on the affine line) [Expository].** Take $X=U=\mathbb A^1_{\mathbb C}$, so that $A=\mathbb C[t]$, and one function, $k=1$, $\varphi=f$ a nonzero polynomial. The complex points are the $z\in\mathbb C$, with $\mathfrak m_z=(t-z)$.

- *Transversal zeros are simple roots.* Let $f(z)=0$ and write $f=(t-z)g$. Then $f-g(z)(t-z)=(t-z)\bigl(g-g(z)\bigr)$ lies in $\mathfrak m_z^2$, and $g(z)=f'(z)$. If $f'(z)\ne0$, then
  $$
  t-z=\frac{f}{g(z)}-\frac{(t-z)\bigl(g-g(z)\bigr)}{g(z)}\in(f)+\mathfrak m_z^2 .
  $$
  If $f'(z)=0$, then $f\in\mathfrak m_z^2$, so $(f)+\mathfrak m_z^2=\mathfrak m_z^2$, which does not contain $t-z$. So the transversal zeros of $f$ are exactly its simple roots.
- *Three simple roots.* Take $f=t^3-3t=t(t^2-3)$, the translate $t^3-3t+1+c$ of the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets) at the harmless parameter $c=-1$. Its roots $0,\pm\sqrt3$ are simple, since $f'=3t^2-3$ takes the values $-3,6,6$ there, so $T=\{0,\sqrt3,-\sqrt3\}$. At $z=0$ the certificate is $t=-\tfrac13f+\tfrac13t^3$, with $t^3\in\mathfrak m_0^2$. In $A/I=\mathbb C[t]/(t^3-3t)$ the image of $\mathfrak m_0$ is generated by the idempotent $e_0=t^2/3$. Indeed $t^3\equiv3t$, so $e_0^2=t^4/9\equiv t^2/3=e_0$ and $t\,e_0=t^3/3\equiv t$, whence $(t)=(e_0)$. The element $r=1-e_0$ is the one Nakayama's lemma produces: $r-1\in(t)$ and $r\,t\equiv0$.
- *A double root.* Take $f=t^3-3t+2=(t-1)^2(t+2)$, the translate at the bad parameter $c=1$. The root $-2$ is simple, with certificate
  $$
  t+2=\tfrac19f-\tfrac19(t-4)(t+2)^2 .
  $$
  In $A/I$ the image of $\mathfrak m_{-2}$ is generated by the idempotent $e=(t+2)(4-t)/9$, which is $0$ modulo $t+2$ and $1$ modulo $(t-1)^2$, because $e-1=-(t-1)^2/9$. The root $1$ is a zero but not a transversal one, since $f\in\mathfrak m_1^2$. So $T=\{-2\}$.
- *Minimal primes.* The minimal primes over $(f)$ are the ideals $(t-r)$, one for each distinct root $r$, so there are at most $\deg f$ of them. For $f=(t-1)^2(t+2)$ both $(t-1)$ and $(t+2)$ are minimal, but only $(t+2)$ comes from a transversal zero. So the map $z\mapsto\mathfrak m_z$ of the proof is injective but need not be onto the minimal primes, and the bound by the number of minimal primes can be strict. The bound uses no degree.

**Example (transversal intersection points in the plane) [Expository].** Take $X=U=\mathbb A^2_{\mathbb C}$, so that $A=\mathbb C[x,y]$, and $k=2$ with the cubic and the line of the earlier examples,
$$
\varphi_1=\Phi=y^2-x^3+x,\qquad \varphi_2=L_c=y+cx .
$$

- *The zero scheme.* Since $\Phi-\Phi(x,-cx)=(y+cx)(y-cx)$, modulo $L_c$ we may replace $y$ by $-cx$, and
  $$
  A/I\cong\mathbb C[x]/\bigl(x^3-c^2x^2-x\bigr)=\mathbb C[x]/\bigl(x(x^2-c^2x-1)\bigr).
  $$
  The common zeros are $(0,0)$ and the points $(a,-ca)$ with $a^2-c^2a-1=0$.
- *Transversality is the Jacobian criterion.* At a common zero $z=(a,b)$ the classes of $x-a$ and $y-b$ form a basis of $\mathfrak m_z/\mathfrak m_z^2$, and Taylor's formula gives $\varphi\equiv\partial_x\varphi(z)\,(x-a)+\partial_y\varphi(z)\,(y-b)$ modulo $\mathfrak m_z^2$. So $z$ is transversal if and only if the Jacobian determinant
  $$
  \det\begin{pmatrix}1-3a^2&2b\\ c&1\end{pmatrix}=1-3a^2-2bc
  $$
  is nonzero. This is Lemma 4 of the Sard step, written in the coordinates of the plane.
- *Three transversal points, $c=0$.* The common zeros are $(0,0)$, $(1,0)$ and $(-1,0)$, with determinants $1$, $-2$ and $-2$. The certificates are explicit. At $(0,0)$ they are $y=L_0$ and $x=\Phi-y^2+x^3$. At $(1,0)$, from $x(x+1)=2+3(x-1)+(x-1)^2$,
  $$
  x-1=\tfrac12\bigl(y^2-\Phi\bigr)-\tfrac32(x-1)^2-\tfrac12(x-1)^3 ,
  $$
  and symmetrically $x+1=\tfrac12(y^2-\Phi)+\tfrac32(x+1)^2-\tfrac12(x+1)^3$ at $(-1,0)$; in both cases $y=L_0$. The ring $A/I\cong\mathbb C[x]/(x^3-x)$ is a product of three copies of $\mathbb C$. The image of $\mathfrak m_{(1,0)}=(x-1,y)$ is $(x-1)$, generated by the idempotent $1-\tfrac12x(x+1)=-\tfrac12(x-1)(x+2)$. The minimal primes over $I$ are the three maximal ideals, and $|T|=3$.
- *A tangent point, $c=1+i$.* Now $x^2-c^2x-1=x^2-2ix-1=(x-i)^2$, so
  $$
  A/I\cong\mathbb C[x]/\bigl(x(x-i)^2\bigr)\cong\mathbb C\times\mathbb C[\varepsilon]/(\varepsilon^2).
  $$
  The common zeros are $P_0=(0,0)$ and $Q=(i,1-i)$. At $Q$ the determinant is $1-3i^2-2(1-i)(1+i)=4-4=0$, so $Q$ is a zero but not a transversal one; its maximal ideal is nevertheless a minimal prime over $I$. At $P_0$ the determinant is $1$, and the certificates are $x=\Phi-y^2+x^3$ and $y=L_c-c\,(\Phi-y^2+x^3)$. The image of $\mathfrak m_{P_0}$ in $A/I$ is generated by the idempotent $e=x^2-2ix$, because $e(e-1)=x(x-2i)(x-i)^2$ lies in $\bigl(x(x-i)^2\bigr)$ and $x\,e\equiv x$. So $T=\{P_0\}$, against two minimal primes.
- *The same count in the consumer.* The consumer applies the theorem on the cubic $E$ itself, with $U=D(h)=E\setminus\{P_0,O\}$ and $\varphi=y/x+c$. For $c^4\ne-4$ the common zeros are the points of $E$ over the two roots of $x^2-c^2x-1$, neither of which is $0$, and both are transversal by the Sard step. So $T$ has two points, and the denominator $f_0=z$ of the earlier example avoids $S\cup T$.

All assertions in the two examples and in the counterexamples below are exact identities over $\mathbb Q$, $\mathbb Q(i)$ or $\mathbb Q(\sqrt3)$, with Gröbner-basis membership tests for the transversality claims. They are checked by <code>check_transv_zeros.py</code> in the run directory (162 assertions).

**Definitions.**

- *Complex points and their maximal ideals.* As in the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets), a complex point is a $\mathbb C$-morphism $z:\operatorname{Spec}\mathbb C\to X$ (<code>CxPts p (RingHom.id ℂ)</code>), and $U(\mathbb C)$ is the set of those landing in $U$ (<code>ptsIn</code>). Evaluation $\mathrm{ev}_z:\Gamma(X,U)\to\mathbb C$ (<code>evHom</code>) is the ring map that $z$ induces on sections, followed by the isomorphism $\Gamma(\operatorname{Spec}\mathbb C,\mathcal O)\cong\mathbb C$. A constant $c\in\mathbb C$, viewed as a section through the structure map <code>algX</code>, takes the value $c$ at every complex point (<code>evHom_algX</code>). Put $\mathfrak m_z=\ker\mathrm{ev}_z$.
- *Transversal common zero.* For any $k\ge0$ and $\varphi_1,\ldots,\varphi_k\in\Gamma(X,U)$, a point $z\in U(\mathbb C)$ is a transversal common zero if every $\varphi_j(z)=0$ and $\mathfrak m_z\subseteq(\varphi_1,\ldots,\varphi_k)+\mathfrak m_z^2$. The number $k$ is not tied to a dimension; the consumer uses $k=d$.
- *The zero scheme.* With $A=\Gamma(X,U)$ and $I=(\varphi_1,\ldots,\varphi_k)$, the zero scheme is $Z=\operatorname{Spec}(A/I)$, a closed subscheme of $U\cong\operatorname{Spec}A$. A complex point $z$ of $U$ is a common zero if and only if $I\subseteq\mathfrak m_z$, that is, if and only if it lies on $Z$.
- *Minimal primes.* A prime $\mathfrak p\supseteq I$ is minimal over $I$ if no prime $\mathfrak q$ satisfies $I\subseteq\mathfrak q\subsetneq\mathfrak p$ (<code>Ideal.minimalPrimes</code>). The minimal primes over $I$ are the generic points of the irreducible components of $Z$.
- *Locally of finite type.* In the pinned Mathlib, $p:X\to\operatorname{Spec}\mathbb C$ is locally of finite type (<code>LocallyOfFiniteType</code>) if for every affine open $V$ of the base and every affine open $U$ of $X$ with $U\subseteq p^{-1}V$ the ring map $\Gamma(V,\mathcal O)\to\Gamma(X,U)$ is of finite type. Classically this is equivalent to the same condition on a single affine open cover ([Stacks Project, Lemma 29.15.2](https://stacks.math.columbia.edu/tag/01T2)).

**Theorem (finitely many transversal zeros) [Lean, read].** Let $X$ be a scheme and $p:X\to\operatorname{Spec}\mathbb C$ a morphism locally of finite type. Let $U\subseteq X$ be an affine open and let $\varphi_1,\ldots,\varphi_k\in\Gamma(X,U)$, with $k\ge0$ arbitrary. Then the set of transversal common zeros
$$
T=\bigl\{z\in U(\mathbb C):\ \varphi_j(z)=0\ \text{for all }j,\ \ \mathfrak m_z\subseteq(\varphi_1,\ldots,\varphi_k)+\mathfrak m_z^2\bigr\}
$$
is finite. More precisely, $z\mapsto\mathfrak m_z$ maps $T$ injectively into the finite set of minimal primes over $(\varphi_1,\ldots,\varphi_k)$.

This is <code>GlobalTheory.TransvZeros.finite_transv_zeros</code>; the exported statement <code>finite_complexPoints_transversal_zeros</code> is the same sentence and delegates to it. The sentence asserts only finiteness; the "more precisely" is what the proof shows. Smoothness, integrality, separatedness and projectivity of $X$ are not assumed. We prove four lemmas. Lemmas 2 and 4 are proved in the archive's file; Lemmas 1 and 3 are Mathlib theorems whose proofs we also read.

**Lemma 1 (Nakayama: a finitely generated idempotent ideal is generated by an idempotent) [Lean, read].** Let $R$ be a ring and $J\subseteq R$ a finitely generated ideal with $J^2=J$. Then $J=(e)$ for some $e\in J$ with $e^2=e$.

*Proof.* This is Mathlib's <code>Ideal.isIdempotentElem_iff_of_fg</code>. It rests on Nakayama's lemma in the following form (<code>Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul</code>): if $N$ is a finitely generated $R$-module and $N\subseteq JN$, then some $r\in R$ with $r-1\in J$ satisfies $rN=0$.

Mathlib proves this form by induction over a finite generating set $s$ of $N$. The induction carries an element $r$ with $r-1\in J$ and $rN\subseteq J\operatorname{span}(s)$. At the start $r=1$ works, because $N\subseteq JN$. To remove a generator $i$, write $s=\{i\}\cup s'$. Since $i\in N$, we have $ri=ci+w$ with $c\in J$ and $w\in J\operatorname{span}(s')$. Put $c'=r-c$. Then $c'-1\in J$ and $c'i=w\in J\operatorname{span}(s')$. The new element $r'=c'r$ satisfies $r'-1=c'(r-1)+(c'-1)\in J$. For $n\in N$ write $rn=di+w'$ with $d\in J$ and $w'\in J\operatorname{span}(s')$; then $r'n=d\,(c'i)+c'w'\in J\operatorname{span}(s')$. When $s$ is empty, $rN\subseteq J\cdot0=0$.

Apply this to $N=J$, which is finitely generated and satisfies $J\subseteq J\cdot J$. We get $r$ with $r-1\in J$ and $rJ=0$. Put $e=1-r\in J$. For $j\in J$ we have $ej=j-rj=j$. In particular $e^2=e$, and $J=(e)$, since every $j=ej$ lies in $(e)$ and $e\in J$. $\square$

This is Lemma 10.21.5 of the Stacks Project ([00EH](https://stacks.math.columbia.edu/tag/00EH)), with the same proof from Nakayama's lemma in the form "$f\in1+I$ and $fM=0$" ([Lemma 10.20.1(1), 00DV](https://stacks.math.columbia.edu/tag/00DV)). Stacks proves that form by the determinant trick, Mathlib by the induction above. The Stacks lemma adds that $V(J)$ is open and closed in $\operatorname{Spec}R$. Finite generation cannot be dropped. In the valuation ring $V=\bigcup_n\mathbb C[[t^{1/n}]]$, whose value group is $\mathbb Q$, every element of the maximal ideal is $t^a$ times a unit for some rational $a>0$, and $t^a=t^{a/2}t^{a/2}$, so $\mathfrak m=\mathfrak m^2$. But $V$ is a domain, its only idempotents are $0$ and $1$, and so $\mathfrak m$ is not generated by an idempotent.

**Lemma 2 (a transversal maximal ideal is a minimal prime) [Lean, read].** Let $A$ be a ring and $I\subseteq\mathfrak m$ ideals, with $\mathfrak m$ maximal and finitely generated. If $\mathfrak m\subseteq I+\mathfrak m^2$, then $\mathfrak m$ is a minimal prime over $I$.

*Proof.* This is <code>mem_minimalPrimes_of_le_sup_sq</code>. Let $\pi:A\to A/I$ be the quotient map and $\bar{\mathfrak m}=\pi(\mathfrak m)$. Because $\pi$ is onto with kernel $I\subseteq\mathfrak m$, we have $\pi^{-1}(\bar{\mathfrak m})=\mathfrak m+I=\mathfrak m$, and likewise $\pi^{-1}(\pi(P))=P$ for every ideal $P\supseteq I$ (Mathlib's <code>Ideal.comap_map_of_surjective'</code>). Applying $\pi$ to $\mathfrak m\subseteq I+\mathfrak m^2$ gives $\bar{\mathfrak m}\subseteq\bar{\mathfrak m}^2$, and $\bar{\mathfrak m}^2\subseteq\bar{\mathfrak m}$ always, so $\bar{\mathfrak m}$ is idempotent. It is finitely generated, being the image of $\mathfrak m$. Lemma 1 gives $e\in\bar{\mathfrak m}$ with $e^2=e$ and $\bar{\mathfrak m}=(e)$.

Let $P$ be a prime with $I\subseteq P\subseteq\mathfrak m$; we show $\mathfrak m\subseteq P$. The image $\bar P=\pi(P)$ is a prime of $A/I$, since $\ker\pi=I\subseteq P$ (<code>Ideal.map_isPrime_of_surjective</code>). If $1-e$ were in $\bar P\subseteq\bar{\mathfrak m}$, then $1=(1-e)+e\in\bar{\mathfrak m}$, so $1\in\pi^{-1}(\bar{\mathfrak m})=\mathfrak m$, which is impossible. But $e(1-e)=e-e^2=0$ lies in $\bar P$, and $\bar P$ is prime, so $e\in\bar P$. Hence $\bar{\mathfrak m}=(e)\subseteq\bar P$, and $\mathfrak m=\pi^{-1}(\bar{\mathfrak m})\subseteq\pi^{-1}(\bar P)=P$. So $P=\mathfrak m$, and $\mathfrak m$ is minimal over $I$. $\square$

Of the maximality of $\mathfrak m$ the proof uses only that $\mathfrak m$ is prime and proper. Finite generation is essential: in the valuation ring $V$ above, $I=0$ and $\mathfrak m$ satisfy $\mathfrak m\subseteq0+\mathfrak m^2$, yet the prime $0$ lies strictly below $\mathfrak m$.

The conclusion has a local reading. The local ring of the zero scheme at $z$ is $\mathcal O_{Z,z}=(A/I)_{\mathfrak m}$. Its maximal ideal $M$ is finitely generated and satisfies $M=M^2$, so $M=0$ by the local form of Nakayama's lemma ([Nakayama 1951, p. 140, statement II](https://doi.org/10.1017/S0027763000012265)), and $\mathcal O_{Z,z}$ is the field $\mathbb C$. Conversely, if $\mathcal O_{Z,z}$ is a field, then $\mathfrak m\subseteq I+\mathfrak m^2$. So the transversal zeros are exactly the points at which $Z$ is a reduced point. The archive does not localize. It works in $A/I$ with the idempotent $e$, and the identity $e(1-e)=0$ forces every prime between $I$ and $\mathfrak m$ to contain $e$.

**Lemma 3 (finitely many minimal primes) [Lean, read].** If $A$ is a Noetherian ring and $I\subseteq A$ an ideal, then only finitely many primes are minimal over $I$.

*Proof.* This is Mathlib's <code>Ideal.finite_minimalPrimes_of_isNoetherianRing</code>, proved by Noetherian induction. Suppose some ideal has infinitely many minimal primes. In a Noetherian ring every nonempty set of ideals has a maximal element (<code>set_has_maximal_iff_noetherian</code>), so we may choose $I$ maximal among such ideals. Then $I$ is not prime, because a prime is its own only minimal prime, and $I\ne A$, because no prime contains $A$. Hence there are $x,y\notin I$ with $xy\in I$. The ideals $I+(x)$ and $I+(y)$ strictly contain $I$, so each has only finitely many minimal primes. Let $\mathfrak p$ be minimal over $I$. Since $xy\in\mathfrak p$, we may assume $x\in\mathfrak p$. Then $\mathfrak p\supseteq I+(x)$, and $\mathfrak p$ is minimal over $I+(x)$, because a prime between $I+(x)$ and $\mathfrak p$ lies between $I$ and $\mathfrak p$. So every minimal prime over $I$ is minimal over $I+(x)$ or over $I+(y)$, and there are only finitely many of them, a contradiction. $\square$

The Stacks Project proves the case $I=0$ through topology ([Lemma 10.31.6, 00FR](https://stacks.math.columbia.edu/tag/00FR)). There $\operatorname{Spec}A$ is a Noetherian space ([Lemma 10.31.5, 00FQ](https://stacks.math.columbia.edu/tag/00FQ)), a Noetherian space has finitely many irreducible components ([Lemma 5.9.2, 0052](https://stacks.math.columbia.edu/tag/0052)), and the components correspond to the minimal primes. A general $I$ is the case of the ring $A/I$. Mathlib's proof never forms the spectrum.

**Lemma 4 (a complex point of an affine open is determined by its maximal ideal) [Lean, read].** Let $U\subseteq X$ be affine and let $y,z\in U(\mathbb C)$ satisfy $\mathfrak m_y=\mathfrak m_z$. Then $y=z$.

*Proof.* This is <code>eq_of_ker_eq</code>, which reduces to <code>eq_of_evHom_eq</code>. First the values. Let $f\in\Gamma(X,U)$ and $c=\mathrm{ev}_y(f)$. The constant $c$ takes the value $c$ at $y$ (<code>evHom_algX</code>), so $f-c\in\mathfrak m_y=\mathfrak m_z$, and therefore $\mathrm{ev}_z(f)=c$. Thus $\mathrm{ev}_y=\mathrm{ev}_z$.

Then the points. The evaluation $\mathrm{ev}_y$ is the ring map $y^\sharp:\Gamma(X,U)\to\Gamma(\operatorname{Spec}\mathbb C,\mathcal O)$ induced by $y$, followed by the isomorphism $\Gamma(\operatorname{Spec}\mathbb C,\mathcal O)\cong\mathbb C$. Cancelling that isomorphism gives $y^\sharp=z^\sharp$. Because $U$ is affine, $y$ is, up to the canonical isomorphism $\operatorname{Spec}\mathbb C\cong\operatorname{Spec}\Gamma(\operatorname{Spec}\mathbb C,\mathcal O)$, the composite of $\operatorname{Spec}(y^\sharp)$ with the canonical morphism $\operatorname{Spec}\Gamma(X,U)\to X$ onto $U$ (Mathlib's <code>IsAffineOpen.SpecMap_appLE_fromSpec</code> and <code>IsAffineOpen.fromSpec_top</code>). The same holds for $z$, so $y=z$. $\square$

The first half is where the residue field enters. It needs every element of $\Gamma(X,U)$ to be congruent modulo $\mathfrak m_y$ to a constant, that is, $\Gamma(X,U)/\mathfrak m_y=\mathbb C$ through the structure map. For points with values in a larger field this fails. On $\mathbb A^1_{\mathbb R}$ the two $\mathbb C$-valued points $t\mapsto i$ and $t\mapsto-i$ are different, but they have the same kernel $(t^2+1)$. The archive's statement concerns <code>CxPts p (RingHom.id ℂ)</code> only.

*Proof of the theorem.* We follow <code>finite_transv_zeros</code>, lines 74–102.

- *Finite type and the Noetherian property (lines 79–86).* The base $\operatorname{Spec}\mathbb C$ and the open $U$ are affine, so the ring map $\Gamma(\operatorname{Spec}\mathbb C,\mathcal O)\to\Gamma(X,U)$ is of finite type (<code>LocallyOfFiniteType.finiteType_of_affine_subset</code>, an alias of the defining field of <code>LocallyOfFiniteType</code>). The isomorphism $\mathbb C\cong\Gamma(\operatorname{Spec}\mathbb C,\mathcal O)$ is onto, hence of finite type (<code>RingHom.FiniteType.of_surjective</code>), and the composite (<code>RingHom.FiniteType.comp</code>) is the structure map <code>algX</code> from $\mathbb C$ to $\Gamma(X,U)$. So $A=\Gamma(X,U)$ is a finitely generated $\mathbb C$-algebra, and by Hilbert's basis theorem it is Noetherian (<code>Algebra.FiniteType.isNoetherianRing</code>; [Stacks Project, Lemmas 10.31.1](https://stacks.math.columbia.edu/tag/00FN) and [10.31.3](https://stacks.math.columbia.edu/tag/00FO)).
- *The map (lines 88–89).* Put $F(z)=\mathfrak m_z$ for $z\in U(\mathbb C)$. The archive sets $F(z)=0$ at the other complex points; those values are never used.
- *Transversal zeros go to minimal primes (lines 92–99).* Let $z\in T$. The evaluation $\mathrm{ev}_z$ is onto $\mathbb C$, because the constant $c$ has value $c$, so $\mathfrak m_z$ is a maximal ideal with residue field $\mathbb C$ (<code>RingHom.ker_isMaximal_of_surjective</code>). It is finitely generated, because $A$ is Noetherian. It contains $I$, because each generator $\varphi_j$ vanishes at $z$ (<code>Ideal.span_le</code>). And $\mathfrak m_z\subseteq I+\mathfrak m_z^2$ is the transversality of $z$. By Lemma 2, $\mathfrak m_z$ is a minimal prime over $I$.
- *Finiteness (lines 90–91).* By Lemma 3 the minimal primes over $I$ form a finite set, and $F(T)$ lies in it.
- *Injectivity (lines 100–102).* By Lemma 4, $F$ is injective on $U(\mathbb C)$.
- *Conclusion.* A set on which a map is injective and whose image is finite is itself finite (Mathlib's <code>Set.Finite.of_finite_image</code>, line 90). $\square$

**The actual consumer [Lean, read].** The statement is used once, at line 161 of <code>exists_transversal_forms_first_separate</code>, the proof of Lemma 2 of the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre).

1. *The instance and the affine open.* The instance <code>LocallyOfFiniteType p</code> needed by the call is inferred from the smoothness of $p$ (line 98 records <code>Smooth p</code>). The open $U=D(h)$ is affine by line 100, the fact the Sard step also used.
2. *The call (line 161).* The theorem is applied with $k=d$ and $\varphi_j=F_j/h$. Its output <code>hfin</code> is the finiteness of the set $T$ of transversal common zeros of the $F_j/h$ in $D(h)$.
3. *The denominator (line 162).* <code>hfin.toFinset</code> turns $T$ into a finite set, and <code>EtProj.exists_form_genericPoint_cxPts</code> gives a form $f_0$ of degree $n$ that vanishes neither at the generic point nor at any point of $S\cup T$. The [denominator and open-cover proof](#choosing-the-denominator-and-detecting-the-open-cover) makes this finite avoidance at the prescribed degree explicit.
4. *Where the finiteness is spent (lines 185–188).* For property (i) of Lemma 2, let $z$ be a complex point at which $f_0$ and all $F_j$ vanish. If $z\in D(h)$, the Sard choice of $c$ makes $z$ a transversal zero (<code>htrh</code>), so $z\in T$; otherwise $z\in S$ by the base-locus clause of the jet forms. Either way $f_0(z)\ne0$, a contradiction.

So the consumer combines two facts, neither of which suffices alone. The Sard step makes every common zero in $D(h)$ transversal, and the present theorem makes the transversal ones finitely many. Together they make the whole common zero locus in $D(h)$ finite.

**Example (counterexamples when a hypothesis is dropped) [Expository].**

1. *Without transversality.* In $\mathbb A^2$ take $k=2$ and $\varphi=(x(x-1),\,xy)$. Then $I=(x)\cap(x-1,y)$, and the common zeros are the line $x=0$ together with the point $(1,0)$. The zero $(1,0)$ is transversal, with certificates $x-1=x(x-1)-(x-1)^2$ and $y=xy-(x-1)y$. At a point $(0,b)$ of the line, $x(x-1)\equiv-x$ and $xy\equiv bx$ modulo $\mathfrak m^2$, so $(\varphi)+\mathfrak m^2=(x)+\mathfrak m^2$, which does not contain $y-b$. So the common zeros are infinite in number while $T=\{(1,0)\}$. The minimal primes over $I$ are $(x)$ and $(x-1,y)$. The first is not maximal: it is the generic point of the line, which carries infinitely many complex points, none of them transversal.
2. *Without finite type: entire functions.* Let $\mathcal O(\mathbb C)$ be the ring of entire functions, $X=U=\operatorname{Spec}\mathcal O(\mathbb C)$, $k=1$ and $\varphi=\sin z$. For each $n\in\mathbb Z$, evaluation at $n\pi$ is a $\mathbb C$-algebra map $\mathcal O(\mathbb C)\to\mathbb C$, hence a complex point, and its kernel is $\mathfrak m_{n\pi}=(z-n\pi)$ by the removable singularity theorem. From $(-1)^n\sin z=(z-n\pi)-(z-n\pi)^3/6+\cdots$ we get $z-n\pi\in(\sin z)+\mathfrak m_{n\pi}^2$. So every $n\pi$ is a transversal zero: there are infinitely many, and they are isolated and discrete in $\mathbb C$. The hypothesis that fails is finite type. The ideals $I_N=\{f:f(n\pi)=0\text{ for all }n\ge N\}$ form a strictly increasing chain, since $\sin z/(z-N\pi)$ lies in $I_{N+1}$ but not in $I_N$, its value at $N\pi$ being $(-1)^N$. So $\mathcal O(\mathbb C)$ is not Noetherian, hence not a finitely generated $\mathbb C$-algebra, and the proof breaks at its first step.
3. *Without finite type: quasi-compact and zero-dimensional.* Let $R=\mathbb C^{\mathbb N}$ be the ring of complex sequences, $X=U=\operatorname{Spec}R$ and $k=0$. Each evaluation $a\mapsto a_n$ is a complex point, and its kernel $\mathfrak m_n$ is generated by the idempotent $1-\delta_n$. So $\mathfrak m_n=\mathfrak m_n^2$, and every $n$ gives a transversal zero of the empty family. Each $\{\mathfrak m_n\}=D(\delta_n)$ is open in $\operatorname{Spec}R$, which is quasi-compact because it is affine. So a quasi-compact space carries infinitely many isolated points. They do not form a closed set, and $R$ is not Noetherian: the ideal of finitely supported sequences is not finitely generated. Quasi-compactness alone does not bound the number of isolated points; the Noetherian property does.
4. *Without affineness.* The disjoint union $X=\coprod_{n\in\mathbb N}\mathbb A^1_{\mathbb C}$ is locally of finite type over $\mathbb C$, and the section $\varphi=t$ on every copy has a transversal zero at each origin. Here $U=X$ is not quasi-compact, hence not affine, and the theorem does not apply. In the consumer $U=D(h)$ is affine.

**Remark (what each hypothesis pays for) [Expository].**

- *Quasi-compactness.* It enters through the affineness of $U$: a single ring $A$ describes all of $U$. With finite type, that ring is Noetherian, and Lemma 3 is a Noetherian induction, which is stronger than quasi-compactness. Counterexample 3 shows that quasi-compactness alone is not enough, and counterexample 4 shows what happens without it.
- *Closedness.* The common zeros are the complex points of the closed subscheme $Z$, and the proof sees this as $I\subseteq\mathfrak m_z$ (lines 97–99). Each $\mathfrak m_z$ is maximal, so each transversal zero is a closed point of $Z$, and by Lemma 2 this closed point is a whole irreducible component of $Z$. By Stacks 00EH it is even open in $Z$. The proof never uses that the zero set is closed, or compact, in the analytic topology.
- *The residue field.* The evaluation $\mathrm{ev}_z$ is onto $\mathbb C$ (lines 94–95), so $\mathfrak m_z$ is maximal with residue field $\mathbb C$; and constants take their own values (lines 60–62), so the kernel determines the point (Lemma 4). The Nullstellensatz is not used. The proof needs only the map from points to maximal ideals, not its surjectivity, which Lemma 5 of the reduced auxiliary projection supplies for a different purpose.
- *Zero-dimensionality.* It is paid by Lemma 2: no prime lies strictly between $I$ and $\mathfrak m_z$, so $Z$ has dimension $0$ at $z$, and in fact $\mathcal O_{Z,z}=\mathbb C$. This is a property of $Z$ at the points of $T$ only. Elsewhere $Z$ may have components of positive dimension, as in counterexample 1. No dimension theory is used.

**Remark (what is and is not claimed) [Expository].**

- The bound is the number of minimal primes over $I$. No Bézout bound, degree or multiplicity appears. In the plane example with $c=0$ we have $|T|=3=\dim_{\mathbb C}A/I$, the product of the degrees, but the archive proves nothing of this kind.
- The theorem says nothing about the zeros that are not transversal. They may be infinite in number (counterexample 1). In the consumer they are excluded beforehand by the Sard step.
- No topology is used: not the analytic topology, not compactness of $X(\mathbb C)$, not the holomorphic inverse function theorem, and not smoothness of $X$. Once $A$ is known to be Noetherian, the step is pure commutative algebra.
- The following are used at their statements and not read here: Mathlib's <code>set_has_maximal_iff_noetherian</code>, <code>Algebra.FiniteType.isNoetherianRing</code> (Hilbert's basis theorem), <code>LocallyOfFiniteType.finiteType_of_affine_subset</code>, <code>RingHom.FiniteType.of_surjective</code>, <code>RingHom.ker_isMaximal_of_surjective</code>, <code>Ideal.comap_map_of_surjective'</code>, <code>Ideal.map_isPrime_of_surjective</code>, <code>IsAffineOpen.SpecMap_appLE_fromSpec</code> and <code>Set.Finite.of_finite_image</code>, together with the archive's evaluation lemmas <code>CxPts.ev_eq</code> and <code>CxPts.ev_algX</code>, whose definitions are read in the Sard step. The jet forms and the Sard argument retain their stated scope. See [holomorphic local sections](#holomorphic-local-sections-of-étale-families) for the chart inverse and the [change of denominator](#changing-the-denominator-in-cotangent-generation) for transport to the final projective chart. The cotangent basis <code>CotDim.exists_cotangent_basis</code> remains [Lean]. The [denominator and open-cover proof](#choosing-the-denominator-and-detecting-the-open-cover) reads the two producers called at lines 162 and 176.

**Reading the formal proof.** Paths are relative to the root of archive A2 (Lean 4.33.1, joined SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>, Mathlib pinned at <code>0df444a360eaa60ab8c11dca51a86af692955474</code>).

| Node | A2 path and lines | Role and reading |
|---|---|---|
| <code>finite_complexPoints_transversal_zeros</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteComplexPointsTransversalZerosStatement.lean:8–12</code> | Exported statement; delegates to <code>TransvZeros.finite_transv_zeros</code>. R3 [Lean, read]. |
| <code>TransvZeros.finite_transv_zeros</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteComplexPointsTransversalZeros.lean:74–102</code> | The theorem. R3 [Lean, read]. |
| <code>TransvZeros.mem_minimalPrimes_of_le_sup_sq</code> | same file, <code>:14–47</code> | Lemma 2. R3 [Lean, read]. |
| <code>TransvZeros.eq_of_evHom_eq</code>, <code>evHom_algX</code>, <code>eq_of_ker_eq</code> | same file, <code>:49–58,60–62,64–72</code> | Lemma 4. R3 [Lean, read]. |
| <code>CxPts</code>, <code>ptsIn</code>, <code>ev</code>, <code>evHom</code>, <code>ev_eq</code>, <code>ev_algX</code> | <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/DetJacMatCoordsEqTransitionJacobianDet.lean:22,41,43,71,73,94–95</code> | Complex points and evaluation. Definitions read in the Sard step, rechecked here. |
| <code>valMap</code>, <code>PtsOver</code> | <code>src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemRangeCompIffOfIsClosedImmersion.lean:16–17,184</code> | Evaluation as a map of sections; points over the base. Definitions read. |
| <code>algX</code> | <code>src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean:204–205</code> | Constants as sections. Definition read. |
| <code>Sp</code>, <code>spMap</code> | <code>src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsCompletedStrictHens.lean:11–14</code> | The spectrum of a ring and of a ring map. Definitions read. |
| Actual call | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFormsTransversalAtComplexPoints.lean:98,100,161–162,185–188</code> | Consumer. Body read in the reduced auxiliary projection; the call and the use of <code>hfin</code> rechecked here. |

Mathlib supplies, with proofs read: <code>Ideal.isIdempotentElem_iff_of_fg</code> (<code>Mathlib/RingTheory/Ideal/IdempotentFG.lean:22–37</code>, by Mario Carneiro and Kevin Buzzard), <code>Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul</code> and <code>exists_mem_and_smul_eq_self_of_fg_of_le_smul</code> (<code>Mathlib/RingTheory/Finiteness/Nakayama.lean:28–81,83–87</code>, by Johan Commelin), and <code>Ideal.finite_minimalPrimes_of_isNoetherianRing</code> (<code>Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean:26–41</code>, by Thomas Browning). Cited at their statements: <code>set_has_maximal_iff_noetherian</code> (<code>Mathlib/RingTheory/Noetherian/Defs.lean:155</code>), <code>Algebra.FiniteType.isNoetherianRing</code> (<code>Mathlib/RingTheory/FiniteType.lean:187</code>), <code>RingHom.FiniteType.of_surjective</code> and <code>RingHom.FiniteType.comp</code> (same file, <code>:247,251</code>), <code>LocallyOfFiniteType.finiteType_of_affine_subset</code> (<code>Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:51</code>), <code>RingHom.ker_isMaximal_of_surjective</code>, <code>Ideal.comap_map_of_surjective'</code> and <code>Ideal.map_isPrime_of_surjective</code> (<code>Mathlib/RingTheory/Ideal/Maps.lean:842,1078,1102</code>), <code>IsAffineOpen.SpecMap_appLE_fromSpec</code> and <code>IsAffineOpen.fromSpec_top</code> (<code>Mathlib/AlgebraicGeometry/AffineScheme.lean:482,494</code>), <code>Set.Finite.of_finite_image</code> (<code>Mathlib/Data/Set/Finite/Basic.lean:579</code>), and the instance from <code>Smooth</code> to <code>LocallyOfFinitePresentation</code> (<code>Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:241</code>).

The [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets), the [jet forms](#forms-with-prescribed-jets-at-finitely-many-points), the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre), the [reduced-fibre trace](#from-the-finite-algebra-trace-to-the-reduced-fibre), the [global boundary](#from-fixed-point-vanishing-to-a-global-čech-boundary) and the [local Koszul weights](#from-a-finite-étale-chart-to-the-local-lefschetz-weight) keep the reading levels recorded there.

#### Choosing the denominator and detecting the open cover

The [finiteness argument](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes) leaves a finite list of places where the translated forms can all vanish. A denominator must be nonzero at those places and at the generic point, since its chart will also be used to form ratios in the function field. Once the denominator has been chosen, the proof checks coverage by testing complex points. These are two different uses of the ground field: infinitude supplies the form, and algebraic closedness turns a maximal ideal on an affine chart into a complex point.

**Example 1 [Expository].** On $\mathbb P^1_{\mathbb C}$ take $S=\{[1:0],[0:1]\}$ and $T=\{[1:1],[1:-1]\}$. In the pencil $\ell=X_0+aX_1$, the evaluations in that order are $1,a,1+a,1-a$. The forbidden values of $a$ are $0,-1,1$. With $a=2$, a degree-three denominator is $f_0=(X_0+2X_1)^3$, with values $1,8,27,-1$ at the chosen representatives. On $D_+(X_0)$ write $u=X_1/X_0$. The generic point is the zero prime of $\mathbb C[u]$, and $f_0/X_0^3=(1+2u)^3$ is a nonzero element of $\mathbb C(u)$. The zero of $f_0$ is $[-2:1]$, outside the prescribed set.

On $\mathbb P^2_{\mathbb C}$ let $S$ consist of the three coordinate points and let $T=\{[1:1:1],[1:-1:0],[0:1:-1]\}$. In $\ell=X_0+aX_1+a^2X_2$ the six values are $1,a,a^2,1+a+a^2,1-a,a-a^2$. Take $a=2$ and degree two. Then $f_0=(X_0+2X_1+4X_2)^2$ takes values $1,4,16,49,1,4$. With $u=X_1/X_0$ and $v=X_2/X_0$, its generic value in this trivialization is $(1+2u+4v)^2\ne0$ in $\mathbb C(u,v)$. Its vanishing line has underlying equation $X_0+2X_1+4X_2=0$, and contains, for instance, $[-2:1:0]$. In both cases the requirement is to avoid vanishing **at** the prescribed points. Vanishing elsewhere is allowed.

**Example 2 [Expository].** In $X=\mathbb A^2_{\mathbb C}=\operatorname{Spec}\mathbb C[x,y]$, the union $D(x)\cup D(y)$ has complement $V(x,y)$, the singleton defined by the maximal ideal $(x,y)$. The quotient by that ideal is $\mathbb C$, and the missed complex point is evaluation at $(0,0)$. In the punctured plane $W=X\setminus V(x,y)$, every complex point has at least one nonzero coordinate, and $D(x),D(y)$ cover $W$. Consider the smaller open $D(x)$ of $W$. Its complement in $W$ lies entirely in the chart $D(y)$ and is cut out there by $(x)\subset B=\mathbb C[x,y,y^{-1}]$. This ideal is prime, with quotient $\mathbb C[y,y^{-1}]$. It lies in the maximal ideal $(x,y-1)$ of $B$, with quotient $\mathbb C$. The map $B\to\mathbb C$ sends $(x,y,y^{-1})$ to $(0,1,1)$ and gives the missed point $(0,1)$ of $W$. More generally, if an open of $W$ misses any scheme point, a chart containing it cuts out a nonempty closed complement by a proper ideal in $B$ or $\mathbb C[x,x^{-1},y]$. A maximal ideal containing that ideal gives evaluation at $(a,b)$ with $b\ne0$ or $a\ne0$, respectively. Thus the only open of $W$ containing every $(a,b)\ne(0,0)$ is $W$ itself.

**Definitions.** For the structure map $p:X\to\operatorname{Spec}\mathbb C$, write $X(\mathbb C)$ for the morphisms $z:\operatorname{Spec}\mathbb C\to X$ over $\operatorname{Spec}\mathbb C$. If $U\subseteq X$ is open, $z\in U(\mathbb C)$ means that the image of the unique point of $\operatorname{Spec}\mathbb C$ lies in $U$, equivalently that $z$ factors through $U$. Write $R=\mathbb C[X_0,\ldots,X_N]$ with its standard grading. A point of $\operatorname{Proj}R$ is a homogeneous prime $P$ with $R_+\nsubseteq P$, where $R_+=(X_0,\ldots,X_N)$ is the irrelevant ideal. For a homogeneous $f$, $D_+(f)$ consists of the primes $P$ with $f\notin P$. For a morphism $\iota:X\to\mathbb P^N_{\mathbb C}$ write $D(f)=\iota^{-1}D_+(f)$, the archive's <code>fOpen</code>.

**Lemma 1 (finite subspace avoidance) [Lean, read].** If $K$ is an infinite field and $V_1,\dots,V_r$ are proper linear subspaces of a $K$-vector space $E$, there is an element of $E$ outside all $V_i$.

*Proof.* The empty family imposes no condition, and one proper subspace leaves a point outside it. For $r\ge2$, suppose the subspaces cover $E$. If $V_r$ is already contained in the union of the earlier subspaces, those earlier subspaces cover $E$, contrary to induction. Otherwise take $x\in V_r$ outside the others, and take $y\notin V_r$. For each $t\in K\setminus\{0\}$, the vector $x+ty$ lies outside $V_r$, so it must lie in an earlier subspace. Among the infinitely many parameters, two distinct ones, $s,t$, land in the same $V_i$ with $i<r$. Subtraction gives $(t-s)y\in V_i$, so $y\in V_i$ and then $x\in V_i$, a contradiction. This is the infinite-field case of the line and counting argument in Mathlib, which counts the nonzero parameters against the number of earlier subspaces. $\square$

**Theorem 2 (finite avoidance in projective space) [Lean, read].** For every $N,n\ge0$ and every finite set $A$ of scheme points of $\mathbb P^N_{\mathbb C}$, there exists $f\in R_n$ such that $A\subseteq D_+(f)$. In particular, for every integral $\mathbb C$-scheme $X$, every morphism $\iota:X\to\mathbb P^N_{\mathbb C}$, every $n\ge0$, and every finite $F\subseteq X(\mathbb C)$, a single $f\in R_n$ satisfies $\eta_X\in D(f)$ and $F\subseteq D(f)(\mathbb C)$.

*Proof.* For $P\in A$ define $V_P=P\cap R_1$. This is a linear subspace of $R_1$. Some coordinate variable $X_i$ lies outside $P$, since otherwise $P$ would contain $R_+$. Thus $V_P$ is proper. Lemma 1 chooses a linear form $\ell$ outside all these subspaces. Put $f=\ell^n$. Multiplication respects the grading and primality gives $\ell^n\notin P$ for each $P\in A$ (for $n=0$, $f=1$). For the second assertion take $A$ to be the union of the image of the underlying points of $F$ with the singleton $\{\iota(\eta_X)\}$. Membership in the inverse image open gives both conclusions. On any coordinate chart containing $\iota(\eta_X)$, the value means the image of the degree-zero fraction $f/X_i^n$ in $\kappa(\eta_X)$ is nonzero. $\square$

**Lemma 3 (the affine residue field) [Lean, read].** For any finitely generated $\mathbb C$-algebra $B$ and maximal ideal $\mathfrak m$, the structural map $\mathbb C\to B/\mathfrak m$ is an isomorphism.

*Proof.* The field $L=B/\mathfrak m$ is a finite type algebra over the Jacobson ring $\mathbb C$. Mathlib's <code>finite_of_finite_type_of_isJacobsonRing</code> presents $L$ as a quotient of a polynomial ring in finitely many variables. Its Jacobson polynomial theorem makes the map on constants integral (the kernel of the surjection onto the field is maximal). A finite type integral algebra is module-finite, by bounding the powers of each generator by a monic equation. Finally the map on constants is injective because its source is a field. Every $b\in L$ is integral, and its monic minimal polynomial is irreducible over $\mathbb C$, hence linear. If that polynomial is $T+c$, then $b=-c$ in $L$. Thus the structural map is surjective as well. The inverse is canonical over the given base. $\square$

**Theorem 4 (complex points detect opens) [Lean, read].** For every scheme $X$, every morphism $p:X\to\operatorname{Spec}\mathbb C$ locally of finite type, and every open $U\subseteq X$, if every morphism $z:\operatorname{Spec}\mathbb C\to X$ with $p\circ z=\operatorname{id}_{\operatorname{Spec}\mathbb C}$ factors through $U$, then $U=X$ as an open subscheme.

*Proof.* If $x\in X\setminus U$, choose an affine open $V$ containing $x$. Write $B=\Gamma(X,V)$. The affine-local characterization of locally finite type makes $B$ a finite type $\mathbb C$-algebra via $p$. The inverse image of $X\setminus U$ in $\operatorname{Spec}B\simeq V$ is a nonempty closed set $V(I)$. Take a maximal ideal $\mathfrak m$ containing the proper ideal $I$. The archive uses the equivalent topological argument. In the quasi-compact $T_0$ space $\operatorname{Spec}B$, a nonempty closed set has a minimal nonempty closed subset by the finite intersection property and Zorn’s lemma. If this subset had two distinct points, a $T_0$ open distinguishing them could be removed to give a smaller nonempty closed subset. The resulting closed singleton corresponds to a maximal ideal because the closure of a prime $P$ consists of the primes containing $P$. Form
$\phi:B\to B/\mathfrak m\xrightarrow{\sim}\mathbb C$ using the inverse in Lemma 3. It fixes constants, and its kernel is $\mathfrak m$. Thus the map on spectra followed by $V\hookrightarrow X$ gives a complex point whose underlying point is the image of $\mathfrak m$. It misses $U$, a contradiction. $\square$

**Remark (Jacobson density).** The scheme-theoretic formulation is that closed points are dense in every closed subset of a scheme locally of finite type over a field. On an affine chart, the strong form of the Nullstellensatz says that a radical ideal in a finite type algebra over a field is the intersection of the maximal ideals above it. The proof of Theorem 4 only needs one maximal ideal in a nonempty affine closed set. The weak form, which identifies residue fields over an algebraically closed field, supplies the extra step from an affine closed point to a morphism over the base. The conclusion concerns a Zariski open. For example, the subset of $\mathbb A^2_{\mathbb C}$ consisting solely of its closed points contains the image of every complex point and omits the generic point. [Stacks, Theorem 10.34.1](https://stacks.math.columbia.edu/tag/00FV) · [Stacks, locally finite type over a field](https://stacks.math.columbia.edu/tag/02J5)

**Remark (the two calls in Lemma 2).** In <code>exists_transversal_forms_first_separate</code>, line 161 produces the finite set $T$ of transversal common zeros in $D(h)$. The Sard step makes every common zero in $D(h)$ transversal. At line 162, Theorem 2 with $F=S\cup T$ gives the degree-$n$ denominator $f_0$, including its generic nonvanishing. To check the union $D(f_0)\cup\bigcup_jD(F_j)$, take any complex point outside all $D(F_j)$. In $D(h)$ it belongs to $T$. Outside $D(h)$ the relation $F_j=g_j+c_jh$ forces all $g_j$ to vanish, so the base-locus condition puts it in $S$. In either case it lies in $D(f_0)$. Line 176 invokes Theorem 4 to turn this pointwise test into property (i), the cover of the scheme. The same avoidance theorem supplies the linear reference form in Step 2 of the jet-forms proof. The [change of denominator](#changing-the-denominator-in-cotangent-generation) proves the remaining containment used at line 226.

**Where the hypotheses enter [Expository].**

- *Generic points of components.* On the reduced union $X=V_+(X_0X_1)\subset\mathbb P^2_{\mathbb C}$, the two component generic primes are $(X_0)$ and $(X_1)$. The linear form $X_0$ is nonzero at the latter and at $[1:0:0]$, but it vanishes at the former. Checking one component cannot stand for checking the generic point of an integral scheme. The projective avoidance theorem itself applies to any finite list of scheme points. In this example insert both generic primes and use $X_0+X_1$, which also evaluates to $1$ at $[1:0:0]$. Taking a power works for any positive degree.
- *Local finite type.* $\operatorname{Spec}\mathbb C(t)$ has one point and no complex points over $\mathbb C$. A $\mathbb C$-map $\mathbb C(t)\to\mathbb C$ would send $t$ to some $a\in\mathbb C$ and the unit $t-a$ to zero. The empty open therefore contains all complex points vacuously. The field $\mathbb C(t)$ is transcendental over $\mathbb C$ and, by the finite-type field lemma, cannot be a finitely generated $\mathbb C$-algebra.
- *Algebraic closedness.* In $\mathbb A^1_{\mathbb Q}$ the proper open $D(t^2+1)$ contains every rational point, since $a^2+1\ne0$ for $a\in\mathbb Q$. Its complement is the closed point $(t^2+1)$, with residue field $\mathbb Q[t]/(t^2+1)\cong\mathbb Q(i)$. A maximal ideal still witnesses the omitted locus. It has no lift to a rational point.

| Declaration | Fixed location and scope |
|---|---|
| <code>EtProj.exists_form_forall_notMem</code>, <code>EtProj.exists_form_genericPoint_cxPts</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsProjFormNonvanishingGenericPointComplexPoi.lean:15–40</code>. R3, the proper subspaces, the power, and insertion of the image of the generic point. |
| <code>MaxPt.eq_top_of_forall_cxPts_mem</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqTopOfForallComplexPointsMemOpens.lean:14–68</code>. R3, the affine complement and the map with specified kernel. |
| Mathlib direct supply | <code>Mathlib/Algebra/Module/Submodule/Union.lean:33–95</code>; <code>Mathlib/RingTheory/Jacobson/Ring.lean:633–686</code>; <code>Mathlib/FieldTheory/IsAlgClosed/Basic.lean:215–230</code>. Read for finite avoidance, the polynomial presentation and finite residue field, and bijectivity of the structural map. |
| Retained supply | The deeper Jacobson polynomial induction (<code>aux_IH</code>), <code>Algebra.IsIntegral.finite</code>, and the affine finite-type interface remain named. The [change of denominator](#changing-the-denominator-in-cotangent-generation) reads <code>RatioSpanCotangentChangeDenominator.lean:47–138</code> at scoped R3. |

The reading levels refer to proof bodies at the scope indicated. Archive and Mathlib pins are in the [source ledger](../sources/SOURCES.md#chapter-12-1244-finite-avoidance-and-complex-point-detection).

#### Changing the denominator in cotangent generation

The [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets) establishes transversality in the chart $D(h)$. The preceding [denominator and open-cover proof](#choosing-the-denominator-and-detecting-the-open-cover) chooses $f_0$. Lemma 2 needs it in $D(f_0)$, where the projection takes its origin fibre. At a common zero in both charts, changing the denominator changes the first derivatives by a single nonzero scalar. The archive also has to transport an ideal containment between the two rings of sections. This requires an argument on their intersection.

**Example 1 (two charts of the projective line) [Expository].** On $\mathbb P^1$ take $a=X_0$, $b=X_1$, $f=X_1-2X_0$, and $z=[1:2]$. On $D_+(a)$ set $t=X_1/X_0$, and on $D_+(b)$ set $s=X_0/X_1$. The chart rings are $\mathbb C[t]$ and $\mathbb C[s]$, with evaluation ideals $(t-2)$ and $(s-1/2)$. The overlap inverts $t$ on the first side and $s$ on the second, with $s=t^{-1}$. The two ratios are $t-2$ and $1-2s$. With $u=t-2$ and $v=s-1/2$, in the common local ring,
$v=(2+u)^{-1}-1/2=-u/(2(2+u))\equiv -u/4\bmod (u^2)$.
Thus the coordinate transition has matrix $(-1/4)$, with inverse $(-4)$. The first ratio has class $[u]$ and the second has class $-2[v]=(1/2)[u]$. The ratio transition matrix is $(1/2)$, with inverse $(2)$. The scalar $1/2$ is the value of $a/b=s$ at $z$.

**Example 2 (a quadratic denominator on the projective plane) [Expository].** On $\mathbb P^2$ take $z=[1:1:1]$ and the degree-two forms
$a=X_0^2$, $b=X_0^2+X_0X_1+X_2^2$, $f_1=X_0(X_1-X_0)$ and $f_2=X_0(X_2-X_0)$.
Use $x=X_1/X_0$, $y=X_2/X_0$ on $D_+(a)$. In the local ring at $(1,1)$ put $u=x-1$, $v=y-1$, so $\mathfrak m=(u,v)$ and $([u],[v])$ is a basis of $\mathfrak m/\mathfrak m^2$. The overlap in this chart inverts $b/a=1+x+y^2=3+u+2v+v^2$. Its inverse is congruent to $1/3-(u+2v)/9$ modulo $\mathfrak m^2$, as multiplication shows. The two initial ratios are $u,v$. The new ratios are $u/(3+u+2v+v^2)$ and $v/(3+u+2v+v^2)$. For the first ratio, the quotient rule at $(1,1)$ gives the $x,y$ derivatives $(3\cdot1-0\cdot1)/9=1/3$ and $(3\cdot0-0\cdot2)/9=0$. For the second it gives $(3\cdot0-0\cdot1)/9=0$ and $(3\cdot1-0\cdot2)/9=1/3$. With the differentials as rows, the transition is $\begin{pmatrix}1/3&0\\0&1/3\end{pmatrix}$, of determinant $1/9$, with inverse $\begin{pmatrix}3&0\\0&3\end{pmatrix}$. This inverse also comes from multiplication by $b/a$, whose constant term is $3$. The overlap from $D_+(b)$ is the principal open of $a/b$, so both computations take place at the same point of $X$.

**Definitions.** Let $R=\mathbb C[X_0,\ldots,X_N]$ with its standard grading and $\iota:X\to\mathbb P^N_{\mathbb C}$. For a homogeneous $c$ put $D(c)=\iota^{-1}D_+(c)$. When $f,c$ have the same degree, $f/c$ denotes the pullback of a degree-zero fraction on $D_+(c)$ (<code>EtProj.fRatio</code>). Equivalently, on $D_+(X_i)$, both forms of degree $n$ are represented in the same trivialization by $f/X_i^n$ and $c/X_i^n$. Their ratio is independent of $i$ because both representatives acquire the same transition factor. The base locus of a family consists of the points where every member vanishes. At a common zero of the numerators outside the vanishing loci of the two denominators, both tuples of ratios vanish. For the enlarged family $(a,b,f_1,\ldots,f_k)$ this point lies outside the base locus.

For a $\mathbb C$-point $z$ in an open $U$, write $A_U=\Gamma(U,\mathcal O_X)$ and $m_U=\ker(A_U\to\mathbb C)$, where the map evaluates along $z$. Evaluation is onto by constants. In the local ring $L=\mathcal O_{X,z}$ write $\mathfrak m$ for its maximal ideal and $d_z r=[r-r(z)]$ in $\mathfrak m/\mathfrak m^2$ for the first-order class of a germ $r$. If $U$ is affine, $L=(A_U)_{m_U}$. The map $m_U/m_U^2\to\mathfrak m/\mathfrak m^2$ is an isomorphism. Indeed localization commutes with quotients, and every element outside $m_U$ acts on $m_U/m_U^2$ by its nonzero residue, hence already invertibly.

**Lemma (localization and first-order ideals) [Lean, read].** Let $A$ be a ring with maximal ideal $m$ and $s\notin m$. The kernel of $A_s\to A/m$ induced by reduction is $mA_s$. For any ideal $I\supseteq m^2$, an element $g\in A$ whose image lies in $IA_s$ belongs to $I$.

*Proof.* The evaluation of $x/s^j$ is $\bar x/\bar s^j$, which vanishes exactly when $x\in m$. Membership in the extended ideal gives $wg\in I$ for some power $w=s^\ell$, by clearing denominators, including any extra power needed for equality in the localization. Since $\bar w$ is invertible, choose $q$ and $i\in m$ with $qw+i=1$. Then
$g=(q^2w+2qi)wg+i^2g\in I$,
by squaring this identity and using $i^2\in m^2$. This argument applies even when $s$ is a zero divisor. The condition on $I$ matters. In $\mathbb C[t]$, with $m=(t)$, $s=t-1$ and $I=(t-1)$, the extended ideal is the whole localized ring although $1\notin I$. $\square$

**Theorem (change of denominator) [Lean, read].** Let $p:X\to\operatorname{Spec}\mathbb C$ be a scheme over $\mathbb C$, let $\iota:X\to\mathbb P^N_{\mathbb C}$ be a closed immersion, and take $a,b,f_1,\ldots,f_k\in R_n$ with $n>0$. Let $z$ be a point over $\mathbb C$ in the sense of $p$, lying in $D(a)\cap D(b)$. For $c=a,b$ put $m_c=m_{D(c)}$ and $I_c=(f_1/c,\ldots,f_k/c)$ in $A_{D(c)}$. Then
$m_a\subseteq I_a+m_a^2$ if and only if $m_b\subseteq I_b+m_b^2$. The archive states the forward ideal implication. Its proof permits the reverse implication by exchanging $a,b$.

*Proof.* The projective basic opens for $a,b$ are affine by positive homogeneity, with rings $(R[a^{-1}])_0$ and $(R[b^{-1}])_0$. Their pullbacks along a closed immersion are affine. Write $A=A_{D(a)}$, $B=A_{D(b)}$ and $C=\Gamma(W,\mathcal O_X)$, where $W=D(a)\cap D(b)$. On $D_+(a)$ a homogeneous prime is in $D_+(b)$ exactly when the degree-zero element $b/a$ is invertible at that point. One can check this on a coordinate chart by dividing both forms by $X_i^n$, where the representative of $a$ is a unit. Pullback preserves the basic open of a section. In <code>ProjFrac.frac_mul_eq</code>, the multiplication identity is proved by comparing stalk evaluations and cross-multiplying. For <code>ProjFrac.basicOpen_frac</code>, a unit fraction has unit numerator in the ordinary prime localization since the denominator is already a unit there. Conversely the reversed degree-zero fraction gives an inverse on the overlap. Hence $W$ is the principal open of $s=b/a$ in $D(a)$ and of $t=a/b$ in $D(b)$. In particular the restriction maps identify $C$ with $A_s$ and $B_t$. By the same-degree fraction identity and compatibility of restriction with pullback, in $C$ we have $st=1$ and $f_j/a=s(f_j/b)$. Thus $I_a C=I_b C$.

Evaluation on $W$ agrees with evaluation after restriction from either chart, so the lemma identifies $m_W=m_a C=m_b C$. Extend the inclusion on $A$ to $C$, using extension of ideals to commute with sums and products. This gives $m_W\subseteq I_b C+m_W^2=(I_b+m_b^2)C$. For any $g\in m_b$, its image belongs to that extended ideal. Apply the lemma to $B,t,I_b+m_b^2$ and use $t(z)\ne0$ to recover $g\in I_b+m_b^2$. The reverse follows by symmetry. $\square$

**Corollary (common-zero cotangent classes) [Expository].** Under the same hypotheses, at a common zero of the $f_j$, either condition is equivalent to the corresponding ratio classes generating $\mathfrak m/\mathfrak m^2$ in the same local ring $L$, and $d_z(f_j/b)=(a/b)(z)\,d_z(f_j/a)$ for every $j$.

*Proof.* The maps from the two chart rings and the overlap to the stalk identify their localizations at the evaluation kernels with $L$. At a common zero the $I_c$ lie in $m_c$. The image of $I_c$ in $m_c/m_c^2$ is the $\mathbb C$-span of the classes of its generators, since all coefficients act there by their residues. The preceding isomorphism with $\mathfrak m/\mathfrak m^2$ gives the asserted equivalence. To calculate the first-order classes, the product identity in $L$ gives $d_z(rq)=r(z)d_zq+q(z)d_zr$. For a unit $q$ this also gives $d_z(q^{-1})=-q(z)^{-2}d_z q$, upon differentiating $qq^{-1}=1$. With $r=f_j/a$ and $q=b/a$, we have
$d_z(r/q)=q(z)^{-1}d_z r-r(z)q(z)^{-2}d_z q$.
At the common zero $r(z)=0$ for every $j$, so the second term drops out and every class is multiplied by the same nonzero scalar. The transformation on the list of $k$ classes has matrix $(a/b)(z) I_k$. $\square$

**Remarks on the hypotheses.**

- *At the point and on the chart.* The unit in the stalk comes from membership in the intersection. The ring of sections of that intersection is a principal localization because each chart is affine and the intersection is the basic open of its transition ratio. The stalk argument itself only needs local trivializations and unit germs. The archive uses positive degree and the closed immersion to secure the affine presentation. It requires no smoothness, integrality, generic nonvanishing or relation between $k$ and $\dim X$ at this step. Its statement uses $p$ for evaluation at a point over $\mathbb C$ and does not need $\iota$ to be a map over $p$. In Lemma 2 the immersion is over the base.
- *Removing nonvanishing.* On $\mathbb P^1$ with $a=X_0$, $b=X_1$, $f=X_1$ and $z=[1:0]$, the ratio $f/a=t$ generates the cotangent line at $z$. The expression $f/b$ is defined on $D_+(b)$, which misses $z$. It even extends as the constant $1$, whose differential is zero. Meanwhile $a/b=1/t$ has a pole at $z$. Thus extending a particular expression across the excluded point gives no generation theorem.
- *Removing the common degree.* On $\mathbb P^1$ with $a=X_0$, $b=X_1^2$ and $f=X_1$, both denominators are nonzero at $[1:1]$. The expression $f/b$ takes value $1$ at the representative $(1,1)$ and $1/2$ at $(2,2)$. It has degree $-1$ and is not a function of the projective point. Normalizing $X_0=1$ gives the expression $1/t$, with differential $-d_z t$ at $t=1$. Normalizing $X_1=1$ gives the constant $1$ and differential zero on the same overlap. The mixed-degree expression therefore gives no intrinsic cotangent class even after centering. The same failure of descent occurs at a common zero: use $f=X_1-X_0$ at $[1:1]$ and compare the two representatives $(1,2)$ and $(2,4)$ of the neighboring point $[1:2]$ in the same chart. The values of $f/b$ are $1/4$ and $1/8$, so the expression does not descend to a germ at $[1:1]$.
- *Common zeros and first derivatives.* The archive's ideal implication does not require vanishing of the numerators. If one ratio has nonzero residue, its ideal together with the square of the evaluation kernel is the entire ring, by the inverse-modulo-$m^2$ argument of the lemma. An assertion about centered derivatives alone would be different. For $a=X_0$ and $b=f=X_1$ at $[1:1]$, $d_z(f/a)=d_z t$ spans, while $d_z(f/b)=0$. The common-zero assumption is exactly what removes the extra term in the quotient rule.

**How Lemma 2 uses the theorem.** The consumer <code>exists_transversal_forms_first_separate</code> builds the form system in two stages, then checks two kinds of common zeros. The line numbers below refer to <code>ExistsFormsTransversalAtComplexPoints.lean</code>.

1. Lines 22–75 connect a homogeneous numerator's vanishing to evaluation of its ratio, and show that adding $c_jh$ adds the expected scalar multiple on any chart. Lines 83–101 set up the desired cover, generic nonvanishing and transverse zero clause. They obtain the jet data $(n,h,g_j)$ for $S$, make $D(h)$ affine, and take the Sard exceptional set for $g_j/h$.
2. Lines 102–137 allow at most one bad scalar per $j$ for generic nonvanishing. Indeed, if two translates vanish at the generic point, subtraction there forces $h$ and then $g_j$ to vanish. The corresponding coordinate hyperplanes together with the Sard exceptional set are null, so choose $c$ outside their union. Lines 138–160 define $F_j=g_j+c_jh$. Because $F_j/h=g_j/h+c_j$, their common zeros on $D(h)$ are transversal by the Sard supply.
3. Lines 161–175 use finite transversal zeros to form $T$, then finite avoidance to choose $f_0$ of degree $n$ nonzero on $S\cup T$ and at the generic point. Outside $D(h)$ a common zero of the $F_j$ is a common zero of the $g_j$ and belongs to $S$ by the jet base-locus clause. Lines 176–188 use complex-point detection to prove $D(f_0)\cup\bigcup_j D(F_j)=X$, since each common zero lies in $S$ or $T$. Lines 189–206 recover generic nonvanishing of each $F_j$ and show that all ratios $F_j/f_0$ vanish on $S$.
4. Lines 207–222 take a common zero of $F_j/f_0$ in $D(f_0)$. For $z\in S$, the jet clause gives generation by $g_j/f_0$ and $h/f_0\in m_{f_0}^2$. The correction $c_jh/f_0$ contributes zero in the cotangent quotient. For $z\notin S$, lines 223–225 force $z\in D(h)$ by the base-locus clause. At line 226 the theorem is applied with $f_j=F_j$, $a=h$, $b=f_0$ and the Sard containment from line 159. Both denominators are nonzero at this point, and the two chart rings refer to the same stalk.
5. Lines 234–258 package the tuple as $(f_0,F_1,\ldots,F_d)$ for the finite projection. In the reduced auxiliary projection, the ideal of the origin fibre is generated by $F_j/f_0$ on $D(f_0)$. At each maximal ideal above that ideal, Lemma 2 now supplies the first-order containment used by the Artinian reducedness criterion. The finite projection, the fibre and germ comparison, and the transport of <code>RedFib</code> use the geometric inputs recorded in the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre).

The dependencies of the assembly are as follows. Each arrow passes the data just proved to the next step.

~~~text
Jet forms on S ──┬──> Sard on D(h) + generic-point hyperplane avoidance
                 │                   │
                 │                   v
                 │            F_j = g_j + c_j h
                 │              │            │
                 │              │            └──> Transversality on D(h)
                 │              │                        │
                 │              │                        v
                 │              │                Finite set T on D(h)
                 │              │                        │
                 │              │                        v
                 │              │           Avoid S ∪ T and generic point
                 │              │                        │
                 │              │                        v
                 │              │                        f_0
                 │              │                        │
                 │              └──> Common zeros in S ∪ T + avoidance
                 │                         │
                 │                         v
                 │                 Complex-point test → open cover
                 │
                 └──> At zeros in S: second-order correction on D(f_0)
                      At zeros off S: base locus → D(h)
                          → Sard containment → denominator change to D(f_0)
                                       │
                                       v
             Open cover + generic nonvanishing + vanishing on S
                      + transversality on D(f_0) → Lemma 2
                                       │
                                       v
                    Finite projection → reduced origin fibre
                             → germ comparison and RedFib transport
~~~

The same theorem already serves the jet producer at <code>ExistsFormsVanishingComplexPointsFullJets.lean:612</code>. At $y\in S$ it transfers the $g_j$ from the reference chart $D(a)$ to an arbitrary degree-$n$ denominator chart $D(f_0)$ containing $y$. The second-order clause for $h/f_0$ is supplied separately at line 609.

**Proof locations.** In <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/RatioSpanCotangentChangeDenominator.lean</code>, lines 12–32 prove contraction by clearing denominators and squaring the inverse relation. Lines 34–45 lift the evaluation kernel through localization. Lines 47–82 set up the overlap and the fraction identity, lines 84–106 identify the two localizations and their compatible evaluations, and lines 107–138 map the first containment to the overlap and contract the second one back. The direct proofs <code>ProjFrac.frac_mul_eq</code> and <code>ProjFrac.basicOpen_frac</code> are in <code>src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean:74–111,177–211</code>. The affine chart and localization interfaces and the deeper Sard and geometric inputs carry the reading levels recorded in the [source ledger](../sources/SOURCES.md#chapter-12-1244-cotangent-denominator-change).

The reduced origin fibre feeds the trace sum used in the [local Lefschetz weight](#from-a-finite-étale-chart-to-the-local-lefschetz-weight).

### 12.4.5 Compact-open fixed spaces and the smooth contragredient

The local representation-theoretic argument uses the contragredient twice. At the highest nonzero mirabolic derivative it pairs a vector of the original representation with a functional in the contragredient. Later it reverses the duality on an irreducible Jacquet label. The first step needs enough *smooth* functionals to detect nonzero vectors. The second needs the smooth bidual to recover the representation. Compact-open fixed spaces explain both facts and show where finite-dimensionality enters.

The construction starts with a finite sum on each compact orbit. The usual averaging integral therefore reduces to a finite calculation for each vector.

#### Two calculations

**An infinite-dimensional representation of $\mathrm{GL}_1(\mathbb Q_3)$.** Write an element of $\mathbb Q_3^\times$ uniquely as $3^m u$ with $u\in U=\mathbb Z_3^\times$. Let $V$ be the locally constant complex functions on $U$, and let $3^m u$ act by $f(x)\mapsto f(u^{-1}x)$. Write $K_0=U$ and $K_r=1+3^r\mathbb Z_3$ for $r\ge1$. Compactness of $U$ gives a finite cover by cosets on which a given $f$ is constant. Taking the largest depth in this cover shows that $f$ is fixed by some $K_r$. For $r\ge1$, reduction modulo $3^r$ identifies $U/K_r$ with the invertible residues, so
$$
V^{K_r}=\mathbb C^{\,U/K_r},\qquad \dim V^{K_r}=d_r=2\cdot3^{r-1}.
$$
At $K_0$ the fixed space is the constants and $d_0=1$. Every compact open subgroup contains some $K_r$, so its fixed space is finite-dimensional as well. The unbounded sequence of dimensions proves that $V$ is infinite-dimensional.

For functions $f,h$ choose a depth $s$ at which both descend and define the bilinear pairing as $d_s^{-1}\sum_{x\in U/K_s} f(x)h(x)$. Refining the depth repeats each term by the same factor and leaves the value unchanged. The group permutes the cells, so sending $h$ to the functional given by pairing with $h$ is equivariant. At depth $r$, the indicators of the cells form a basis and the pairing matrix is $d_r^{-1}I$. Thus a functional with values $a_C$ on the indicators is represented by the function with value $d_r a_C$ on cell $C$. In particular, at depth two the six cells are $1,2,4,5,7,8\bmod 9$. The $2\bmod 3$ indicator is the sum of the indicators of $2,5,8\bmod 9$. A functional represented at depth one by $2\,1_{2\bmod3}$ takes value $1/3$ on each of those three depth-two indicators and value $1$ on their sum.

For a $K_r$-fixed functional and a test function at depth $s\ge r$, invariance makes the values on the depth-$s$ indicators constant among the cells above each depth-$r$ cell. Since their sum is its indicator, each value is $d_r/d_s$ times the corresponding $a_C$. This agrees with the pairing against the chosen $h$ at every depth. Since every smooth functional is fixed by some $K_r$, this identifies the entire smooth dual with $V$. It also gives the evaluation identification with the smooth bidual, using symmetry of the displayed pairing. The algebraic functional $f\mapsto f(1)$ is moved by every nonidentity element of $U$ because residue cells separate distinct points. Its stabilizer in $\mathbb Q_3^\times$ is $3^{\mathbb Z}$, which is not open. This functional therefore lies outside the smooth contragredient.

**A finite quotient with a visible kernel.** Use $U\to(\mathbb Z/3\mathbb Z)^\times=\{1,2\}$ and its two-dimensional permutation representation on $\mathbb C^2$. The class of $2$ swaps the two entries. For $K=U$, the fixed space is $\mathbb C(1,1)$ and the span of relations $k v-v$ is $\mathbb C(1,-1)$. Averaging sends $(x,y)$ to $((x+y)/2,(x+y)/2)$. A functional taking value $a$ on $(1,1)$ has unique invariant extension $(x,y)\mapsto a(x+y)/2$. In the dual coordinate basis the fixed line is spanned by $e_1'+e_2'$, which takes value $2$ on $(1,1)$. At the kernel $K_1$, the fixed spaces are both two-dimensional and the evaluation matrix in dual bases is $I$. The sign line $\mathbb C(1,-1)$ is irreducible, with dual action $(-1)^{-1}=-1$. For $K=U$ its fixed space is zero, whereas at $K_1$ the map $t(1,-1)\mapsto t$ exhibits the pairing on that line. On the whole two-dimensional smooth dual, a bidual form taking values $a,b$ on $e_1',e_2'$ is evaluation at $(a,b)$. On the $U$-fixed layer a bidual form taking value $c$ on $e_1'+e_2'$ is evaluation at $(c/2,c/2)$.

#### Definitions and finite averaging

Let $G$ be a topological group and $\pi$ a complex linear action on a vector space $V$. Smoothness means that every vector has open stabilizer. We use a compact-open basis at the identity when stated: every identity neighbourhood contains a compact open subgroup. Admissibility means smoothness together with $\dim V^K<\infty$ for each compact open $K$. The full algebraic dual is $V^*=\operatorname{Hom}_{\mathbb C}(V,\mathbb C)$, with action $(g\ell)(v)=\ell(\pi(g^{-1})v)$. Its smooth part is the smooth contragredient $V^\vee$. The pairing $\ell(v)$ is complex bilinear.

**Lemma (compact orbit averaging) [Lean, read].** Suppose $V$ is smooth and $K\subset G$ is compact. For any vector $u$ and any linear map $f$ that is constant on the $K$-orbit of $u$, there is a fixed vector $u_0\in V^K$ with $f(u_0)=f(u)$. Moreover, for
$$
D_K=\operatorname{span}_{\mathbb C}\{\pi(k)w-w:k\in K,\ w\in V\},
$$
one has $V=V^K\oplus D_K$.

**Proof.** Smoothness makes the orbit map locally constant because the translate by $k$ of the open stabilizer is a neighbourhood on which the value is $\pi(k)u$. The fibres cover the compact subgroup $K$, so only finitely many values occur. The orbit contains $u$ and $K$ permutes its elements. Average the distinct orbit vectors to obtain $u_0$. Its image is $f(u)$ by the hypothesis on the orbit. Also, $u-u_0$ is the average of differences $u-\pi(k)u$ and belongs to $D_K$.

For the directness, write a vector $v\in V^K\cap D_K$ as a finite linear combination of differences $\pi(k_i)w_i-w_i$. Take the finite union of the $K$-orbits of the $w_i$. Let $P$ be the image of $K$ in the permutation group of this finite set and choose a representative $k_p$ for each $p\in P$. The unnormalized sum $A=\sum_{p\in P}\pi(k_p)$ kills each displayed difference. Indeed right multiplication by the permutation of $k_i$ reindexes the sum on $w_i$. Since $v$ is fixed, $Av=|P|v$. The image contains the identity, so the positive integer $|P|$ is nonzero in $\mathbb C$ and $v=0$. This proves directness. It also shows that $u_0$ is the value of a linear projection $P_K$ with kernel $D_K$, since the fixed representative of each class modulo $D_K$ is unique. The two finite sums here correspond to the actual `exists_fixed_map_eq` and `eq_zero_of_fixed_twKer` proofs. The first divides by the orbit size and the second cancels the size of the finite permutation image. Neither uses finite-dimensional fixed spaces. [Archive citations](../sources/SOURCES.md#chapter-12-compact-open-fixed-spaces-and-the-smooth-contragredient)

#### Restriction, evaluation and irreducibility

**Theorem (fixed-space duality) [Lean, read].** For a smooth complex representation and every compact open $K$, restriction gives an isomorphism
$$
r_K:(V^\vee)^K \longrightarrow (V^K)^*,\qquad \ell\longmapsto \ell|_{V^K}.
$$
When $V^K$ is finite-dimensional, evaluation is a perfect pairing between $V^K$ and $(V^\vee)^K$, identifying each side with the full dual of the other.

**Proof.** Since $K$ contains inverses, an algebraic functional is fixed by the dual action of $K$ exactly when $\ell(\pi(k)w)=\ell(w)$ for all $k\in K$ and $w\in V$. Such a functional annihilates $D_K$. Thus it is determined by its values on $V^K$, even when $K$ is merely compact. Conversely, compose a linear functional on $V^K$ with $P_K$ to extend it to $V$. The resulting form annihilates $D_K$, hence is invariant by $K$. Openness of $K$ puts it in $V^\vee$ because its stabilizer contains $K$. In the archive, `exists_fixed_contra` uses a linear left inverse of the injection $V^K\to V/D_K$. The preceding lemma makes this injection onto and identifies the extension with composition with $P_K$. The proof of `res_injective` uses `form_ext`: given two invariant forms, apply the orbit-average lemma with their difference as $f$. This proves uniqueness from equality on fixed vectors. Finite-dimensional algebraic evaluation gives the second identification whenever $V^K$ is finite-dimensional.

**Theorem (smooth biduality) [Lean, read].** Suppose $G$ has a compact-open basis at the identity and $V$ is smooth. The map
$$
\mathrm{ev}_V:V\longrightarrow (V^\vee)^\vee,\qquad
v\longmapsto [\ell\longmapsto\ell(v)]
$$
is an injective intertwiner. If $V$ is admissible, $V^\vee$ is admissible and $\mathrm{ev}_V$ is an isomorphism.

**Proof.** A subgroup fixing $v$ fixes evaluation at $v$ by the inverse-action formula applied twice. Smoothness of $V$ therefore makes every evaluation smooth, and the same formula makes the map equivariant. For $v\ne0$, choose a compact open subgroup $K$ in its open stabilizer. Extend any linear form on $V^K$ nonzero on $v$ by the previous theorem. This gives injectivity. Smoothness of $V^\vee$ follows from its definition, and the fixed-space isomorphism gives the required finite dimensions for admissibility.

For surjectivity take an arbitrary $\Lambda\in(V^\vee)^\vee$. Choose a compact open $K$ in its stabilizer. Restrict $\Lambda$ to $(V^\vee)^K$ and transport along $r_K^{-1}$ to a linear form on $(V^K)^*$. Finite-dimensionality of $V^K$ now gives a vector $v\in V^K$ whose evaluation is that form. Thus $\Lambda$ and $\mathrm{ev}_V(v)$ agree on $(V^\vee)^K$. Both are $K$-invariant forms on the smooth representation $V^\vee$. The compact-subgroup uniqueness statement for invariant forms extends this equality to all of $V^\vee$. The choice of $K$ is made for each $\Lambda$ separately. No bound on the overall dimension of $V$ occurs.

**Corollary (irreducibility and recovery of isomorphisms) [Lean, read].** Under the same group hypothesis, if $V$ is admissible and irreducible then $V^\vee$ is irreducible. For two admissible representations $V,W$, any equivariant isomorphism of their smooth duals gives an equivariant isomorphism of $V,W$.

**Proof.** A nonzero $V$ has a nonzero smooth dual by separation. For a nonzero stable subspace $L\subset V^\vee$, let $A$ be its annihilator in $V$. The inverse-action formula shows $A$ is stable. It is proper because a nonzero $\ell\in L$ is nonzero at some vector. Hence $A=0$. Fix any $\ell\in V^\vee$ and choose a compact open subgroup $K$ fixing it. If the image $r_K(L^K)$ were proper in $(V^K)^*$, a nonzero linear functional on the quotient would pull back to a nonzero linear form on $(V^K)^*$ vanishing on this image. By finite-dimensional evaluation it would be evaluation at some nonzero $v\in V^K$. For every $u\in L$, evaluating at $v$ is constant along the $K$-orbit of $u$. The average in $L$ lies in $L^K$ and has the same value on $v$, so $u(v)=0$. This contradicts $A=0$. Thus $r_K(L^K)$ fills $(V^K)^*$, and injectivity of $r_K$ puts $\ell$ in $L$.

Finally precomposition with an intertwiner $V\to W$ maps smooth forms on $W$ to smooth forms on $V$: the stabilizer of the form is contained in the stabilizer of its pullback. Precomposition with an inverse gives the inverse for an isomorphism. Dualize the given isomorphism (or its inverse to get the desired direction) and use evaluation at both ends. This proves the three conclusions bundled in the archive's Statement, with admissibility required of both representations in its isomorphism clause.

#### What the hypotheses buy

With no admissibility, let $\mathbb Q_3^\times$ act trivially on $V=\bigoplus_{i\ge1}\mathbb C e_i$. Every vector and every functional is smooth. The dual is $\mathbb C^{\mathbb N_{>0}}$. On this product take a linear functional vanishing on the finite-support sequences and taking value $1$ on the all-ones sequence. It exists by extending a form on the line of that sequence in the quotient by the finite-support subspace. It cannot be evaluation at a vector of $V$: testing on each coordinate sequence forces every coefficient of that vector to be zero. Thus restriction remains an isomorphism to $(V^K)^*$ for every compact open $K$, and evaluation fails to be onto. Finite-dimensionality is also needed for irreducibility transfer in this generality. Give the union of the upper-left block groups $\mathrm{GL}_n(\mathbb C)$ the discrete topology, with inclusions $g\mapsto\operatorname{diag}(g,1)$, and let it act on the same direct sum by those blocks. Any two nonzero vectors lie in a finite block and one can be sent to the other there, so the representation is irreducible. All algebraic forms are smooth, and the finite-support forms make a nonzero proper stable subspace of the dual. The compact open subgroup $\{1\}$ has infinite-dimensional fixed space.

With no smoothness, let $G=(\mathbb Q_3,+)$ and choose a $\mathbb Q$-linear map $b:\mathbb Q_3\to\mathbb Q$ with $b(1)=1$ by extending the vector $1$ to a $\mathbb Q$-basis. On a complex basis $e_0,e_1$ let $x$ fix $e_0$ and send $e_1$ to $e_1+b(x)e_0$. Additivity gives a linear action. Every open subgroup contains some $3^r\mathbb Z_3$ and $b(3^r)=3^r\ne0$. Hence $e_1$ has no open stabilizer. At every compact open $K$ we have $V^K=D_K=\mathbb C e_0$. The smooth dual consists precisely of forms annihilating $e_0$, and its restriction to $V^K$ is zero although $(V^K)^*$ is a line. All these fixed spaces are finite-dimensional. In particular, evaluation at the nonzero fixed vector $e_0$ is the zero functional.

In the averaging proof compactness is what makes orbit sets finite. For example the discrete noncompact open subgroup $K=G=\mathbb Z$ acting by shifts on $\bigoplus_{n\in\mathbb Z}\mathbb C e_n$ has zero fixed subspace. The functional sending every $e_n$ to $1$ is invariant and nonzero, so restriction fails to be injective. In positive characteristic, cancellation may fail even for finite $K$. Over $\mathbb F_p$ let a generator of $C_p$ fix $e_0$ and send $e_1$ to $e_1+e_0$. The action has order $p$, and $D_K=V^K=\mathbb F_p e_0$. These last examples isolate the roles of compactness and characteristic zero. Openness of $K$ is used on the extension side to ensure the extended functional is smooth. The compact-open basis is used to locate such a $K$ in a prescribed stabilizer.

#### The actual NuPair call

In the derivative-to-Jacquet assembly, $\omega$ is a smooth irreducible complex representation of $\mathrm{GL}_N(F)$ for a nonarchimedean local field $F$. The archive obtains the compact-open basis by shrinking inside the compact open group $\mathrm{GL}_N(\mathcal O_F)$. An open normal subgroup there is closed in the compact group and therefore compact. For positive $N$ the usual congruence subgroups $1+\mathfrak p^r M_N(\mathcal O_F)$, $r\ge1$, also exhibit the basis. For $N=0$ the group is trivial.

At `NuPairOfDerivativesJacquet.lean:83–97`, the actual right space is `smoothPart ω.dual`. The displayed pairing is the flipped inclusion into the algebraic dual, so $B(v,\ell)=\ell(v)$ and $B(\omega(g)v,\omega^\vee(g)\ell)=B(v,\ell)$. Line 84 calls `ZcDual.isIrreducible_contra hA ω hs hi`. That wrapper uses the compact-open basis and explicitly applies `hA` to the field, rank, space, action, smoothness and irreducibility of $\omega$. Here `hA` is the named deep theorem `Published.IrreducibleAdmissibleGL`. Line 85 uses the resulting irreducibility to get finite length of the dual. Lines 93–97 establish left separation by `exists_smooth_form_ne` with smoothness and the basis alone. At line 98 the pairing enters `pair_deriv` on the actual two representations. At line 118 the second `DerivJac` call uses $\omega^\vee$ with its smoothness and finite length and the inverse additive character. The involution on Jacquet labels uses the bidual via `dual_shift` and `Zcore.dualCl_dualCl`. If $S$ is the first derivative label and $t$ the order, the reversal takes the dual of $S^\vee\nu^{t-1-t/2}$, giving $S\nu^{1-t/2}$. Here $\nu=|\det|_F$, and the separate twist-and-reversal inputs supply inversion of the twist and reversal of the blocks. The rank-two nongeneric constituent $|\det|_F^{1/2}$ over $F=\mathbb Q_3$ gives a test in the actual NuPair domain. Its upper unipotent subgroup acts trivially, so a nontrivial Whittaker character forces the twisted quotient to vanish. Both the character line and its inverse character line are fixed by $\mathrm{GL}_2(\mathbb Z_3)$, and the functional $z\mapsto z$ takes the vector $1$ to $1$. The complementary-series assembly with the separate `DerFin` input makes the same separation and irreducibility calls in `NontrivialOfIsIrreducible.lean:71–98` and uses the label involution at line 125. The highest-order choice, mirabolic separation, Haar/conductor pairing, Jacquet finite length and Gelfand–Kazhdan reversal retain their own named supplies. The two NuPair paths call the production declarations directly. An explicit reader of the bundled Statement is `ThetaLiftGL.main` in `ThetaCorrespondenceLargeRank.lean:33–48`. There the two admissibility proofs enter the Statement in both orders, Howe uniqueness gives an isomorphism between the irreducible smooth duals, and the third conjunct returns the isomorphism between the original representations.

The classical statements are due to Bernstein and Zelevinsky. Their 1976 article gives the compact projection and its relation-space kernel in §2.4, the algebraic and smooth duals and the fixed-space identification in §§2.13–2.14, and admissible biduality and irreducibility in §2.15. The GL admissibility input corresponds to their §3.25. Their 1977 paper recalls the admissibility and duality conventions in §§1.1–1.4. Casselman's draft gives the averaging argument in §2.1, duality in Proposition 2.1.10 and irreducibility in Corollary 2.1.13. The archive specializes the coefficient field to $\mathbb C$ and states the compact-open basis explicitly. For a group with that basis, testing finite-dimensionality at compact open subgroups implies the same at every open subgroup by containment. The textbook calculation follows the archive's finite sums and actual consumers. The status is author-level local R3 for the cited declarations. The section-specific Lean replay, declaration reachability from Main and peer review remain open. [Sources and reading status](../sources/SOURCES.md#chapter-12-compact-open-fixed-spaces-and-the-smooth-contragredient)

### 12.4.6 Detecting a vector by all its twisted Jacquet images

#### Motivation

A conductor cutoff in a matrix-coefficient pairing tests one prescribed last-column character. The ordinary step at the end of a highest derivative asks a different question. If every last-column character gives zero on a particular vector, can that vector survive in the original representation? The answer is no, even when the representation has infinite dimension. The point is to pass from a relation witnessed on a different ball at each frequency to relations witnessed on one ball for a whole compact set of frequencies. Only then can a finite character sum act on the original vector. [Chapter 7’s small-box calculation](07-chains-of-theta-lifts.md#74317-separating-mirabolic-vectors-by-small-box-averages)

#### Two compact quotients over $\mathbb Q_3$

Use the character $\psi_0$ with kernel $\mathbb Z_3$ obtained by exponentiating the negative-power part of the $3$-adic expansion, modulo $\mathbb Z$. Put $\zeta=\exp(2\pi i/3)$. To see the quotients on actual vectors, use $V=C_c^\infty(F^n)$, the space of compactly supported locally constant functions, and the mirabolic action
$$
 (T(g,y)f)(z)=\psi_0(z\cdot y)f(g^{\mathsf T}z),\qquad
 (g,y)(h,x)=(gh,y+gx).
$$
The formula respects multiplication because $(g^{\mathsf T}z)\cdot x=z\cdot gx$. Each function is supported in a ball and constant on the cosets of some finer ball there. A sufficiently small congruence subgroup of $\mathrm{GL}_n(\mathbb Z_3)$ preserves those cosets and that support ball. A sufficiently small box of columns gives phase $1$ throughout the support. Together they give an open stabilizer. The full twisted quotient at $a$ is evaluation at $a$. Every relation vanishes there. If $f(a)=0$, the support of $f$ is compact and avoids $a$. At each point $z$ in it, choose $y$ with $\psi_0((z-a)\cdot y)\ne1$. Both phases are locally constant. A finite disjoint compact open partition subordinate to these neighborhoods lets us divide the part of $f$ on each cell by the constant nonzero difference $\psi_0(z\cdot y)-\psi_0(a\cdot y)$. This expresses each part as one actual relation. An indicator of a neighborhood of $a$ shows surjectivity.

**One coordinate.** Take $D=3^{-1}\mathbb Z_3$ as the frequency ball, its annihilator $K=3\mathbb Z_3$, and $L=\mathbb Z_3$ as the column ball. The frequency denominator may be $N=\mathbb Z_3$, since $N$ annihilates $L$. With frequency representatives $i/3$ and column representatives $j$, for $i,j=0,1,2$, the matrix of inverse phases is
$$
 M=\begin{pmatrix}
 1&1&1\\
 1&\zeta^2&\zeta\\
 1&\zeta&\zeta^2
 \end{pmatrix}.
$$
Its column sums are $(3,0,0)$ and the scalar product of row $i$ against the phase row for $k$ is $\sum_{j=0}^2\zeta^{(k-i)j}=3\delta_{ik}$. Let $f=1_{1/3+9\mathbb Z_3}+2\,1_{2/3+9\mathbb Z_3}$. The inverse-weighted sums of its column translates are $0$, $3\,1_{1/3+9\mathbb Z_3}$ and $6\,1_{2/3+9\mathbb Z_3}$ in frequency order. Their sum is $3f$.

The same columns and frequency classes also illustrate the danger of choosing representatives too early. All three representatives $a_i=i/3+1$ have zero full quotient on $f$. At column level $L$, the sum for $a_1$ is still $3\,1_{1/3+9\mathbb Z_3}$. More precisely, for $a=1/3+1$ the two support cells have differences from $a$ of orders $0$ and $-1$. On $L'=3^{-1}\mathbb Z_3$, the element $1/3$ has distinct phases from that of $a$ on both cells. Division by the differences gives a witness on $L'$. For $a=1/3+3$, the first difference has order $1$ and the second order $-1$. The first phase difference is trivial throughout $L'$ and becomes nontrivial at $1/9$. Their witness neighborhoods are $1/3+1+3\mathbb Z_3$ and $1/3+3+9\mathbb Z_3$. The characters agree with each center on its own witness ball. The union is compact, and the smallest common column ball on this union is $3^{-2}\mathbb Z_3$. To see minimality in either case, evaluate every generator at $z=1/3$ on the immediately smaller ball. It vanishes there while $f(1/3)=1$. Both frequencies kill the same vector in the full quotient. The actual frequency $1/3$ detects it, so the hypothesis of vanishing at **every** frequency is false in this example.

**Two coordinates.** Use $D=(3^{-1}\mathbb Z_3)^2$, $K=(3\mathbb Z_3)^2$, $L=\mathbb Z_3^2$, and $N=\mathbb Z_3^2$. Order pairs lexicographically from $(0,0)$ to $(2,2)$. For $a=(i,k)/3$ and $x=(j,\ell)$ the inverse entry is $\zeta^{-ij-k\ell}$. Thus the full nine-by-nine matrix, in three-by-three blocks, is
$$
 \begin{pmatrix}
 M&M&M\\
 M&\zeta^2 M&\zeta M\\
 M&\zeta M&\zeta^2 M
 \end{pmatrix}.
$$
The row tests factor in both coordinates by the one-coordinate scalar product. The column sums factor as $(\sum_i\zeta^{-ij})(\sum_k\zeta^{-k\ell})$, giving $9$ at $(j,\ell)=(0,0)$ and zero on the other eight columns. For $f=1_{(1/3,0)+\mathbb Z_3^2}+2\,1_{(0,2/3)+\mathbb Z_3^2}$ the two row tests at $(i,k)=(1,0),(0,2)$ give nine times the respective weighted support indicators. The other seven give zero, so the total is $9f$. On the entire compact frequency coset $(1,1)/3+\mathbb Z_3^2$, the column ball $L$ itself gives a common relation witness. The column $e_2$ separates the first support cell from this test coset by the phase difference $1-\zeta$, and $e_1$ separates the second by the same difference. Divide the respective weighted indicators by $1-\zeta$ and use these two columns. On $K$ the phase of every testing row in this coset and the phases of both support centers are all $1$, so evaluation at a support center rules out a witness at that smaller ball. This is a common level for a specified compact family of vanishing tests on the same nonzero vector.

At $n=0$ the last-column group and the frequency space each consist of one element. The quotient matrix is $[1]$ and the sole relation space is zero. A nonzero vector already survives in the ordinary image.

#### Definitions and detection lemma

Let $F$ be a nonarchimedean local field with integer ring $\mathcal O$ and uniformizer $\varpi$. Fix a continuous nontrivial character $\psi:F^+\to S^1$. For $n\ge0$, write $P_{n+1}$ for the subgroup of $\mathrm{GL}_{n+1}(F)$ with last row $(0,\ldots,0,1)$, and $u(x)$ for the last-column unipotent with column $x\in F^n$. The archive writes $\mathrm{Mir}(F,n)$ for $P_{n+1}$. For any smooth complex representation $T$ of $P_{n+1}$ on a vector space $V$, set $\rho(x)=T(u(x))$. For a column subgroup $H$ and a row $a\in F^n$, put $\chi_a(x)=\psi(a\cdot x)$ and
$$
 R_a(H)=\operatorname{span}_{\mathbb C}
 \{\rho(x)w-\chi_a(x)w:x\in H,\ w\in V\}.
$$
The source calls this subspace `twKer` and uses the algebraic quotient by it. We use $B_j=(\varpi^j\mathcal O)^n$ with $j\in\mathbb Z$, so increasing $j$ shrinks the ball.

**Lemma (joint detection) [Lean, read].** Fix $v\in V$. If its image in $V/R_a(F^n)$ is zero for every $a\in F^n$, then $v=0$. In particular the product of the quotient maps is injective. More precisely, given any compact frequency ball $D$, the hypothesis produces one column ball $L$ with $v\in R_a(L)$ for every $a\in D$.

#### Proof

**Localize the relation in the original carrier.** The last-column map is a continuous group isomorphism onto the last-column subgroup, so $\rho$ is smooth and the displayed relations are precisely the transported mirabolic relations. Membership in the span at a fixed $a$ is a finite linear combination. Put every column occurring in it in a single ball $B_{j(a)}$ by exhaustion. Every larger ball still admits the same expression. This is the pointwise statement $\forall a\,\exists j(a)$.

**Choose a compact frequency domain.** Smoothness of this $v$ gives a column ball $B_b$ contained in its stabilizer. For a frequency subgroup $D$, put $D^\perp=\{x:\chi_a(x)=1\text{ for all }a\in D\}$. Choose $y\in F$ with $\psi(y)\ne1$ and set $D=(y\varpi^{-b}\mathcal O)^n$. If some coordinate of $x$ is outside $\varpi^b\mathcal O$, the row supported in that coordinate with entry $y/x_i$ belongs to $D$ and has value $\psi(y)$ on $x$. Consequently $K=D^\perp\subseteq B_b$. This is the point in the source that uses nontriviality. The case $n=0$ is included.

Continuity gives a ball $\varpi^{c_0}\mathcal O$ on which $\psi=1$. Indeed continuity puts a small additive ball into the open right semicircle, and closure under integer multiples keeps all powers there. A nonidentity point of the circle has a positive power outside that semicircle, by taking the first multiple of its absolute argument reaching $\pi/2$. This trivial ball also shows that $K$ is open. If $D=B_d$, then $B_{c_0-d}\subseteq K$ by multiplying coordinates and adding. If $c$ is the exact conductor exponent, then $K=B_{c-d}$. Each coordinate product lands in the conductor ball for $x\in B_{c-d}$. For any coordinate outside that bound, $x_i\varpi^d\mathcal O$ is a strictly larger ball, and one of its elements has nontrivial character. The production here uses the inclusion obtained from $y$ and the existence of $c_0$.

**Make the level common on $D$.** At a row $a$ the single pointwise witness works unchanged for every $a'$ in
$$
 a+B_{c_0-j(a)} .
$$
Indeed, $(a'-a)\cdot x\in\varpi^{c_0}\mathcal O$ for all $x\in B_{j(a)}$, so the two characters agree on the entire subgroup and define the same relation space there. These open neighborhoods cover $D$. Compactness gives finitely many centers $a_1,\dots,a_h$. Take $J=\min_i j(a_i)$ and $L=B_J$. For each $a'$ in $D$, use a center whose neighborhood contains it, then enlarge that center's column ball to $L$. Thus $\exists L\,\forall a'\in D$ holds for exactly the same vector. The same proof works for any specified compact frequency ball, and even when the pointwise hypothesis is given only on that compact domain. It uses the pointwise equalities on the witness balls before increasing their radii.

**Produce the two finite quotients.** Write $D=B_d$ and set $N=B_{\max(d,c_0-J)}$. Then $N\subseteq D$ and $\chi_a(x)=1$ for $a\in N$, $x\in L$. The frequency quotient $D/N$ is finite since $D$ is compact and $N$ is open. Choose a full set $R$ of representatives, including a representative of the zero class, and put $S=L\cap K$. The source takes this intersection as a subgroup of $L$. Since $S$ is open in compact $L$, $L/S$ is finite too. Every $\chi_a$ with $a\in R$ descends on $L/S$, and $S$ fixes $v$. The inverse phase sum indexed by $R$ is $|R|$ on $S$. For $x\in L\setminus S$, some $b\in D$ has $\chi_b(x)\ne1$ by the definition of $K$. The function $a\mapsto\chi_a(x)^{-1}$ descends on $D/N$. Translating its sum by $b$ multiplies it by $\chi_b(x)^{-1}$ and leaves the sum unchanged. The sum is therefore zero at $x$. This works even if some distinct classes in $D/N$ give the same character on $L$.

**Use the relation-to-sum interface.** The small-box averaging result in §7.4.3.17 applies to the actual span $R_a(L)$. Refine $S$ by the finite-index subgroup supplied for the relation witness at $a$. Since $S$ fixes $v$ and lies in the character kernel, the fine sum is $[S:H]$ times the sum on $L/S$, where $H$ is the common refinement. The fine sum is zero by the averaging result. Dividing by the positive index gives
$$
 \sum_{x\in L/S}\chi_a(x)^{-1}\rho(x)v=0\qquad(a\in R).
$$
Summing the displayed equalities over $R$ and interchanging the two finite sums leaves exactly $|R|v$ at the identity coset. The frequency quotient is nonempty and $\mathbb C$ has characteristic zero, so $v=0$. $\square$

#### Where the original vector enters

| Source call | What is put in the relation space | What the call supplies |
|---|---|---|
| `ExistsNontrivialDerivative.lean:80–92` | A fixed nonzero $v$ is in the ordinary kernel. Assuming all Levi translates lie in the distinguished twisted kernel gives all rows by completing each nonzero row to the last row of an invertible matrix. | Line 85 calls the **Chapter 7** separation production. It gives a surviving Levi translate. Lines 87–92 use the smooth first twisted quotient, induction and the one-step quotient comparison to obtain a nonzero grouped derivative. |
| `InvariantPairingMirabolicVanishing.lean:59–71` | For fixed $u,v$, use $w=T(u)v-v$. For row zero it is itself a relation. For every other row, conjugation transports its kernel to the distinguished kernel, which is the whole space because the distinguished twisted quotient is zero. | Line 71 calls this section’s `MirFourier.fourier` on $w$, giving $T(u)v=v$. |
| `InvariantPairingMirabolicVanishing.lean:134–154` | The left last-column action is now trivial. Pairing covariance at a unipotent, of determinant $1$, gives invariance under the right action in that slot. | The pairing descends through the two ordinary relation spaces, keeps its determinant exponent and retains left separation. |

For the first call, if $g$ has last row $a$, apply $T(\ell(g)^{-1})$ to a distinguished relation at column $gx$. Its scalar is $\psi((gx)_n)=\chi_a(x)$. This is why the all-row test concerns the original $v$. The second call has a zero **representation** as its distinguished twisted quotient and applies the theorem to each difference $T(u)v-v$. It explains the ordinary final step after the twisted conductor pairing. That earlier construction uses a single-ball Fourier indicator, Haar cutoff and finite shear orbit in the scope of one twisted step. In `IsSmoothIterPhi.lean:139–144` the base of `pair_iter` uses this ordinary descent, and each earlier twisted step adds one to the determinant exponent. The invariant starting form in `pair_deriv` has exponent zero, so $j$ twisted steps leave exponent $j$ at the ordinary step. Smooth biduality is a separate input to NuPair. [Compact-open smooth duality](#1245-compact-open-fixed-spaces-and-the-smooth-contragredient)

#### Hypothesis tests and attribution

For $n>0$, deleting nontriviality makes every test ordinary. In the same smooth function model over $\mathbb Q_3$ retain the action defined with $\psi_0$ and use the trivial character for the tests. The indicator of $e_1+3\mathbb Z_3^n$ is nonzero and is killed by every test. In fact the column $e_1/3$ acts on it by $\zeta$, so dividing it by $\zeta-1$ gives a single ordinary relation. The scalar test outside the annihilator in the proof cannot be obtained from a trivial character.

For smoothness use the algebraic group algebra $\mathbb C[F^n]$ for $F=\mathbb Q_3$ and $n>0$, with basis $[x]$, and let $E$ be its field of fractions. The group algebra is a domain because any two finite supports lie in a finitely generated torsion-free abelian subgroup, whose group algebra is Laurent polynomial. Let $u(y)$ act by multiplication by $[y]$ and let $g$ act by the field automorphism $[x]\mapsto[gx]$. The actions satisfy the mirabolic semidirect product law. For any nonzero $y$ and any row $a$, multiplication by $[y]-\chi_a(y)[0]$ is invertible in $E$. The vector $1$ is in every relation space, witnessed at any column ball containing such a $y$, and has trivial column stabilizer. Thus even common **relation** balls may exist after deleting smoothness. The fixing annihilator and the smooth relation-to-sum passage need smoothness.

Bernstein and Zelevinsky’s 1976 paper parametrizes the characters using a fixed nontrivial additive character in §5.3 and describes the two Levi orbits in §5.4. Their §§5.9–5.10 apply to smooth complex representations, identify the original space with compactly supported sheaf sections on the additive dual, and identify each twisted relation subspace with the sections vanishing at the corresponding stalk. A section with every germ zero is zero. This gives the same detection theorem with its whole family of quotient maps. Proposition 5.12(e) gives the last-column triviality used in the second row of the table. The 1977 derivative and pairing conventions are in §§3.2, 3.5 and 3.7–3.8. The present account explains the A2 route through a compact cover, a finite frequency quotient and a finite column quotient. Its local R3 status records proof-body reading and the two source consumers at the stated spans. Lean kernel replay, declaration-level reachability from Main and independent review of this reading remain to be checked. [Bernstein–Zelevinsky 1976, pp. 44–48](https://www.uni-muenster.de/imperia/md/content/theoretische_mathematik/topologie/bernstein-zelevinsky.pdf) · [Bernstein–Zelevinsky I, pp. 450–453](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0.pdf) · [Pinned source map](../sources/SOURCES.md#chapter-12-joint-twisted-jacquet-detection)

### 12.4.7 Integral matrices and the compact-open congruence basis

In the [smooth contragredient argument](#1245-compact-open-fixed-spaces-and-the-smooth-contragredient), an open stabilizer must contain a compact open subgroup before we can average a vector over it. For $\mathrm{GL}_n$ over a nonarchimedean local field, lattice-preserving matrices supply the compact group, and congruences of increasing depth make its subgroups as small as needed.

For instance, $\operatorname{diag}(3,1)$ is a matrix over $\mathbb Z_3$ and is invertible over $\mathbb Q_3$. It sends the standard lattice into itself, with first coordinate in $3\mathbb Z_3$. Its inverse has first diagonal entry $1/3$. In contrast, $I_2+3E_{12}$ preserves the lattice in both directions, with inverse $I_2-3E_{12}$. This distinction is also topological. The integral matrices invertible over $\mathbb Q_3$ contain $\operatorname{diag}(3^j,1)$ for every $j\ge1$. Their images in $M_2(\mathbb Q_3)$ converge to the singular matrix $\operatorname{diag}(0,1)$. A compact subset would have closed image in the Hausdorff matrix space.

#### The integral subgroup

Let $F$ be a complete field with a nontrivial discrete valuation $v:F^\times\to\mathbb Z$ of image $\mathbb Z$, equipped with the valuation topology, and set $v(0)=+\infty$. Let $\mathcal O=\{x:v(x)\ge0\}$, choose a uniformizer $\varpi$ with $v(\varpi)=1$, and let $k=\mathcal O/\varpi\mathcal O$ be finite of order $q$. We use the compact open unit ball from Chapter 2. For $\mathbb Q_p$ we use the field and valuation constructed in Chapter 15. The Lean source uses the class `IsNonarchimedeanLocalField`, which assumes a compatible valuation topology, local compactness and a nontrivial valuation. [§2.3.5.1](02-functional-equations-and-primitive-characters.md#2351-finite-residue-fields-and-compact-unit-balls) · [§15.4.3.12](15-two-proofs-side-by-side.md#154312-completing-the-rationals-at-a-prime)

Write $G=\mathrm{GL}_n(F)$, $C=M_n(\mathcal O)$ inside $M_n(F)$ and $K=\mathrm{GL}_n(\mathcal O)$ for the image of the integral matrix units in $G$. Equivalently $K$ is the stabilizer of $\mathcal O^n$: asking for the images of the standard basis columns to be integral gives inclusion of lattices, and applying the same test to the inverse gives equality. The archive calls the image `GlobalTheory.SplitWeil.KO`.

**Lemma (integral matrix units) [Lean, read].** The map $A\mapsto(A,A^{-1})$ identifies $G$ with a closed subspace of $M_n(F)\times M_n(F)$, and the map $A\mapsto A$ identifies its topology with the subspace topology of the invertible matrices. The subgroup $K$ consists exactly of $A$ with both $A,A^{-1}\in C$. Equivalently, $A\in C$ and $\det A\in\mathcal O^\times$. In particular $K$ is compact and open.

**Proof.** In the archive the topology on units is induced by the embedding into the product. The second factor is written as the opposite monoid, to make the pair map multiplicative. Passing from the opposite monoid to its underlying matrix space is a homeomorphism. The image is
$$
 \{(A,B):AB=I_n,\ BA=I_n\}.
$$
Finite matrix multiplication is continuous in each entry of the output as a polynomial in all input entries. The two product equations are inverse images of a closed singleton, so the image is closed. On invertible matrices the formula $A^{-1}=(\det A)^{-1}\operatorname{adj}(A)$ gives continuity of the second coordinate as a function of the first. The determinant and adjugate are polynomial and scalar inversion is continuous at each nonzero scalar. Thus the matrix projection and the graph map are inverse homeomorphisms between the two presentations of $G$. This is the extra topology check made by `isEmbedding_val_GL`. [Pinned Units and matrix topology](../sources/SOURCES.md#chapter-12-integral-general-linear-compact-open-subgroups)

If $A$ comes from an integral matrix unit, its matrix and inverse have integral entries. Conversely, retype the two matrices as matrices over $\mathcal O$. The two products there are identities, since the entrywise map into $F$ is injective. They therefore give a unit over $\mathcal O$. For the determinant formulation, two integral inverses have integral determinants with product $1$. If $A$ is integral and its determinant is a unit, the adjugate formula gives an integral inverse. The determinant reformulation is the adjugate argument [Expository] and uses integrality of the entries.

The entries of $C$ range independently over the compact open $\mathcal O$. Thus $C$ is compact by the product theorem and is open by a finite intersection of coordinate conditions. Under the pair embedding, $K$ corresponds to the closed image intersected with $C\times C$, so it is compact. It is open as the inverse image of the open product under the same embedding. The A2 proofs `isOpen_KO` and `isCompact_KO` use these two inverse-image arguments. [Pinned archive declarations](../sources/SOURCES.md#chapter-12-integral-general-linear-compact-open-subgroups)

#### Principal congruences and reduction

**Proposition [Expository].** Suppose $n\ge1$ and $r\ge1$, and write $R_r=\mathcal O/\varpi^r\mathcal O$. Then
$$
 K(r)=I_n+\varpi^r M_n(\mathcal O)=\ker\bigl(K\longrightarrow\mathrm{GL}_n(R_r)\bigr).
$$
These are compact open subgroups, normal in $K$. They decrease with $r$, intersect in $\{I_n\}$ and form an identity neighbourhood basis in $G$. Reduction is surjective and the index is
$$
 [K:K(r)]=|\mathrm{GL}_n(R_r)|=q^{n^2(r-1)}\prod_{j=0}^{n-1}(q^n-q^j).
$$

**Proof.** The reduction of a matrix $I_n+\varpi^r X$ modulo $\varpi$ is $I_n$. Its determinant is a unit of $\mathcal O$, so it lies in $K$. Entrywise reduction modulo $\varpi^r$ then gives the indicated kernel in both directions. The set $I_n+\varpi^r C$ is compact and open in the matrix space by translation and scaling. Via the matrix projection it is compact and open in $G$. The ideals $\varpi^r\mathcal O$ are a basis at zero in $F$. A basic matrix neighbourhood of $I_n$ prescribes finitely many entry neighbourhoods. Taking the largest of the finitely many required depths produces a single $K(r)$ inside it. Each nonzero matrix entry has finite valuation, so a matrix congruent to $I_n$ at every depth equals $I_n$.

For surjectivity lift the entries of any invertible matrix over $R_r$ to $\mathcal O$. Its reduction over $k$ is still invertible, since reduction sends its given inverse to an inverse. The lift has determinant outside $\varpi\mathcal O$ and thus belongs to $K$. Over $k$ an invertible matrix is an ordered basis in columns. After $j$ independent columns their span has $q^j$ vectors, so the next column has $q^n-q^j$ choices. For each $i\ge1$, multiplication by $\varpi^i$ identifies the additive group $k$ with $\varpi^i\mathcal O/\varpi^{i+1}\mathcal O$. The map is surjective by the definition of the ideal and injective by cancellation of $\varpi^i$ in the domain. Each entry of a matrix modulo $\varpi^i$ therefore has $q$ lifts modulo $\varpi^{i+1}$. Every lift of an invertible matrix is invertible because its determinant is nonzero modulo $\varpi$. In $R_{i+1}$ an element with nonzero first residue is a unit, as it is the image of a unit of $\mathcal O$. Thus each invertible matrix lifts in exactly $q^{n^2}$ ways per step. Multiplying the counts from $i=1$ to $r-1$ and using the reduction kernel proves the index.

**Rank and depth zero.** For $n=0$ the empty matrix has determinant $1$ and the whole matrix group and every congruence quotient have one element. At depth $r=0$ we set $K(0)=K$, with index one. This is the kernel of the map to the one-element group of matrices over the zero ring if that convention is used. The expression $I_n+M_n(\mathcal O)$ at rank $n\ge1$ gives the entire matrix space over $\mathcal O$, so the affine formula applies only from depth one.

#### Two calculations

**Over $\mathbb Q_3$.** Here $\varpi=3$, $k=\mathbb F_3$, and $R_1=\mathbb Z/3$, $R_2=\mathbb Z/9$. A first column over $\mathbb F_3$ has eight nonzero choices. Its span contains three vectors and the second column has six choices outside them. Thus the first quotient has order $48$. In $R_2$, each residue matrix of the first quotient has $3^4=81$ lifts with entries $a_{ij}+3x_{ij}$ for $0\le a_{ij},x_{ij}\le2$. Each determinant stays nonzero modulo $3$. The second quotient has order $48\cdot81=3888$ and $[K(1):K(2)]=81$. For example
$$
 A=\begin{pmatrix}4&3\\0&1\end{pmatrix},\qquad
 A^{-1}=\begin{pmatrix}1/4&-3/4\\0&1\end{pmatrix}.
$$
The determinant is $4\in\mathbb Z_3^\times$. The reductions of $A$ are $I_2$ at depth one and $\left(\begin{smallmatrix}4&3\\0&1\end{smallmatrix}\right)$ at depth two. The inverse at depth two is $\left(\begin{smallmatrix}7&6\\0&1\end{smallmatrix}\right)$, since $4\cdot7=28$ and $4\cdot6+3=27$. So $A\in K(1)\setminus K(2)$. The matrix $I_2+9E_{21}$ is in $K(2)$, with inverse $I_2-9E_{21}$. If a left Haar measure $\mu$ gives $K$ mass $b>0$, the two subgroup masses are $b/48$ and $b/3888$ by equal coset masses.

**Over $\mathbb Q_2(\sqrt 2)$.** Put $\varpi=\sqrt2$ and extend the convention $v_2(0)=+\infty$. The polynomial $X^2-2$ has no root in $\mathbb Q_2$ because a square has even valuation. For $a,b\in\mathbb Q_2$, the norm of $a+b\varpi$ is $a^2-2b^2$. Its two nonzero terms have distinct parity of valuation, so
$$
 v(a+b\varpi)=v_2(a^2-2b^2)=\min(2v_2(a),\,1+2v_2(b)).
$$
Norm multiplicativity gives the product law. The minimum formula gives the ultrametric inequality using that of $v_2$, and identifies the field topology with the product topology on the two coefficients. Completeness follows by taking limits of the two Cauchy coordinate sequences in $\mathbb Q_2$. Thus $\mathcal O=\mathbb Z_2+\mathbb Z_2\varpi$. The map $a+b\varpi\mapsto a\bmod2$ has kernel $2\mathbb Z_2+\varpi\mathbb Z_2=\varpi\mathcal O$, so $q=2$. Here $v(2)=2$, and
$$
 R_1=\mathbb F_2,\qquad R_2=\mathbb F_2[\epsilon]/(\epsilon^2),\qquad \epsilon=\varpi\bmod\varpi^2.
$$
Indeed modulo $\varpi^2=2$ the two coefficients are independent modulo $2$ and $\epsilon^2=0$. For $n=2$ the first quotient has $(4-1)(4-2)=6$ elements. Every residue matrix has $2^4=16$ lifts at depth two, obtained by adding $\epsilon X$ with $X\in M_2(\mathbb F_2)$. Thus the second quotient has order $96$ and $[K(1):K(2)]=16$. For example
$$
 B=\begin{pmatrix}1+\varpi&\varpi\\0&1\end{pmatrix},\qquad
 B^{-1}=\begin{pmatrix}\varpi-1&\varpi-2\\0&1\end{pmatrix}.
$$
Here $(1+\varpi)(\varpi-1)=1$ and the upper-right entry of the product is $(1+\varpi)(\varpi-2)+\varpi=0$. At depth one $B$ is the identity and at depth two it is $I_2+\epsilon X$ with $X=\left(\begin{smallmatrix}1&1\\0&0\end{smallmatrix}\right)$. This class is nonidentity and is its own inverse since the quotient ring has characteristic two and $\epsilon^2=0$. The matrix $I_2+2E_{21}$ is in $K(2)$ with inverse $I_2-2E_{21}$. Group Haar masses at depths one and two are $b/6$ and $b/96$ when $\mu(K)=b$. The distinction between $2$ and $\varpi$ is essential for identifying the first layer.

#### Smooth vectors and the limits of the argument

If $V$ is a complex representation of $G$, then $V$ is smooth exactly when $V=\bigcup_{r\ge1} V^{K(r)}$. In one direction put a congruence subgroup inside the open stabilizer of each vector. In the other, a subgroup containing an open subgroup is open, by its coset decomposition. One depth fixes any prescribed finite collection of smooth vectors, by taking the maximum of their depths. The same stabilizer criterion applies to smooth forms in the algebraic dual with its inverse action. Finiteness of the fixed spaces for these congruence groups is equivalent to admissibility for a smooth $V$, since for any compact open $H$ one can choose $K(r)\subseteq H$ and then $V^H\subseteq V^{K(r)}$. The quotient order of $K/K(r)$ supplies no dimension bound for an arbitrary representation. For instance every vector of an infinite direct sum of trivial complex representations is fixed at every depth.

In the archive, `SmGL.exists_open_normalised_subgroup_subset` uses the matrix embedding and the compact open $K$ to find an open normal subgroup of $K$ in a prescribed identity neighbourhood. `SqIntUnit.compactOpen_basis` and `ThetaLiftGL.compactOpen_basis` make this subgroup compact by closedness inside $K$. The displayed $K(r)$ give concrete witnesses to the same basis property. At depth one the archive also defines the kernel as `KOne`, and `redK_surjective` proves surjectivity by lifting the entries and testing the determinant. The table records how the archive uses the property. [Pinned consumer map](../sources/SOURCES.md#chapter-12-integral-general-linear-compact-open-subgroups)

| Consumer | Use of the basis | Other inputs |
|---|---|---|
| Smooth contragredient, `ContraRefl.exists_smooth_form_ne` | Put a compact open subgroup inside the stabilizer of a nonzero vector and extend a separating fixed-space form | Smoothness for separation, and admissibility for the bidual and irreducibility clauses of §12.4.5 |
| `BZNuPairAsm.nuPair` | `ThetaLiftGL.compactOpen_basis` supplies smooth separation for the evaluation form fed into `pair_deriv`. `ZcDual.isIrreducible_contra` uses `SqIntUnit.compactOpen_basis` | The named irreducible-admissibility input, derivative/Jacquet inputs and character, and the top-order vanishing used by the pairing |
| `ThetaLiftGL.main` | Gives the compact-open basis to the smooth-duality theorem in both orders before using Howe uniqueness | The two admissibility inputs come from Bernstein–Zelevinsky finiteness, with unitary product irreducibility and Howe duality supplied separately |

The mass for averaging on a compact open subgroup $H$ is divided by $\mu(H)$ for any positive group Haar normalization. In particular $\mu(K(r))=\mu(K)/[K:K(r)]$, by the disjoint left coset partition. The additive Haar measure $\lambda$ of the conductor calculation is a separate choice. With $a_0=\lambda(\mathcal O)>0$, $L_t=(t\mathcal O)^m$ and $D_t=(ct^{-1}\mathcal O)^m$, use the normalized local absolute value $|\varpi|=q^{-1}$. To see how the mass scales, partition $\varpi^i\mathcal O$ into the $q$ additive cosets of $\varpi^{i+1}\mathcal O$ for each integer $i$. These cosets have equal mass. Thus the two box masses are $a_0^m|t|^m$ and $a_0^m|c/t|^m$. Their product is $a_0^{2m}|c|^m=a_0^m\lambda^m(L_c)$. For $F=\mathbb Q_3$, $m=2$, $c=1$, $t=1/3$, and $a_0=2$, the masses are $36$ and $4/9$, giving $16$. The compact-open group basis fixes smooth vectors for the pairing argument, and the conductor balls supply the separate additive integrals. [Local Haar conventions](15-two-proofs-side-by-side.md#154311-haar-measure-on-p-adic-balls-and-shells)

**Deleting finite residue.** Let $F=\mathbb Q((t))$ with the $t$-adic topology, uniformizer $t$, and $\mathcal O=\mathbb Q[[t]]$. This field is complete: the tails of a Cauchy sequence have a common lower exponent bound and each coefficient eventually stabilizes, defining its limit. The residue field $\mathbb Q$ is discrete and infinite. For $n\ge1$ the continuous reduction on $K$ has infinite image, since $\operatorname{diag}(a,1,\ldots,1)$ for $a\in\mathbb Q^\times$ have distinct residues. Hence $K$ is open and fails to be compact. Each $K(r)$ for $r\ge1$ also fails compactness, since the continuous map $A\mapsto (A-I_n)/t^r\bmod t$ onto the discrete infinite set $M_n(\mathbb Q)$ is surjective. The entrywise neighbourhood argument and the reduction kernel and surjectivity still hold. A subgroup neighbourhood contains some $K(r)$, and each such $K(r)$ is a closed subgroup of $G$ by openness and the complementary cosets. Thus there is no compact open subgroup at positive rank in this example.

Bernstein and Zelevinsky specify $\mathrm{GL}_n(\mathcal O)$ and its compact-open congruence basis in §3.1 of their 1976 paper, for a locally compact nondiscrete nonarchimedean field and a generator of its maximal ideal. Their §2.1 uses open stabilizers, and Casselman's draft §2.1 gives the same definition for groups with the basis hypothesis. The finite-field order is also formalized separately in Mathlib as `Matrix.card_GL_field`. Klopsch’s §8.1 gives the same congruence kernels and indices over $\mathbb Z_p$. The proof above uses the successive quotients of the uniformizer over general $\mathcal O$. The local R3 reading covers the stated A2 bodies and direct topological suppliers. [Bernstein–Zelevinsky 1976, §§2.1 and 3.1](https://www.uni-muenster.de/imperia/md/content/theoretische_mathematik/topologie/bernstein-zelevinsky.pdf) · [Casselman, draft, pp. 18–19](https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf) · [Klopsch, §8.1, p. 32](https://www.math.uni-duesseldorf.de/~klopsch/mathematics/Manuskripte/analytic_groups.pdf) · [Reading and verification scope](../sources/SOURCES.md#chapter-12-integral-general-linear-compact-open-subgroups)

### 12.4.8 Why ordered segment quotients exhaust the irreducible representations

**Motivation.** The extension in [§12.4.1](#1241-multisegment-assembly-of-partial-local-langlands-srcdevelopmentautomorphicarithmeticfoundationslocallanglandslocalcentralunitsrectexistslean) needs a multisegment for each input representation before it can apply the segment formula. Cuspidal support gives a multiset of supercuspidal representations. Exhaustion must do more: it must group those representations into segments and exhibit the given irreducible representation as the cosocle of an ordered product of segment quotients. The passage from an embedding to that quotient is the last step of the archive's induction.

**Example.** In $\mathrm{GL}_2(k)$ take the two smooth characters $\alpha=\xi\nu^{-1/2}$ and $\beta=\xi\nu^{1/2}$ of the diagonal blocks. Here $\nu$ is the normalized absolute value on $k^\times$, with value $q^{-1}$ on a uniformizer. In normalized upper Borel induction the inducing character is multiplied by the half modulus. For a diagonal pair $(a,d)$ that multiplier is $\nu(a)^{1/2}\nu(d)^{-1/2}$.

In the order $\alpha,\beta$ the resulting transformation character is $\xi(ad)$. Hence the function $g\mapsto\xi(\det g)$ spans a subrepresentation. After removing the determinant twist, the quotient is the smooth Steinberg representation, defined as locally constant functions on the Borel quotient modulo constants. The two orders give these exact sequences.

- $0\to \xi\circ\det\to\alpha\times\beta\to \mathrm{St}_2\otimes(\xi\circ\det)\to0$.
- $0\to \mathrm{St}_2\otimes(\xi\circ\det)\to\beta\times\alpha\to \xi\circ\det\to0$.

The decreasing-order sequence follows by applying smooth contragredients to the increasing-order sequence for $\xi^{-1}$. In this convention contragredients dualize the inducing characters in place, and $\mathrm{St}_2$ is self-dual. The irreducibility and the unique submodule and quotient in this example follow from the adjacent-twist case of §§1.11, 3.1–3.2 and 9.1–9.4. Thus the single segment $[\alpha,\beta]$ yields the Steinberg twist as its segment quotient. The two singleton segments must be ordered $[\beta],[\alpha]$ and their standard module has quotient $\xi\circ\det$. The common determinant twist acts on both factors, with the same Borel half modulus. For instance, taking $\xi=\lvert\cdot\rvert_k^s$ shifts both exponents by $s$, preserving their unit difference. [Paper] [Zelevinsky, pp. 175, 180–181, 197–198](https://www.numdam.org/item/ASENS_1980_4_13_2_165_0.pdf).

**Remark (the seed-extension example).** The two presentations above can give the same Frobenius eigenvalues. In the rank-two parameter example over $\mathbb Q_5$ associated with the extension in [§12.4.1](#1241-multisegment-assembly-of-partial-local-langlands-srcdevelopmentautomorphicarithmeticfoundationslocallanglandslocalcentralunitsrectexistslean), take $\xi=\chi\nu^{1/2}$ with $\chi$ unramified and $\chi(5)=2$. Then the inducing characters are $\chi,\chi\nu$. A degree-one Frobenius lift maps under the archive's Artin map to an element of valuation $-1$, so the two seed values are $1/2$ and $5/2$. The Frobenius matrix is $D=\operatorname{diag}(1/2,5/2)$. The two singleton blocks have zero monodromy. The single length-two block has $N(e_1)=e_2$, $N(e_2)=0$, so $DN=5ND$ and $N^2=0$. Both have characteristic polynomial $(X-1/2)(X-5/2)=X^2-3X+5/4$ before twisting. In the archive's parameter convention the $\nu^2$ twist takes $D$ to $25D$ and keeps $N$ fixed. Both twisted parameters therefore have characteristic polynomial $(X-25/2)(X-125/2)=X^2-75X+3125/4$, with their monodromy ranks still $0$ and $1$. [Parameter conventions and source lines](../sources/SOURCES.md#chapter-12-multisegment-exhaustion-jacquet-shuffles-and-segment-production)

**Definitions.** A segment $\Delta$ of length $l>0$ begins at an irreducible supercuspidal $\rho$ of $\mathrm{GL}_d(k)$ with $d>0$ and consists of $\rho,\rho\nu,\ldots,\rho\nu^{l-1}$. Its degree, meaning the rank of the resulting general linear group, is $dl$. Two segments are *linked* if their union is a segment and neither contains the other. A linked $\Delta$ *precedes* $\Gamma$ if $\Gamma$ begins at $\Delta.\mathrm{first}\,\nu^j$ for some integer $j>0$. Write $L(\Delta)$ for a representation satisfying the archive's predicate **IsLSeg**, the irreducible cosocle of the increasing product of the terms of $\Delta$. The cosocle condition singles out the kernel as the unique maximal proper subrepresentation. Dually the socle condition singles out the image as the unique irreducible subrepresentation.

For a finite multiset $\mathfrak m$, **IsL** means that there is an enumeration $\Delta_1,\ldots,\Delta_h$ counting multiplicities, with no $\Delta_i$ preceding $\Delta_j$ when $i<j$, and that the given representation is the cosocle of $L(\Delta_1)\times\cdots\times L(\Delta_h)$. Its degree is the sum of the segment degrees. Repeated and nested segments are allowed. The empty multiset has degree zero. The exhaustion statement ranges over **every** smooth irreducible complex representation of every $\mathrm{GL}_n(k)$ in the archive, including the rank-zero convention, with no restriction on the cuspidal support. Its field assumptions are the field, valuation relation, topology, nonarchimedean local field structure and characteristic zero in the declaration. The actual segment hypothesis is uniform over local fields even before imposing characteristic zero: it gives the unique irreducible **submodule** of each increasing segment induction, with normalized Jacquet module isomorphic to the tensor of the increasing terms along the same block parabolic. These are the two substantive conclusions of **SegmentRepresentation** (uniqueness included in the first). The single-segment quotient above is the other orientation.

**Lemma (replacing a middle block).** Write $I(A)$ for the ordered normalized product of a list $A$, with the empty product in rank zero. Suppose $x$ is irreducible and embeds in $I(A)\times I(M)\times I(B)$. Then there is an irreducible subquotient $\sigma$ of $I(M)$ such that $x$ embeds in $I(A)\times\sigma\times I(B)$. If instead we are given an embedding $\sigma\hookrightarrow I(M)$, an embedding using $\sigma$ can be refined to one using $M$. An isomorphism between adjacent factors' products likewise lets us replace either product by the other inside a list. [Lean, read]

*Proof.* For fixed outside factors put $T(V)=I(A)\times(V\times I(B))$. In the middle variable the proof tensors on the right, induces, tensors on the left, and induces again. The tensor maps preserve injectivity and exactness over $\mathbb C$. The induction step uses the normalized induced maps on functions and parabolic induction's preservation of injectivity and exactness at the middle term. This establishes the exactness used by the argument, including the kernel identity for the induced quotient map.

Take a minimal subrepresentation $S\subset I(M)$ such that $x\hookrightarrow T(S)$. The existence follows from finite length of $I(M)$, supplied using admissibility, and $S\ne0$ since $T(0)=0$. Choose a maximal proper subrepresentation $U$ of $S$. The composite $x\hookrightarrow T(S)\to T(S/U)$ has kernel either zero or all of $x$. In the latter case its image lies inside the image of $T(U)$, and pulling back along the injection $T(U)\hookrightarrow T(S)$ contradicts minimality. Thus $\sigma=S/U$ works. The refinement assertion follows by applying $T$ to $\sigma\hookrightarrow I(M)$ and composing injections. The swap assertion applies the same argument to the isomorphism for the two unlinked blocks. Induction in stages identifies the nested products with their concatenated lists and checks the rank sums, so these constructions give **MidP**, **RefineP** and, with **LUnlinkedComm**, **SwapP**. The finite-length argument concerns smooth induced representations and uses their subrepresentation lattice. Their underlying vector spaces can be infinite-dimensional. See the source map below.

**Proposition (conditional exhaustion used in the archive).** Assume **SegmentRepresentation**. Over every characteristic-zero nonarchimedean local field, each irreducible $x$ of rank $n$ admits a finite multiset $\mathfrak m$ of degree $n$ with **IsL** $\mathfrak m$ $x$. [Lean, read]

*Proof.* The producer first supplies irreducibility for products of pairwise unlinked segment quotients. Its proof calls the all-parabolic Jacquet calculation for segments, the geometric lemma, the adjacent-twist criterion, the standard-product Whittaker-rank calculation and finite length of products. The unlinked irreducibility input then gives the required commutation isomorphism. Together with the middle-block lemma this supplies the three inputs to **exhaustion_of_three**.

Here are the additional inputs to its induction. An irreducible representation embeds in a product of supercuspidals (**CuspEmbP**). In the archive this follows by rank induction: the Jacquet input gives an embedding with a positive-rank supercuspidal left factor and an irreducible right factor, which is expanded by **RefineP** after applying induction. The rank-zero factor is the empty product. If $x\hookrightarrow I(l)$ for a supercuspidal list $l$, and also $x\hookrightarrow a\times y$ where $y$ satisfies **IsL**, every beginning of a segment of $y$ belongs to $l$ (**SuppP**). Indeed the two embeddings give the same cuspidal support for $x$ by uniqueness. In the second expression the support is the sum of that of $a$ and the multisets of terms of the segments of $y$. Every beginning occurs in that sum.

A nonempty finite cuspidal list has an element $\rho$ that is no positive integral twist of any element of the list (**MinP**). Starting with any $\rho_0$ in the list, take the maximal $m\ge0$ for which $\rho_0\nu^{-m}$ occurs there. These backward twists are distinct, as a nonzero integral twist changes the central character at a scalar uniformizer. A singleton $[a]$ linked to a segment $\Delta$ must adjoin one end (**LinkP**), so either $\Delta.\mathrm{first}=a\nu$ or $a=\Delta.\mathrm{first}\,\nu^{\ell(\Delta)}$. For $a$ at the upper end, an irreducible subquotient $\sigma$ of $a\times L(\Delta)$ either is $L(\Delta\cup\{a\})$ or embeds in $L(\Delta)\times a$ (**JuxtP**). The archive obtains this last dichotomy from Jacquet shuffle words and uniqueness for irreducibles embedded in the descending word of a segment. The induction uses the dichotomy supplied in [§12.4.9](#1249-jacquet-shuffles-and-the-descending-segment-word).

The archive dispatches rank zero through its rank-at-most-one lemma. For positive rank, choose $x\hookrightarrow I(l)$ by **CuspEmbP**. The rank sum forces $l$ to be nonempty. Choose a minimal $\rho$ as above and split $l=A,[\rho],B$. Start with the singleton segment beginning at $\rho$. The following loop maintains an embedding with a distinguished segment quotient $b=L(\Delta)$ preceded by a list of supercuspidals from $A$, and $\Delta.\mathrm{first}=\rho$.

- If the prefix is empty, apply **MidP** to the entire suffix, producing $x\hookrightarrow b\times y$ for an irreducible $y$.
- Otherwise take the last prefix factor $a$. If its singleton is unlinked to $\Delta$, use **SwapP** and move $a$ to the suffix.
- If linked, minimality excludes $\rho=a\nu$. Apply **MidP** to the adjacent pair $a,b$. By **JuxtP** the replacement irreducible is the longer segment quotient, still beginning at $\rho$, or it embeds in $b\times a$. In the second case **RefineP** substitutes $b,a$ for the replacement and again moves $a$ to the suffix.

Each pass shortens the prefix. Thus $x\hookrightarrow c\times y$ with $c=L(\Gamma)$ and $\Gamma.\mathrm{first}=\rho$. Now use strong induction on the rank of $x$. In rank zero the empty product is the unique irreducible representation of the trivial group. In positive rank the constructed $c$ has positive degree, so $y$ has smaller rank and admits a multisegment $\mathfrak n$. If $\Delta'\in\mathfrak n$ precedes $\Gamma$, then $\rho=\Delta'.\mathrm{first}\,\nu^j$ for some $j>0$. Since $\Delta'.\mathrm{first}\in l$ by **SuppP**, this contradicts minimality.

It remains to pass from the embedding to **IsL**. Take an ordered list $t$ of segment quotients for $y$. Appending $c$ to $t$ is allowed by the preceding paragraph. The standard cosocle supplier dualizes the ordered factors in place. The dual segments are in reverse order in the precedence sense. It uses the socle of their product, transported along the induced contragredient isomorphism, and takes smooth duals again to obtain the cosocle. For the original ordered list the standard cosocle theorem now gives an irreducible quotient $z$ of the resulting ordered product, with **IsL** for $\mathfrak n+\{\Gamma\}$. By the supplied reverse-product socle theorem, $y$ embeds in the product of $t$ in reverse order, and $z$ is the unique irreducible submodule of $c$ times that reversed product. Inducing the embedding of $y$ with $c$ and composing with $x\hookrightarrow c\times y$ puts $x$ in this same product. Uniqueness of its irreducible submodule gives $x\simeq z$, and the cosocle predicate transports across this isomorphism. This is **PeelGoodP**, and it completes the induction. $\square$

**Notes on the literature and the proof boundary.** Zelevinsky's field and complex representation conventions are in §1.1 (p. 170), and §1.11 (p. 175) specifies the standard norm in $\nu$. The archive takes the characteristic-zero subcase in its exhaustion statement. The following correspondences use the original paper's notation $\langle\Delta\rangle$ for its increasing-product submodule and $\langle\Delta\rangle^t$ for its increasing-product quotient. The application of normalized induction in stages and the support and ordering comparisons occur on both sides. The paper uses its own proof of exhaustion.

| Archive input or condition | Corresponding place in Zelevinsky (1980) |
|---|---|
| Positive rank and length, supercuspidal beginning, unique segment submodule and exact block Jacquet tensor in **SegmentRepresentation** | §1.10 (pp. 174–175) gives the cuspidal condition. §3.1 (pp. 180–181) gives the consecutive twists, the ascending submodule and its block Jacquet tensor. §9.1 (p. 197) gives the reverse orientation and the ascending quotient. |
| Irreducibility of unlinked products of the quotient blocks | §4.2 (p. 184) gives the criterion for $\langle\Delta\rangle$; §9.7 (pp. 198–199) treats unlinked products of $\langle\Delta\rangle^t$. |
| **MidP**, **RefineP**, **SwapP** | §1.1(a,c) (p. 170) gives exactness and induction in stages. In §6.7 (p. 190) a simple submodule survives in one of the two outer induced terms of a short exact sequence, the same kernel argument used in **MidP**. §6.4 (p. 189) swaps unlinked neighbors in the submodule convention using §§1.9 and 4.2. Commutativity in the Grothendieck ring alone only gives equality of composition factors. |
| **CuspEmbP**, **SuppP** | §1.10 (pp. 174–175) gives the support and the embedding with a suitable ordering. §4.4 (p. 185) computes the support of constituents of a product of segment modules. For two terms the proof also uses the same additivity of cuspidal support. |
| **JuxtP**, **LinkP** | §4.1 (p. 184) gives linked and juxtaposed segments and the precedence direction. §4.6 (pp. 185–186) gives the union/intersection constituent and the other constituent for a linked pair in the submodule convention. This is the classical comparison for the two outcomes, while the Lean quotient-block dichotomy uses its own shuffle and descending-word supplies. |
| **MinP**, **PeelGoodP** and exhaustion | §6.7 (p. 190) uses finiteness and minimizes inversions instead of selecting the minimal beginning and peeling by rank. §6.1(a,c) (p. 188) gives the same no-precedence ordering and exhaustion with a unique **submodule** for the $\langle\Delta\rangle$ blocks. For an individual quotient block, compare the reversed-submodule direction of §9.1. The archive's reverse-product socle and standard cosocle inputs supply the general change of direction used in this proof. |

Zelevinsky §9.3 identifies the quotient blocks as essentially square-integrable. The existence of a quotient presentation proved here uses the explicit no-precedence condition. A decreasing-exponent order is visible in the two-singleton example. The proof of §6.1(c) in the original uses $\langle\Delta\rangle$, and §9.7 concerns non-degenerate representations. [Paper] [Zelevinsky, original article](https://www.numdam.org/item/ASENS_1980_4_13_2_165_0.pdf).

In the archive **Outright** passes the actual theorem **PositivityTheory.RgGu.segmentRepresentation** to the conditional producer and exports **langlandsExhaustionGL_holds**. The producer's outer assembly of that segment input from the geometric lemma, the stage package and the two-term reducibility package is visible in its three-line body. The shuffle and segment-production assemblies appear in [§12.4.9](#1249-jacquet-shuffles-and-the-descending-segment-word) and [§12.4.10](#12410-producing-the-increasing-segment-from-adjacent-pairs). The imported geometric filtration, underlying Jacquet and induction exactness, Whittaker, admissibility, finite length, two-segment interactions, commutation and reverse-socle suppliers retain [Lean] status, with their deeper reading [Open]. The [Lean, read] status here applies to the conditional proofs and assembly bodies itemized in the source map.

**Source map.**

The paths below are relative to the extracted A2 archive's `lean/` directory. The joined archive SHA-256 is **9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc**. The line spans identify the declarations or proof portions used in this section. [A2 source record](../sources/SOURCES.md).

| Textbook step | Lean source and lines | Reading status |
|---|---|---|
| Exhaustion statement | LanglandsExhaustionGL · `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/LanglandsExhaustionGL.lean:10–12` | Definition |
| Actual input and its export to local Langlands | langlandsExhaustionGL_holds · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/Outright.lean:8`; Pr.exh · `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/Multi.lean:11` | [Lean, read] |
| Conditional producer | langlandsExhaustionGL_of_seg · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/LanglandsMultisegmentsOfSeg.lean:10–14` | [Lean, read] |
| The actual segment input and its statement | segmentRepresentation · `src/Development/WeilBound/RepresentationTheoryGL/GenericUnitaryGL/ComplementarySeries/SegmentJacquetSubquotients/SegmentRepresentation.lean:9–12`; SegmentRepresentation · `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/SegmentRepresentation.lean:15–22`; segTerm · `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsCellOfIsSubquotient.lean:126–128` | [Lean, read] for producer assembly. [Lean] for its imported inputs. |
| Normalized induction and the two-character example | parInd, parInd_law · `src/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean:228–239`; isL_detRep_two, segment_two_spec · `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyEquivContraOfChar.lean:447–474` | Definition and [Lean] cross-reference for the example. |
| Segment, linking, ordering and quotient conditions | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NonemptyEquivMultiProdOne.lean:435–456,537–556`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NonemptyEquivOfRangeEq.lean:90–96` | Definitions |
| Embedding and nine step interfaces | `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/CuspEmbP.lean:14–43`; PeelGoodP · `src/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/ZelevinskyJacquet/ZelevinskyExhaustion/PeelDefs.lean:35–38` | Definitions |
| Unlinked irreducibility supplier | lUnlinkedIrr_of_seg · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/LUnlinkedIrrOfSeg.lean:12–15`; LUnlinkedIrr, LUnlinkedComm · `src/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/ZelevinskyJacquet/ZelevinskyCosocles/LUnlinkedComm.lean:36–42` | [Lean, read] for the assembly. [Lean] for the imported irreducibility and commutation arguments. |
| Exactness, simple quotient of a minimal submodule and transports | extL_exact, extR_exact, ind₂Map_exact, tripleProductMap_injective · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/MidExact.lean:18–28,41–51,60–71`; mid_sub, mid_gen · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/MidGen.lean:32–42,46–148,152–170`; stage3_iso and its helpers · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/EquivTripleProductOfIso.lean:16–43`; middle-factor assembly · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/EmbeddingMiddleFactorTriple.lean:15–110` | [Lean, read] for these bodies. Imported parabolic induction exactness, finite length and two-block induction-in-stages theorems [Lean]. |
| Supercuspidal embedding and support comparison | cuspEmbP, suppP, irreducibleAdmissibleGL, cuspEmbP_of_refine · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/IrreducibleAdmissibleGL.lean:18–37,41–60,64–100` | [Lean, read] for rank induction and support calculation. Jacquet splitting, support and admissibility supplies [Lean]. |
| Adjacent linked pair | juxtP, juxtP_of_fineUniq · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/JuxtPOfFineUniq.lean:15–48` | [Lean] as used in the textbook argument. |
| Endpoints and minimal beginning | linkP, minP · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/NotAboveTransGenSelf.lean:13–36,40–96` | [Lean, read] for the interval and finite-list arguments. |
| Ordered cosocle and reverse socle | standardCosocle_of, lOrderFree_of, lSocleGL_of · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/ExhaustionOfThree.lean:30–46`; LSocleGL · `src/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/ZelevinskyJacquet/PropsCos.lean:10–13` | [Lean, read] for assembly. [Lean] for the imported duality and reverse-socle supplies. |
| Appending the segment quotient | isL_add_segment_of_injective_of_not_precedes, peelGoodP · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/IsLAddSegmentOfInjectiveOfNotPrecedes.lean:12–46,48–51` | [Lean, read] for the ordered append and socle comparison. |
| Leftward move, rank induction and assembly | move_left, exhaustion_of_steps · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/ExhaustionOfSteps.lean:13–42,44–75`; rank-zero case · `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExhUnipRadOne.lean:24–72,81–85`; exhaustion_of_three · `src/Development/WeilBound/CoreStatements/AutomorphicKernels/LanglandsExhaustion/ExhaustionOfThree.lean:49–55` | [Lean, read] for the induction and assembly. |

The two parameters passed to `exists_isLExt` in [§12.4.1](#1241-multisegment-assembly-of-partial-local-langlands-srcdevelopmentautomorphicarithmeticfoundationslocallanglandslocalcentralunitsrectexistslean) come from separate exports. `Multi.lean:11–12` binds `Pr.exh` to `Outright.langlandsExhaustionGL_holds` and `Pr.multi` to `Outright.langlandsMultisegments_holds`. Both use the same `segmentRepresentation` supplier. The latter export calls `multisegments_of` with the exhaustion theorem as an input. At `RecTExists.lean:25–28` exhaustion makes a multisegment available for each representation, and the first clause of the separate multisegment theorem makes the multiset independent of that choice. At lines 45–51 seed agreement at each cuspidal beginning lets the segment sum use the extended map. [Production calls and reading scope](../sources/SOURCES.md#chapter-12-multisegment-exhaustion-jacquet-shuffles-and-segment-production)

### 12.4.9 Jacquet shuffles and the descending segment word

#### Motivation

Take an irreducible subquotient of a segment induced with the next cuspidal twist. How can we tell whether this subquotient is the representation attached to the extended segment? The proof of `JuxtP` first embeds the subquotient into an induction from a cuspidal list. The Jacquet module then restricts where the new twist can occur in that list. If it occurs at the front, a theorem about the irreducible submodule of descending induction identifies the representation. In every other position, the proof moves the new twist to the right and recovers an embedding into the two-factor induction in reverse order.

#### Example. Inserting one letter

Let $F$ be a nonarchimedean local field, let $G_m=\mathrm{GL}_m(F)$, and write $\nu(g)=|\det g|_F$. For a character $\chi$ of $F^\times$ write $i$ for the character $\chi\nu^i$ in the tables below. Each row specifies a **position** for the new letter. A word such as $120$ denotes an ordered tensor on the diagonal Levi.

| Descending segment word | Added letter | Number of old letters before the added one | Result | Contribution |
|---|---|---|---|---|
| $10$ | $2$ | $0$ | $210$ | $1$ |
| $10$ | $2$ | $1$ | $120$ | $1$ |
| $10$ | $2$ | $2$ | $102$ | $1$ |
| $210$ | $3$ | $0$ | $3210$ | $1$ |
| $210$ | $3$ | $1$ | $2310$ | $1$ |
| $210$ | $3$ | $2$ | $2130$ | $1$ |
| $210$ | $3$ | $3$ | $2103$ | $1$ |

Repetition changes the count. Shuffling the descending word $10$ with a singleton $1$ gives $110$ twice and $101$ once. Both occurrences of $110$ use the same characters and have different assignments of the two positions labelled $1$ to the two inducing factors.

#### Definitions and inputs

Use smooth complex representations. Write $x_1\times\cdots\times x_h$ for normalized parabolic induction from the standard upper block parabolic, and $r_{(m_j)}$ for its normalized Jacquet functor, with coinvariants by the upper unipotent radical followed by the inverse half-modulus twist. The rank of a representation of $G_m$ is $m$. In this subsection cuspidal means supercuspidal.

A segment $\Delta$ with first term $\rho$ and length $\ell>0$ has ascending terms $t_i=\rho\nu^i$ for $0\le i<\ell$. Its degree is $\ell d$, where $d$ is the rank of $\rho$. Write $D(\Delta)=(t_{\ell-1},\ldots,t_0)$ for its descending word and $L(\Delta)$ for the irreducible cosocle of $t_0\times\cdots\times t_{\ell-1}$. The predicate `IsLSeg` records the degree and this cosocle property. A top cut divides $D(\Delta)$ into consecutive nonempty subwords, in order from high to low. Each subword is itself the descending word of a segment.

For a list $W=(w_j)$ of irreducibles of ranks $m_j$, let $m(W,\pi)$ be the Jordan–Hölder multiplicity of $\boxtimes_j w_j$ in $r_{(m_j)}\pi$. Set it to zero when the ranks fail to sum to the rank of $\pi$. An occurrence `Wd` records compatible ranks and positive multiplicity. For labelled input words $D_i$, a colouring $c$ assigns each position of $W$ to one input index. The restriction $W|_{c=i}$ reads the assigned positions from left to right. Define $s(W;D_i)$ as the number of colourings satisfying $W|_{c=i}=D_i$ for every $i$.

Two archive inputs will be kept explicit. `IrreducibleAdmissibleGL` gives admissibility of irreducible smooth representations. `SegmentRepresentation` supplies the unique irreducible submodule of the **ascending** cuspidal induction and identifies its fine Jacquet module with the ascending tensor. Its submodule is used below in length two. The normalized geometric lemma, finiteness, exactness and specific local results invoked in the proof have their own source entries.

**Proposition (conditional shuffle formula and descending-word recognition).** [Lean, read] Under the two archive inputs above, with the Jacquet, induction and local representation-theoretic inputs cited below, the following hold.

1. For any indexed family of segments $\Gamma_i$ and $x_i\simeq L(\Gamma_i)$, and any cuspidal word $W$, the multiplicity $m(W,\mathop{\times}_i x_i)$ equals $s(W;D(\Gamma_i))$. In particular every occurring cuspidal word is an order-preserving shuffle of these descending words.
2. If a smooth irreducible $\tau$ embeds into the normalized induction of the letters of $D(\Delta)$, then $\tau\simeq L(\Delta)$.
3. Assume the embedding operations `CuspEmbP`, `MidP`, `RefineP` and `SwapP` as described below. Put $a=\rho\nu^\ell$ and let $\Delta^+$ extend $\Delta$ by $a$. If $b\simeq L(\Delta)$ and $\sigma$ is an irreducible subquotient of $a\times b$, then $\sigma\simeq L(\Delta^+)$ or $\sigma$ embeds into $b\times a$.

#### Proof. The fine Jacquet input

The property `FineJac` says that for $L(\Delta)$, the descending word has multiplicity one, and every occurring all-cuspidal word is that word. Two suppliers use strong induction on length with the same base and step results.

In length one the cosocle is the cuspidal term itself. The one-block Jacquet functor gives that term with multiplicity one, a zero-block word has the wrong rank, and any word with at least two positive ranks uses a proper parabolic and has zero Jacquet module.

For length two write $I=t_0\times t_1$. The cuspidal permutation formula gives each of $01$ and $10$ once in its fine Jacquet module. The ascending submodule supplied by `SegmentRepresentation` has fine Jacquet module $01$. This tensor differs from $10$, as the central actions in the first block differ by $|z|_F^d$. In particular the ascending submodule is proper since $10$ occurs in the parent. Its inclusion lands in the kernel of any irreducible quotient of $I$. Indeed a zero kernel would make $I$ irreducible, and a nonzero kernel contains an irreducible submodule by finite length. Uniqueness of the ascending submodule identifies the latter with the given submodule. Exactness and the multiplicity bound of one in $I$ now rule out $01$ in the cosocle. The cuspidal-permutation occurrence theorem gives a permutation word in the cosocle, so it must be $10$. Exactness bounds that multiplicity by one and also rules out every cuspidal word other than $10$.

For $\ell\ge 3$, split the segment into two nonempty consecutive pieces at a cut $a$. The split intertwiner makes $L(\Delta)$ a quotient of the product of the low piece followed by the high piece. For the shorter segment representations, the archive upgrades the fine word test to an isomorphism of the equal-block Jacquet module with the descending tensor. This uses finite length and the result that every irreducible factor of that module is the descending tensor, together with its multiplicity one. The pair-length lemma then places the two descending words in any occurring cuspidal word as disjoint order-preserving subsequences. The chosen positions already account for rank $\ell d$. Since each letter has positive rank, the positions cover the word and its length is $\ell$.

Apply this to the cuts $1$ and $\ell-1$. In the first cut deleting the minimum exponent gives a descending sequence, and in the second cut deleting the maximum does the same. Distinctness of integer twists lets us compare exponents. Each pair of positions has the required order by one of the two deletions except possibly the pair of extremes. If the minimum precedes the maximum, take a third position. If it lies before the minimum, the deletion of the minimum forces its exponent above the maximum. If it lies after the minimum, the deletion of the maximum forces its exponent below the minimum. Both are impossible. Thus the word is strictly decreasing and must be $D(\Delta)$. Its multiplicity is at most one by comparison with the ascending cuspidal induction, where just the reversing permutation gives that word. Some cuspidal permutation word occurs by the occurrence theorem, so the shape result gives multiplicity at least one for $D(\Delta)$.

#### Proof. From one segment to a product

The shuffle supplier uses the stronger `LSegJacquet` statement. For a Levi whose blocks all have positive rank, a tuple has multiplicity one exactly when it consists of the segment representations of a top cut, and otherwise it has multiplicity zero. Here is how the archive derives this statement from the fine result.

Suppose $y=(y_j)$ occurs in the Jacquet module of $L(\Delta)$. Embed each $y_j$ into a cuspidal induction using the cuspidal embedding theorem. Frobenius reciprocity gives positive multiplicity for each refinement. Jacquet transitivity and the multiplicity inequality `jacquet_multiplicity_concat` give $m(y,L(\Delta))\le m(W,L(\Delta))$ for the concatenated refinement $W$. The fine result makes $W=D(\Delta)$ and gives the upper bound one. Each refinement has positive length because its degrees sum to the positive rank of $y_j$. Thus the refinement for $y_j$ is the descending word of the corresponding piece of a top cut. Part 2 of the proposition, proved independently below, identifies $y_j$ as that piece's segment representation.

Conversely fix a top cut and its segment tuple. Its concatenated descending word has multiplicity one by the fine result. The factorization theorem for concatenated Jacquet multiplicities produces a coarse tuple occurring with positive multiplicity at the ranks of the cut. Apply the preceding argument to this tuple. Its pieces have lengths forced by those ranks divided by $d>0$. A top cut is determined by its ordered lengths, and each piece has a unique cosocle. The resulting tuple therefore agrees with the prescribed one, which has multiplicity one.

In `jmL_cusp_word`, the top cut into singleton pieces immediately gives multiplicity one for the descending word. Conversely a cuspidal term in a top cut must have a singleton piece. A longer piece would have a nonzero Jacquet module for its own fine word, at a proper parabolic, contrary to cuspidality. A top cut consisting of singletons is exactly the descending word. This supplies the row multiplicity used next.

**Cell calculation.** Let $n_i$ be the ranks of the inducing factors $x_i$. Let $m_j$ be the ranks of the letters $w_j$ of the word being tested. The geometric lemma gives a filtration of the normalized Jacquet module with pieces indexed by matrices $B=(b_{ij})$ of nonnegative integers with row sums $n_i$ and column sums $m_j$. A piece first takes a Jacquet module in each row with block sizes $b_{ij}$, rearranges the resulting factors by columns, then induces within each column. Its contribution is the Jordan–Hölder multiplicity of the irreducible tensor $\boxtimes_j w_j$ in that piece. This is an additive sum over the filtration.

- **Split column.** If column $j$ has two positive entries, the target tensor cannot occur in that piece. The cell factorization in the archive extracts an array of irreducible row constituents from any positive contribution. In column $j$ it forces $w_j$ to occur in the induction of that column's constituents. Remove zero-rank factors in order. The remaining parabolic is proper, so the cuspidal-product vanishing theorem contradicts this occurrence.
- **Unsplit columns.** Each column has a unique nonzero entry, since $m_j>0$. Let $c(j)$ be its row. Column induction retains only that entry's representation, up to the canonical equivalence that removes trivial rank-zero factors. In the cell multiplicity sum the column contribution is one for the unique array with class $w_j$ at $(c(j),j)$ and the rank-zero class elsewhere. Every other array contributes zero, since the column tensor determines its irreducible factor classes. Removing zero blocks in each row leaves exactly the subword $W|_{c=i}$ in its original order. This proves that the contribution of the piece is the product of the row multiplicities $m(W|_{c=i},x_i)$. Each row contributes one if its restricted word is $D(\Gamma_i)$ and zero otherwise.

For every valid colouring $c$, put $b_{ij}=m_j$ when $c(j)=i$, and zero elsewhere. The column sums are immediate, and the row sums are the degrees of the descending words. In particular, a rank mismatch implies there are no valid colourings and both sides of the formula are zero. With compatible ranks the map from valid colourings to contributing matrices is injective because the unique positive entry in each column recovers its colour. The case analysis proves surjectivity, and summing the indicators gives the formula.

In `inShW_of_wd` a nonzero multiplicity gives a colouring by the formula. The source constructs the recursive list shuffle by extracting one colour at a time. The list of extracted positions and its complement interleave to recover the original list, by induction that assigns the first position to the appropriate side. On the complement proceed to the next colour. Filtering a later colour in the complement gives the same ordered subword as filtering it in the original list. Enumerating colours in their input order therefore gives the shuffle witness and the required multiset of segments. The source identifies its two descending-list definitions by comparing their lengths and the entry with index $j$, namely $t_{\ell-1-j}$.

#### Proof. Why a descending embedding identifies the irreducible

Start with a segment cosocle $L=L(\Delta)$. The existence supplier gets it by passing from the descending socle of the dual segment to the ascending cosocle via smooth contragredients. To prove that $L$ itself embeds in the descending induction, take its fine Jacquet module at the Levi with $\ell$ blocks of rank $d$. This module has finite length and is nonzero by `FineJac`. Choose a maximal proper submodule and decompose its irreducible quotient as an exterior tensor $\boxtimes_j y_j$. This is an actual quotient, so its word has positive multiplicity.

At this point the $y_j$ are arbitrary irreducibles of rank $d$. Refine each $y_j$ by a cuspidal embedding and transfer multiplicity to the concatenated refined word as above. The fine result forces exactly $\ell$ letters in total, and each of the $\ell$ positive-rank factors contributes at least one. Each factor therefore has a one-letter refinement. Induction from a one-block Levi is the identity up to equivalence, so the embedding in that one irreducible forces equality of classes. It follows that all $y_j$ are cuspidal and `FineJac` now identifies their ordered tuple with $D(\Delta)$.

Frobenius reciprocity carries this Jacquet quotient to a nonzero map from $L$ into the descending induction. One can see the direction of reciprocity by evaluation at the identity. If $f$ maps into normalized induction, evaluating $f(v)$ at the identity kills the unipotent coinvariant relations. The inverse half-modulus in the Jacquet action cancels the half-modulus in the defining induction law. A nonzero induced function has a nonzero value somewhere, and translation moves this value to the identity. Thus the map on coinvariants is nonzero and surjects when its target is irreducible. In the reverse direction the Jacquet map gives the induced function with value at $g$ obtained by evaluating on $gv$. The nonzero map out of $L$ is injective.

The whole descending induction has multiplicity one for its inducing tensor by the cuspidal permutation formula, since all its inducing letters are distinct. It has finite length and is nonzero. Every simple submodule contributes at least one copy of the tensor to its Jacquet module by evaluation. If two simple submodules differed, they would have zero intersection. After quotienting by one of them, the other would still embed. Exactness and additivity would give multiplicity at least two in the whole Jacquet module. Hence the simple submodule is unique. The given $\tau$ and $L$ both embed and must be isomorphic. This proves part 2. The conversion `decLP` identifies the list indexing of $D(\Delta)$ with the indexed family $j\mapsto t_{\ell-1-j}$ and transports the rank sum and injection to that family.

#### Proof. What JuxtP does with the shuffle

Write $\operatorname{Emb}(\sigma;W)$ for an embedding into the induction of the ordered list $W$. The inputs are as follows. `CuspEmbP` supplies a cuspidal list for every irreducible. `MidP` compresses a contiguous block of an embedding list to an irreducible subquotient of its product, keeping the surrounding factors fixed. `RefineP` expands such a factor using an embedding for it. `SwapP` swaps two adjacent factors that are segment representations of unlinked segments, in an embedding with arbitrary fixed surrounding factors.

Use `CuspEmbP` to choose $W$ with $\operatorname{Emb}(\sigma;W)$. Evaluation gives positive multiplicity in the Jacquet module of $\sigma$, and exactness transfers occurrence to $a\times b$. Part 1 gives a shuffle of $[a]$ and $D(\Delta)$. The list shuffle depends on the multiset of input words. The formal permutation lemma exchanges adjacent inputs by reassociating the interleavings of three lists, keeping the internal order of each, then inducts on the permutation. For a singleton and one list the interleaving is precisely an insertion. Induct along the positions taken from the old word until the singleton is taken, after which the remaining old word is unchanged. Thus $D(\Delta)=P Q$ and $W=P[a]Q$, where juxtaposition of lists denotes concatenation.

If $P$ is empty, $W$ is $D(\Delta^+)$ and descending recognition gives the first conclusion. If $P$ is nonempty, every exponent in $Q$ is at most $\ell-2$. The singleton at exponent $\ell$ is unlinked with each of these singleton segments. If their union were a segment, that segment would have length two by injectivity of its own twists. Its second term would be the first term twisted by $\nu$. Matching the two terms to the original cuspidal line would then give adjacent exponents in one order or the other, by twist injectivity on that line. This contradicts the gap of at least two. Swap the singleton past $Q$ one entry at a time, leaving the preceding prefix fixed at each step. This gives $\operatorname{Emb}(\sigma;D(\Delta)[a])$.

Compress $D(\Delta)$ using `MidP` to get $\operatorname{Emb}(\sigma;[\tau,a])$. Choose a cuspidal embedding word $U$ for $\tau$ and refine to get $\operatorname{Emb}(\sigma;U[a])$. Apply the insertion result again to this new word, using the original subquotient relation to $a\times b$. The last letter $a$ is absent from $D(\Delta)$ by injectivity of the real twists. A nonempty suffix after the inserted $a$ would put a letter of $D(\Delta)$ at the end, a contradiction. Cancel the last letter to conclude $U=D(\Delta)$. Descending recognition now makes $\tau$ the segment representation of $\Delta$. Cosocle uniqueness gives equality of its irreducible class with $b$, yielding the second conclusion. $\square$

#### The calculation in rank three

For $\Delta=[\chi,\chi\nu]$, put $b=L(\Delta)$ and $a=\chi\nu^2$. In Zelevinsky's convention for the descending Jacquet character, $b$ is the Steinberg representation of $G_2$ twisted by $(\chi\nu^{1/2})\circ\det$. The upper unipotent Jacquet module of $b$ has word $10$. For example, the normalized ascending induction $\chi\times\chi\nu$ contains the character $(\chi\nu^{1/2})\circ\det$ by the induction law. Its Jacquet character is $01$, since the on-Levi inverse half-modulus is $\nu^{-1/2}\boxtimes\nu^{1/2}$. Removing that factor from the two Jacquet constituents of the ascending induction leaves $10$ for its Steinberg quotient.

For $a\times b$ the Levi ranks on the induction side are $(1,2)$ and those on the Jacquet side are $(1,1,1)$. The only matrices have first row $(1,0,0)$, $(0,1,0)$ or $(0,0,1)$ and complementary second row. The first row contributes $2$ in its selected position, while the second row contributes $1,0$ in order in the two remaining positions. Thus the three graded pieces are the characters $210,120,102$, each once. In particular each occurs with multiplicity one in the Jordan–Hölder list of the Jacquet module.

The upper extension $L([\chi,\chi\nu,\chi\nu^2])$ is the Steinberg representation of $G_3$ twisted by $(\chi\nu)\circ\det$. Its fine word is $210$. The calculation of the two cuts in the fine proof can be done by hand. Inserting $0$ into $21$ yields $021,201,210$. Inserting $2$ into $10$ yields $210,120,102$. Their intersection has just $210$. In the adjacent-pair proof, an embedding word $120$ moves to $102$ by swapping the twists $2$ and $0$, a gap of two. If the word is $102$ already, compression uses the prefix $10$ immediately. In either case the second shuffle forces the refined word for the compressed factor to be $10$, hence that factor is $b$.

#### Remarks on scope and sources

The geometric lemma describes a filtration for a Levi representation. The shuffle formula records a multiset of its irreducible factors. The use of the socle and Frobenius reciprocity is what gives the conclusion about an irreducible representation of the ambient general linear group. Even in rank three, three distinct words count three Jacquet factors of $a\times b$, with no corresponding count of irreducible $G_3$ factors supplied by that calculation alone.

In the production route, `exhaustion_of_three` obtains `CuspEmbP` from refinement, supplies `ShlP` via `segment_product_word_in_shuffle` applied to `segment_jacquet_all`, and supplies `FineUniqP` separately via `irreducible_sub_segment_product`. It then calls `juxtP_of_fineUniq`. The dichotomy is consumed at the linked-pair branch of `move_left`. The middle-factor exactness construction and rank induction are proved in [§12.4.8](#1248-why-ordered-segment-quotients-exhaust-the-irreducible-representations). The ascending segment supplier is explained in [§12.4.10](#12410-producing-the-increasing-segment-from-adjacent-pairs). `Outright` uses the archive's `SegmentRepresentation` supplier in that argument. The results proved here are local statements about words and embeddings, with no assertion of a full Langlands classification.

Zelevinsky (1980), §§1.2–1.3 and 1.6, gives the filtration and matrix description. His §3.1 uses the ascending word for the irreducible submodule of ascending induction. The convention used for $L(\Delta)$ here matches §9.1, which has the descending Jacquet word, the descending submodule and the ascending quotient. Section 9.2 identifies the Steinberg examples, and §9.5 gives the two-block top-cut formula. [Original article](https://www.numdam.org/item/ASENS_1980_4_13_2_165_0/)

[Archive declarations and named inputs](../sources/SOURCES.md#chapter-12-multisegment-exhaustion-jacquet-shuffles-and-segment-production)

### 12.4.10 Producing the increasing segment from adjacent pairs

The two inputs to `JuxtP` in [§12.4.9](#1249-jacquet-shuffles-and-the-descending-segment-word) start with a representation whose fine Jacquet module is a single ordered tensor. The full induction has a tensor for every permutation. To isolate the increasing word, impose one order relation at a time. Each adjacent pair gives a submodule that remembers the order of that pair. The unique simple submodule lies in every one of these submodules.

#### Two calculations with characters

Write $\nu=|\cdot|_F$ on $F^\times$, and use the same symbol for its pullback by the determinant. Let $\chi$ be a smooth character of $F^\times$ and put $\chi_j=\chi\nu^j$. The product $\times$ denotes normalized induction in the indicated order from the upper parabolic. For the upper Borel $B$ with unipotent radical $U$, write $r_B(V)=\delta_B^{-1/2}V_U$. The word $01$ denotes $\chi_0\boxtimes\chi_1$.

**Rank two.** For $\operatorname{diag}(a,b)$ the inverse half-modulus is $|a|^{-1/2}|b|^{1/2}$. Thus the character $D_2=(\chi\nu^{1/2})\circ\det$ has normalized Jacquet word $01$. The normalized induction $\chi_0\times\chi_1$ is unnormalized induction of the trivial character twisted by $D_2$. Constants give its submodule $D_2$, and the quotient by constants is $E_2=D_2\otimes\mathrm{St}_2$. This gives $0\to D_2\to\chi_0\times\chi_1\to E_2\to0$.

The two Borel cells give $01$ and $10$ once each. Exactness leaves $r_B(E_2)\simeq\chi_1\boxtimes\chi_0$. Apply smooth duality to the increasing product with base character $\chi_1^{-1}$. This gives $0\to E_2\to\chi_1\times\chi_0\to D_2\to0$, using self-duality of the untwisted Steinberg. The two orders thus interchange the simple submodule and simple quotient. [Zelevinsky, §§3.1–3.2 and 9.1–9.2](https://www.numdam.org/item/ASENS_1980_4_13_2_165_0/)

**Rank three.** Here $\delta_B^{-1/2}(\operatorname{diag}(a,b,c))=|a|^{-1}|c|$. The character $D_3=(\chi\nu)\circ\det$ therefore has word $012$. It embeds by constants into the increasing induction $\chi_0\times\chi_1\times\chi_2$. Replacing the pair $01$ by its simple submodule gives $D_2\times\chi_2$. Its three fine words are $012,021,201$, one per placement of the singleton $2$. Replacing the pair $12$ gives $\chi_0\times((\chi\nu^{3/2})\circ\det)$, with words $012,102,120$. Both products contain the simple socle, and the two lists intersect only at $012$.

These pair products are the unnormalized inductions of the trivial character from the two maximal standard parabolics, twisted by $D_3$. Their intersection is $D_3$ because the two parabolics generate the group and invariance under both forces a function to be constant. The Steinberg quotient is the Borel induction modulo the sum of the two parabolic inductions. Exactness removes the five words in the union once each, since their common word is counted once in the intersection. This leaves $210$ as the fine Jacquet word of $D_3\otimes\mathrm{St}_3$. This is the simple cosocle of the increasing induction and the simple socle of the decreasing induction. The decreasing induction has simple cosocle $D_3$, by smooth duality as in rank two. [Zelevinsky, §§1.2–1.3, 3.2 and 9.1–9.2](https://www.numdam.org/item/ASENS_1980_4_13_2_165_0/)

#### Definitions and inputs

Fix a nonarchimedean local field $F$ and a smooth irreducible cuspidal complex representation $\rho$ of $G_d=\mathrm{GL}_d(F)$ with $d>0$. Write $\rho_j=\rho\nu^j$. For integers $a\le b$, let $I[a,b]=\rho_a\times\cdots\times\rho_b$. Write $r$ for the normalized Jacquet functor for consecutive upper blocks of size $d$. For a listing $w$ of the indices from $a$ to $b$, write $V_w$ for the external tensor of these twists in that order.

The socle is the sum of simple submodules. The cosocle is the maximal semisimple quotient of a finite-length representation. A simple socle specifies an actual submodule. A simple cosocle specifies a quotient. The archive absorbs the first twist into $\rho$ so that $a=0$. Its consecutive blocks and the exponent in segTerm fix the increasing order. SegmentRepresentation asserts existence and uniqueness of an actual simple submodule and identifies its actual fine Jacquet module.

Use finite length, nonvanishing of induction on nonzero inducing data, exactness of induction and Jacquet functors, induction in stages, and normalized reciprocity $\operatorname{Hom}_G(X,i_P^G V)\simeq\operatorname{Hom}_M(r_P X,V)$. We also use the geometric filtration and irreducibility of the external tensors of irreducibles here. Cuspidals have vanishing proper Jacquet modules and cannot occur as subquotients of proper parabolic induction. The twists are distinct because their central characters on a scalar uniformizer differ by powers of $|\varpi|^d$.

Two further inputs concern two factors. First, $\rho_i\times\rho_{i+1}$ is reducible (NR.rhoNuRhoReducibleC). Second, an irreducible submodule of the induction of two distinct cuspidals that has both ordered fine Jacquet constituents fills that induction (CuspPairSub.surjective_of_jm). The second assertion is stronger than the two-cell calculation. Its direct proof takes a simple quotient of a hypothetical nonzero cokernel and uses the first-cuspidal embedding supplied by JacquetLeft.exists_embedding. A cuspidal quotient of full rank is excluded by cuspidal nonoccurrence in proper induction. Otherwise the embedding gives a positive fine word for that quotient. The geometric lemma identifies it with one of the original two words. The submodule and the quotient would then contribute the same word, exceeding its multiplicity one in the full induction. The Whittaker and derivative arguments in neighboring results have their own proof dependencies.

#### The simple socle and the length-two step

**Lemma.** The induction $I[a,b]$ has a unique simple submodule $S[a,b]$, and the increasing tensor occurs once in $rS[a,b]$.

**Proof.** In the geometric filtration of $rI[a,b]$, splitting a row would take a proper Jacquet module of a cuspidal. Each surviving row therefore fills one column of size $d$. The cells are indexed by permutations, and each surviving cell is its corresponding irreducible external tensor. Distinct twists give multiplicity one for the increasing tensor.

The nonzero finite-length induction has a simple submodule. For every simple submodule $A$, its inclusion gives by reciprocity a nonzero map from $rA$ onto the simple increasing tensor. Two distinct simple submodules would have zero intersection and hence embed as a direct sum. Jacquet exactness would force the increasing tensor to occur at least twice. This proves uniqueness and the claimed multiplicity. In particular every nonzero submodule contains $S[a,b]$, because it has finite length and hence contains a simple submodule. $\square$

**Lemma.** For $b=a+1$, the actual fine Jacquet module of $S[a,b]$ is the increasing tensor.

**Proof.** The previous lemma supplies the increasing tensor once. If the reverse tensor occurred as well, the two-word submodule input would force $S[a,b]=I[a,b]$, contradicting reducibility. The geometric filtration and Jacquet exactness leave only the increasing tensor. A finite-length module with just one simple constituent of multiplicity one is itself simple and isomorphic to that constituent. This is the argument of segTwo_of using jhMult_rev_jac_sub. $\square$

#### The adjacent order constraint

**Lemma (StageP).** For each $a\le i<b$ there is a nonzero submodule $T_i$ of $I[a,b]$ such that every fine Jacquet constituent of $T_i$ of the form $V_w$, with $w$ a permutation of the interval, puts $i$ before $i+1$.

**Proof.** Let $Z=S[i,i+1]$. Replace the adjacent pair in the increasing induction with $Z$, leaving every other factor in place. Induction in stages identifies the product with the pair expanded with $I[a,b]$. Preservation of injections gives an embedding of the product with $Z$ in place of the pair. Take its image as $T_i$. The new product has one block of size $2d$ and all other blocks of size $d$.

Let $V_w$ occur in $rT_i$. A contributing geometric cell has each column supplied by a single row. A split column would induce from a proper parabolic and could not contain that column's cuspidal letter. Consequently the row of $Z$ fills two columns, say $u<v$. Removing zero blocks in order reduces its Jacquet functor to the $(d,d)$ Jacquet functor. By the length-two lemma, that row has the tensor $\rho_i\boxtimes\rho_{i+1}$. Thus $w(u)=i$ and $w(v)=i+1$. The uniqueness of each index in the word gives $w^{-1}(i)<w^{-1}(i+1)$. $\square$

For the native proof, the chosen length is written as $i+2+q$ with the archive indexing from zero. The pair comes from the base twist $\rho_i$, since $(\rho\nu^i)\nu^j=\rho\nu^{i+j}$. In the archive, classMain constructs the replacement by appending the left and right products and transporting the embeddings along induction-in-stages equivalences. Emb.range realizes the nonzero image. Positivity of fine Jacquet multiplicity transfers to the product with the replaced pair. The proof of comb uses Shuffle2.exists_cell_data to select a contributing size matrix and its row constituents. Shuffle2.exists_row deletes the zero entries in order. It compares the resulting cuspidal row with the prescribed tensor by reciprocity and the cuspidal permutation formula, and uses equality of the ordered-block Jacquet modules after identifying their positive sizes. The outcome is an order-preserving embedding of the two row positions into the whole word. The proof of stageP converts equality of the resulting cuspidal classes into equality of their twist indices.

#### Conditional existence and uniqueness by length

**Theorem.** Under the stated inputs, for every $b-a+1\ge1$ there is a unique simple submodule $S[a,b]$ of $I[a,b]$, and $rS[a,b]\simeq\rho_a\boxtimes\cdots\boxtimes\rho_b$.

**Proof.** For length one the one-block induction and Jacquet functor are the identity. Length two was proved above. Suppose the theorem holds for all shorter intervals and the current length is at least three. The multiplicity-one lemma gives the unique simple submodule and supplies its increasing tensor once. By the inductive hypothesis, $S[a,b-1]\times\rho_b$ embeds in $I[a,b]$ and is nonzero. Its image contains $S[a,b]$. Any fine Jacquet constituent of $S[a,b]$ is therefore a constituent of this product. Each column of a contributing cell belongs to a single row, by cuspidality. The row of $S[a,b-1]$ fills $b-a$ columns. Deleting zero blocks, the inductive Jacquet identification forces the subsequence $a,a+1,\ldots,b-1$ in those columns. By the StageP lemma, the same constituent places $b-1$ before $b$, since $T_{b-1}$ also contains $S[a,b]$. These relations force the increasing word. Multiplicity one and finite length give the asserted equivalence of actual modules. $\square$

The archive uses a direct proof of the all-length step. In segRep_of, each $T_i$ contains some simple submodule. Uniqueness identifies it with $S[a,b]$. Jacquet injectivity passes each constituent into each $rT_i$. Its inverse permutation is then increasing on every successive pair, and so is the identity. The final multiplicity-one argument upgrades the constituent calculation to an equivalence of representations. The archive uses only length-two segments in this step. The length induction above is a textbook proof using a shorter prefix and the final pair.

#### The return to the decreasing segment and JuxtP

The increasing socle here is the segment representation of Zelevinsky §3.1. The Langlands segment $L(\Delta)$ in §§12.4.8–12.4.9 uses the simple cosocle of the increasing induction, equivalently the simple socle of the decreasing induction. Its fine tensor runs from the high twist to the low twist. In length two, the increasing socle belongs to the kernel of every simple quotient of the increasing induction: the kernel is nonzero by reducibility and contains the unique simple submodule. Exactness removes the increasing word from the quotient. The quotient has a fine cuspidal word by the occurrence theorem, so its word must be the reverse one. This is the point at which the ascending theorem supplies the base case of the descending Jacquet argument in §12.4.9. A common exponent shift twists the whole induction and its Jacquet module. Reversing the order changes the induced object and the side on which the simple constituent is specified. The upper Jacquet normalization uses the inverse half-modulus in either order. [Zelevinsky, §§3.1–3.2 and 9.1–9.5](https://www.numdam.org/item/ASENS_1980_4_13_2_165_0/)

The exported `PositivityTheory.RgGu.segmentRepresentation` passes `SRC.stageP`, the geometric lemma `hG` assembled from the filtration and finiteness, and `SRC.segTwo_of hG NR.rhoNuRhoReducibleC` to `SRC.segRep_of`. Both `segRep_of` and `segTwo_of` use that `hG`. The `StageP` interface takes a geometric-lemma argument, while the body `StageC.stageP` gets its cell calculation from the imported `Shuffle2` results and consumes the two-term statement. Outright passes this exact theorem to langlandsExhaustionGL_of_seg. In exhaustion_of_three that argument enters the two inputs to juxtP_of_fineUniq. It supplies the shuffle via segment_jacquet_all and segment_product_word_in_shuffle and supplies the identification via irreducible_sub_segment_product. The first supplies the allowed insertions into the decreasing word. The second, used through decLP, identifies a simple representation embedded in decreasing induction. A front insertion identifies the extended segment. In the other branch it identifies the old segment after the old word has been compressed, giving an embedding with the new letter at the end. This is the use of the increasing socle theorem in the actual adjacent-extension dichotomy.

**Reading boundary.** [Lean, read] refers to the local proof bodies in the source map. The deeper adjacent reducibility construction, the deeper first-cuspidal embedding used in two-word surjectivity, the separate Whittaker and derivative arguments, and the geometric filtration, finiteness and lower-level induction and Jacquet exactness remain named [Lean] inputs with [Open] reading boundaries. Linked and unlinked two-segment interactions remain separate inputs at this reading depth. The two character calculations illustrate the general argument and its normalization.

[Archive declarations and named inputs](../sources/SOURCES.md#chapter-12-multisegment-exhaustion-jacquet-shuffles-and-segment-production)

### 12.4.11 From a conductor-ball average to the mirabolic pairing

#### Motivation

The highest-derivative pairing used by [NuPair](#the-actual-nupair-call) repeatedly discards last-column relations. The adjacent-pair reducibility input in [§12.4.10](#12410-producing-the-increasing-segment-from-adjacent-pairs) uses the complementary-series assembly of NuPair. An invariant pairing on the original representations does not automatically descend through those relations. To construct one that does, integrate a matrix coefficient against the inverse of the desired last-column character. Two facts make this prescription work. Integration over successively larger boxes becomes exactly constant, and every nonzero left coinvariant class retains a right test vector. The small scale in this argument is the radius of a **frequency** box. The integration box in the space of columns grows as the frequency box shrinks.

#### Examples over the 3-adic field

Normalize additive Haar measure by $\lambda(\mathbb Z_3)=1$ and use product measure on two coordinates. Let $\psi_0(x)=\exp(2\pi i\{x\}_3)$, where $\{x\}_3$ is the finite sum of negative-power terms in the 3-adic expansion, taken modulo $\mathbb Z$. This is additive because that sum represents the class modulo $\mathbb Z_3$. Set $\psi_d(x)=\psi_0(3^{-d}x)$ for the two values $d=0,2$. The largest ball on which $\psi_d$ is trivial is $3^d\mathbb Z_3$. On the next larger ball the element $3^{d-1}$ has value $\zeta=\exp(2\pi i/3)$. A one-dimensional ball $3^k\mathbb Z_3$ has mass $3^{-k}$ by successive partitions into three equal cosets.

**Example 1 (conductor $\mathbb Z_3$).** Take the column box $L=(3^{-1}\mathbb Z_3)^2$, of mass $9$. Its frequency box is $D=(3\mathbb Z_3)^2$, of mass $1/9$.

1. For $x=(0,1/3)$ each $b\in D$ satisfies $b\cdot x\in\mathbb Z_3$. The integral of $\psi_0(-b\cdot x)$ over $D$ is $1/9$. For $x=(0,1/9)$ the second frequency coordinate runs over the three cosets $3j+9\mathbb Z_3$ with $j=0,1,2$. Each product cell has mass $1/27$, so the integral is $(1+\zeta^{-1}+\zeta^{-2})/27=0$.
2. At the first $x$, replacing $D$ by $(0,1)+D$ multiplies its integral by $\psi_0(-1/3)=\zeta^{-1}$. Its mass stays $1/9$. Dividing the unshifted integral by this mass gives the value $1$ inside $L$ and $0$ at the tested point outside.
3. On the column side take the test coefficient $C(x)=\psi_0(x_2)1_L(x)$. Its weighted integral over $L$ is $9$. For $y=(0,1/3)\in L$, the tests $C(x+y)$ and $C(x-y)$ give $9\zeta$ and $9\zeta^{-1}$. If $p=\operatorname{diag}(3,1)$, then $pL=\mathbb Z_3\times3^{-1}\mathbb Z_3$ has mass $3$. Integrating $\psi_0(-x_2)C(p^{-1}x)$ on $pL$ gives $3=|3|_3\cdot9$.

**Example 2 (conductor $9\mathbb Z_3$).** Use $\psi_2$, the column box $L=(3^{-2}\mathbb Z_3)^2$ of mass $81$, and its frequency box $D=(3^4\mathbb Z_3)^2$ of mass $3^{-8}$.

1. For $x=(0,1/9)$ the product $b\cdot x$ lies in $9\mathbb Z_3$ throughout $D$, so the integral is $3^{-8}$. For $x=(0,1/81)$ the second frequency coordinate is $81j$ modulo $729\mathbb Z_3$. There are nine product cells of mass $3^{-10}$, and the values are $\eta^{-j}$ for $0\le j<9$, with $\eta=\exp(2\pi i/9)$. Their sum is zero by multiplication by $\eta^{-1}$. The intermediate outside point $x=(0,1/27)$ gives the three cube roots with cells of mass $3^{-9}$, also summing to zero.
2. For $x=(0,1/9)$ the translate $(0,27)+D$ gives $3^{-8}\zeta^{-1}$ since $\psi_2(27/9)=\psi_0(1/3)$. The unshifted mass cancels in the normalized frequency average as in Example 1.
3. Take $C(x)=\psi_2(x_2)1_L(x)$ and $y=(0,3)$. The weighted integral is $81$, and the column translates give $81\zeta$ and $81\zeta^{-1}$. For $p=\operatorname{diag}(9,1)$, the image $pL=\mathbb Z_3\times3^{-2}\mathbb Z_3$ has mass $9$, and $\psi_2(-x_2)C(p^{-1}x)$ integrates to $9=|9|_3\cdot81$.

These are test-function computations [Expository]. A representation-theoretic example below constructs the coefficient and its two Jacquet quotients from actual representations.

#### Definitions

Let $F$ be a nonarchimedean local field, with ring of integers $\mathcal O$, uniformizer $\varpi$, residue cardinality $q$, and absolute value $|\varpi|=q^{-1}$. Write $G_a=\mathrm{GL}_a(F)$, $\nu(g)=|\det g|$, and $P_a$ for the matrices in $G_a$ with last row $(0,\ldots,0,1)$. In this section $m=n+1\ge1$, so the archive's $\mathrm{Mir}(F,n+1)$ is $P_{m+1}$ and its $\mathrm{Mir}(F,n)$ is $P_m$. Write $u(x)$ for the unipotent matrix with last column $(x,1)$, where $x\in F^m$, and all other columns those of the identity. Write $\ell(g)=\operatorname{diag}(g,1)$ for $g\in G_m$. Thus $\ell(g)u(x)\ell(g)^{-1}=u(gx)$.

Let $\psi:F\to S^1$ be continuous and nontrivial. Its conductor parameter is any $c\in F^\times$ such that $c\mathcal O$ is the largest centered ball on which $\psi$ is trivial. To see existence, choose a small ball mapped into the arc $|\arg z|<\pi/2$. Every positive integral multiple of a point of that ball is still in it. If $z\ne1$, a first positive multiple of the absolute value of its principal angle reaches $\pi/2$ before exceeding $\pi$, provided the angle starts in the arc. Hence all powers staying in the arc forces $z=1$. A point on which $\psi$ is nontrivial bounds the radii of triviality above. The radii of nonzero centered balls are discrete, so there is a largest one. This proves the exact condition called `HasConductor`. The additive kernel itself can be larger than $c\mathcal O$. [Lean, read]

For $t\in F^\times$ put $L_t=(t\mathcal O)^m$ and $D_t=L_{c/t}$. Write $dx$ and $db$ for the same product additive Haar measure in the two sets of variables. The Haar measure on $F$ can have any positive normalization. Let $T,T'$ be smooth complex representations of $P_{m+1}$ on $V,V'$, and let $B:V\times V'\to\mathbb C$ be complex bilinear. For $s\in\mathbb Z_{\ge0}$ assume
$$
B(T(h)v,T'(h)v')=\nu(h)^s B(v,v') .
$$
Set $C_{v,v'}(x)=B(T(u(x))v,v')$, $w(x)=\psi(-x_m)$ and
$$
J_M(v,v')=\int_M w(x)C_{v,v'}(x)\,dx .
$$
The condition $\operatorname{EvVal}(v,v';A)$ means that there is a threshold $t_0\in F^\times$ such that $J_{L_t}(v,v')=A$ for every $|t|\ge |t_0|$. Each vector has an open stabilizer, which contains a compact open subgroup since $P_{m+1}$ has the congruence subgroups at the identity as a neighborhood basis. By continuity of $x\mapsto u(x)$, some small $L_d$ fixes $v$. Then $C_{v,v'}$ is constant on every coset of $L_d$, because $u(x+y)=u(x)u(y)$. The weight is continuous and locally constant by the conductor condition. This gives integrability on every compact measurable domain used below.

Put $\chi(u(y))=\psi(y_m)$. Let $R_\chi(V)$ be the complex linear span of $T(u(y))v-\chi(u(y))v$ and define $V_\chi=V/R_\chi(V)$. Define $V'_{\chi^{-1}}$ using $T'$ and $\chi^{-1}$. The action of $p\in P_m$ on either quotient is induced by $\ell(p)$, since $(py)_m=y_m$. This is the archive's unnormalized $\Phi^-$ action.

#### Lemma on one twisted step

**Lemma (one twisted step).** [Lean, read] With the above hypotheses, every $(v,v')$ has a unique eventual value $B_0(v,v')$. It is bilinear and induces a bilinear form $\overline B$ on $V_\chi\times V'_{\chi^{-1}}$ with
$$
\overline B(p[v],p[v'])=\nu(p)^{s+1}\overline B([v],[v']) .
$$
If $B$ is left nondegenerate, meaning that every $v\ne0$ admits $v'$ with $B(v,v')\ne0$, then $\overline B$ is left nondegenerate. The threshold can depend on the pair of vectors. The theorem includes the case $m=1$, for which $P_m$ is the trivial group.

#### Proof

**1. Orthogonality on the conductor box.** For $x\in L_t$, each $b_i x_i$ lies in $c\mathcal O$ when $b\in D_t$, and so does their sum. If $x\notin L_t$, some $|x_i|>|t|$. The ball $x_i(c/t)\mathcal O$ is then strictly larger than $c\mathcal O$. Choose $b_0$ supported in that coordinate with $b_0\in D_t$ and $\psi(-b_0\cdot x)\ne1$. Translation by $b_0$ preserves $D_t$ and its measure, and multiplies the integral by that nonidentity scalar. Hence
$$
\int_{D_t}\psi(-b\cdot x)\,db=\operatorname{vol}(D_t)1_{L_t}(x).
$$
In particular, let $f$ be continuous on a compact measurable $M$ and put $I_b(M,f)=\int_M\psi(-b\cdot x)f(x)\,dx$. The integrand on $D_t\times M$ is bounded, measurable and supported on a set of finite measure. Fubini gives
$$
\frac{1}{\operatorname{vol}(D_t)}\int_{D_t} I_b(M,f)\,db=\int_{M\cap L_t} f(x)\,dx.
$$
The denominator is finite and strictly positive. If $I_b(M,f)=A$ for every $b\in D_t$, the cut-down integral equals $A$. In particular this applies with $A=0$. The factor that divides out belongs to the frequency integral. The matrix-coefficient integral $J_M$ itself has no volume denominator. This argument uses compact character orthogonality rather than a self-dual Haar normalization.

**2. Small shears and transport of the frequency twist.** For $b\in F^m$ let $H_b=I+e_m b^{\mathrm T}$, where $e_m$ is the last coordinate vector. Then $H_bx=x+(b\cdot x)e_m$. Its determinant is $1+b_m$ by last-row expansion. For $\|b\|_\infty<1$, this is a unit of $\mathcal O$. The inverse is $I-(1+b_m)^{-1}e_m b^{\mathrm T}$, as one verifies by multiplying and using $(e_m b^{\mathrm T})^2=b_m e_m b^{\mathrm T}$. Both matrices tend to $I$ as $b$ tends to zero. Thus for a fixed pair of vectors, all sufficiently small $b$ make $\ell(H_b)$ fix both. For any one right vector and any compact box of such $b$, the vectors $T'(\ell(H_b))v'$ form a finite set. Indeed the orbit map has open fibers, which are the pullbacks of cosets of the open stabilizer, and compactness reduces the cover by the fibers to a finite one.

For fixed $g\in G_m$, small $b$ preserve all domains $M=g^{-1}L_z$, uniformly in $z$. These domains are compact and open since $g$ is a homeomorphism. Choose $C\ge1$ bounding the absolute values of the entries of $g^{-1}$ and of $ge_m$. Then every entry of $ge_m b^{\mathrm T}g^{-1}$ has absolute value at most $C^2\|b\|_\infty$. Choose a ball on which this bound is strictly below $1$. The conjugates by $g$ of both $H_b$ and $H_b^{-1}$ have integral entries by the inverse formula and $|1+b_m|=1$. Both act on each $L_z$, so $H_bM=M$. This gives the same uniform membership bound as the source's two directions of the ultrametric estimate.

For later use, the Haar change of variables for a linear $g$ is $dx=|\det g|\,dy$ under $x=gy$. In dimension one, scaling by a unit preserves $\mathcal O$, so Haar uniqueness makes its factor $1$. Scaling by $\varpi$ has factor $1/q$ by the $q$-coset partition of $\mathcal O$. In dimension $m$, diagonal stretches multiply those factors, coordinate permutations preserve product measure, and an elementary transvection preserves it by translation in one coordinate and Fubini. These matrices generate $G_m$ by elimination, so their factors multiply to $|\det g|$. Equivalently, the pushforward is $|\det g|^{-1}dx$.

The representation law and covariance of $B$ give
$$
C_{T(\ell(g))v,T'(\ell(g))v'}(x)=\nu(g)^s C_{v,v'}(g^{-1}x).
$$
Take $g=H_b$ and suppose $\ell(H_b)$ fixes $v$ and $H_bM=M$. Its determinant has absolute value $1$. Changing variables $x=H_by$ therefore changes neither Haar mass nor the coefficient covariance factor. It changes the weight by $w(H_by)=\psi(-b\cdot y)w(y)$. For $f(x)=w(x)C_{v,v'}(x)$ this proves
$$
I_b(M,f)=J_M(v,T'(\ell(H_b))v').
$$
Thus a frequency twist is exactly the integral against a right vector obtained by a small shear. In the fixed-pair case it gives $I_b(M,f)=J_M(v,v')$ for every sufficiently small $b$.

**3. Stabilization and linearity.** Fix $g,v,v'$. Choose $r\in F^\times$ with $|r|<1$ so that all $b\in L_r$ satisfy the lattice bound and the two fixed-vector conditions of step 2. Whenever $|c/t|\le |r|$ and $gL_t\subset L_z$, take $M=g^{-1}L_z$. Every $b\in D_t$ has $I_b(M,f)=J_M(v,v')$. Step 1 with $L_t\subset M$ gives
$$
J_{g^{-1}L_z}(v,v')=J_{L_t}(v,v').
$$
Equivalently, the integral on $g^{-1}L_z\setminus L_t$ vanishes. This is the conductor bound, including its uniformity in the larger box. For $g=1$ choose $t=c/r$. All $|z|\ge|t|$ yield the same value $J_{L_t}$. This is the existence step of `EvVal`.

The larger of any two threshold radii is itself allowed and enforces both equalities, so the eventual value is unique. The coefficient is additive in either variable and homogeneous under complex scalars. On a common box beyond the two thresholds, integrability permits adding the integrals. For scalar multiplication the original threshold works. Uniqueness identifies the resulting values with those of the sum and scalar multiple, proving bilinearity, including for the scalar zero.

**4. Translation and the determinant increment.** Inserting $T(u(y))$ in the left coefficient translates the argument to $x+y$. Inserting $T'(u(y))$ on the right translates it to $x-y$, by applying covariance to $u(y)$ with determinant $1$. Enlarge the integration box until it contains $y$ and the eventual-value threshold. Translation by either $y$ or $-y$ preserves the additive box. The weights after changing variables are $\psi(y_m)w(x)$ on the left and $\psi(-y_m)w(x)$ on the right. Thus
$$
B_0(T(u(y))v,v')=\chi(u(y))B_0(v,v'),\qquad
B_0(v,T'(u(y))v')=\chi(u(y))^{-1}B_0(v,v').
$$

For $p\in P_m$, $w(py)=w(y)$. The coefficient rule and $x=py$ give
$$
J_{L_z}(T(\ell(p))v,T'(\ell(p))v')=\nu(p)^s\nu(p)J_{p^{-1}L_z}(v,v').
$$
Fix $t$ above the eventual threshold for $(v,v')$ and large enough that $|c/t|\le |r|$ for the conductor bound with $g=p$. If $|z|$ exceeds $|t|$ times a bound on the entries of $p$, then $pL_t\subset L_z$. Step 3 identifies the preimage integral with $B_0(v,v')$. Uniqueness gives covariance with exponent $s+1$. The two translation factors are the quotient characters. The extra $\nu(p)$ comes from the additive Haar measure on columns.

**5. Left separation at a finite stage.** Assume $B$ is left nondegenerate and $v\notin R_\chi(V)$. Choose a small box $K=L_d$ on which $u(k)$ fixes $v$ and $\chi(u(k))=1$. Every larger box $L_t\supset K$ is a union of finitely many disjoint cosets $a+K$, with representatives in a set $S$. Compactness gives finiteness and Haar translation gives equal mass. The vector
$$
v_t=\sum_{a\in S}\psi(-a_m)T(u(a))v
$$
has class $|S|[v]\ne0$, because each summand has class $[v]$ and the coefficient field is $\mathbb C$. Hence $v_t\ne0$. Choose $v'$ with $B(v_t,v')\ne0$. On each coset the weighted coefficient is constant, so $J_{L_t}(v,v')=\operatorname{vol}(K)B(v_t,v')\ne0$. The right vector can depend on $t$.

**6. From finite stages to an eventual nonzero test.** Fix $v\notin R_\chi(V)$. Choose $r$ that ensures the left fixed-vector condition and that $H_b$ preserves all untransformed boxes for $b\in L_r$. Choose $t$ large enough for step 5 and with $|c/t|\le |r|$. Take a right vector $v'$ from step 5 for this $t$. Suppose $B_0(v,w')=0$ for every $w'\in V'$. The shear orbit of $v'$ for $b\in L_r$ is finite. Each orbit vector has an eventual vanishing threshold with left vector $v$. Choose $u$ with radius at least all these thresholds and at least $|t|$. The shear identity on $M=L_u$ now gives $I_b(L_u,f)=0$ for all $b\in D_t$, since each is the integral against one of those orbit vectors. By step 1 the integral on $L_u\cap L_t=L_t$ vanishes, contradicting the choice of $v'$. This proves the existence of a right vector with $B_0(v,w')\ne0$. The compact orbit and its common threshold are what allow the finite-stage quantifier to be upgraded.

**7. The two Jacquet quotients.** The translation identities kill every generator of $R_\chi(V)$ in the left slot and of $R_{\chi^{-1}}(V')$ in the right slot. Bilinearity kills the two spans. Thus $\overline B([v],[v'])=B_0(v,v')$ is independent of both representatives, and surjectivity of the two quotient maps gives uniqueness. The $P_m$ covariance already proved is precisely covariance for their induced actions. For any $[v]\ne0$, step 6 provides $w'$ with a nonzero value, so $[w']\ne0$ as well. The left radical of $B_0$ is exactly $R_\chi(V)$. The argument only gives the inclusion of $R_{\chi^{-1}}(V')$ in the right radical. $\square$

#### A nonzero pair of actual quotients and two hypothesis tests

**A representation on the affine mirabolic group.** [Expository] For $m=1$, write an element of $P_2$ as $(a,y)$ with upper row $(a,y)$ and multiplication $(a,y)(b,z)=(ab,y+az)$. On $V=V'=C_c^\infty(F^\times)$, the locally constant compactly supported functions, define
$$
(T(a,y)f)(z)=\psi(zy)f(za),\qquad
(T'(a,y)h)(z)=\psi(-zy)h(za).
$$
The multiplication law verifies both representation identities. Compact support and local constancy give invariance under a common sufficiently small unit subgroup by a finite cover of the support by multiplicative cosets. Bounding $|z|$ on the support gives a small additive subgroup for which the phases are all trivial. These subgroups give an open stabilizer. Put $d^\times z=dz/|z|$ and use the bilinear form $B(f,h)=\int_{F^\times}f(z)h(z)|z|^{-s}\,d^\times z$. The phases cancel and changing from $z$ to $za$ gives $|a|^s$. The form is left nondegenerate by testing a compact open coset on which a nonzero $f$ is constant and nonzero.

Both actual quotients are evaluations at $z=1$. The twisted relations vanish there. If a locally constant compactly supported function vanishes there, its compact support avoids $1$. For each point $z$ of the support choose $y$ with $\psi((z-1)y)\ne1$. The coefficient $\psi(zy)-\psi(y)$ is then a nonzero constant on a neighborhood of $z$. A finite disjoint compact open refinement of those neighborhoods partitions the support. On each piece divide the function by that constant to write the piece as one twisted relation. The same argument with $\psi^{-1}$ proves the right kernel equality. Evaluation is onto, for instance by the indicator of $1+\varpi\mathcal O$. This identifies two one-dimensional coinvariants.

On this object the integral can also be evaluated directly. Fubini over the compact supports and step 1 in one coordinate give
$$
J_{L_t}(f,h)=\lambda(t\mathcal O)\int_{(1+(c/t)\mathcal O)\cap F^\times} f(z)h(z)|z|^{-s}\,d^\times z .
$$
For $|t|$ large the second domain consists of units and $f,h$ are constant there. Writing $\lambda(\mathcal O)=a_0$, the two masses multiply to $a_0^2|c|$, and $\overline B(f(1),h(1))=a_0^2|c|f(1)h(1)$. Over $\mathbb Q_3$ with $a_0=1$, take $f=h=1_{1+3\mathbb Z_3}$. With $\psi_0$, $t=3^{-1}$ gives masses $3$ and $1/3$, so the value is $1$. With $\psi_2$, $t=3^{-2}$ gives masses $9$ and $3^{-4}$, so the value is $1/9$. The two displayed coinvariant classes are both represented by the actual vector with value $1$ at the specified point. The example is a pair of mirabolic representations, with its own $P_2$ action. The segment example below concerns the separate requirement of coming from an irreducible $G_a$ representation for the NuPair consumer.

**A nontrivial determinant test on the quotients.** The same construction works on $C_c^\infty(F^m)$, with $(g,y)\in P_{m+1}$ acting on $f$ by $\psi(z\cdot y)f(g^{\mathrm T}z)$ and on $h$ by $\nu(g)^{s+1}\psi(-z\cdot y)h(g^{\mathrm T}z)$. Use $B(f,h)=\int f(z)h(z)\,dz$. The group law is $(g,y)(a,w)=(ga,y+gw)$, and the change of variables $z\mapsto g^{\mathrm T}z$ gives covariance $\nu^s$. Smoothness follows by choosing a compact open lattice containing the support, a finer lattice whose cosets make the function constant, and a congruence subgroup on the first lattice that acts trivially modulo the finer one. Small $y$ make the characters trivial throughout the support. Write $a_0=\lambda(\mathcal O)$ and let $\lambda^m$ be the product measure used for both $dx$ and $dz$. Step 1 gives $J_{L_t}(f,h)=\lambda^m(L_t)\int_{e_m+D_t} f(z)h(z)\,dz$. For sufficiently large $|t|$, the two masses have product $\lambda^m(L_t)\lambda^m(D_t)=a_0^m\lambda^m(L_c)$. The eventual form is $a_0^m\lambda^m(L_c)f(e_m)h(e_m)$. The same finite partition argument for the two relation spaces works with $\psi((z-e_m)\cdot y)$, using a single coordinate of $z-e_m$ that is nonzero. For $m=2$ over $\mathbb Q_3$ with $a_0=1$, take $f=h=1_{e_2+(3\mathbb Z_3)^2}$ and $p=\operatorname{diag}(3,1)\in P_2$. Since $p^{\mathrm T}e_2=e_2$, the left class stays $1$ and the right class becomes $3^{-(s+1)}$. Thus the pairing changes from $1$ to $3^{-(s+1)}$ with $\psi_0$, or from $3^{-4}$ to $3^{-(s+5)}$ with $\psi_2$.

**Delete nontriviality.** [Expository] Take both representations trivial and one-dimensional, $s=0$ and $B(v,v')=vv'$. With $\psi=1$, $J_{L_t}(1,1)=\operatorname{vol}(L_t)$ grows with $|t|$. No conductor ball is maximal, so the shrinking frequency box in step 1 cannot be constructed. All the representation and pairing hypotheses still hold.

**Delete left smoothness.** [Expository] Over $\mathbb Q_3$ use $\psi_0$ and the same affine formulas on $V=C_c(\mathbb Q_3)$, the continuous compactly supported functions, and $V'=C_c^\infty(\mathbb Q_3)$, multiplying the right action by $|a|_3$. Use additive measure and $B(f,h)=\int f(z)h(z)\,dz$. This form has covariance $s=0$, and it separates each nonzero left vector by a compact open set on which a rotated real part of the vector is strictly positive. The right representation is smooth by the same compact-support argument. Take $h=1_{1+3\mathbb Z_3}$ and $f(z)=|z-1|_3 h(z)$. Every neighborhood of $1$ in $\mathbb Q_3^\times$ contains $a\ne1$ in $1+3\mathbb Z_3$. At $z=1$, $T(a,0)f$ has value $|a-1|_3>0$ while $f(1)=0$. Thus the small scaling shears do not fix $f$. For $t=3^{-j}$ with $j\ge1$, the compact integral still exists, and the one-dimensional orthogonality computation gives
$$
J_{L_t}(f,h)=3^j\int_{3^j\mathbb Z_3}|u|_3\,du
=3^j(1-1/3)\sum_{\ell\ge j}3^{-2\ell}=\tfrac34\,3^{-j}.
$$
The values are all unequal. Smoothness in step 2 is needed even when the matrix coefficients remain continuous. In step 6, smoothness on the right is what makes the shear orbit finite and lets one select a common threshold.

#### Why this is the pairing at the highest derivative

The source uses the evaluation pairing between a smooth $G_N$ representation $\omega$ and its smooth contragredient. Each twisted step in `pair_iter` applies the theorem and increases $s$ by one. At order $t=j+1$, `pair_deriv` takes $j$ twisted steps and one ordinary Jacquet step. For the last step the next twisted quotient on the left must vanish. The separate [joint-character detection in §12.4.6](#1246-detecting-a-vector-by-all-its-twisted-jacquet-images) then shows that the last-column group acts trivially on the left. Covariance with determinant $1$ gives ordinary descent on the right, with no extra Haar factor. Starting with $s=0$ yields $\nu^j=\nu^{t-1}$ on the surviving general linear group. This section supplies the twisted steps and uses the inherited highest-order test and ordinary step. Chapter 7 §§7.4.3.14–15 uses the same bare derivative convention of successive twisted quotients followed by an ordinary quotient. The determinant character from the bilinear pairing here and the shift by $(1-t)/2$ used there for a unitarisable highest derivative have distinct roles.

As a concrete instance of that consumer, use the ascending segment representation $\omega=Z([\rho,\rho\nu])$ of $G_4$ over $\mathbb Q_3$, the length-two case of the increasing segment in [§12.4.10](#12410-producing-the-increasing-segment-from-adjacent-pairs). For an explicit seed, let $I^+$ consist of matrices $i=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)$ with $a,d\in1+3\mathbb Z_3$, $b\in\mathbb Z_3$, $c\in3\mathbb Z_3$. The residues of $b$ and $c/3$ add under multiplication, so $i\mapsto\zeta^{\overline{b+c/3}}$ is a character. Each affine root coordinate gives a nontrivial residue character. It extends trivially across the center $Z$ since it is trivial on $I^+\cap Z$. The matrix $h=\left(\begin{smallmatrix}0&1\\3&0\end{smallmatrix}\right)$ normalizes $I^+$ and swaps those residues. Since $h^2=3I$, extension by the value $1$ on $h$ is compatible with the trivial central character. Use the compact induction from $Z I^+\langle h\rangle$ of this extended character for $\rho$. The compact induction and irreducibility are the cited human input. Zelevinsky's segment formula gives highest order $2$ and normalized derivative $\rho$, so the bare derivative is $S=\rho\nu$. The right bare derivative of the dual segment is $\rho^\vee$. One twisted step really occurs, since an ordinary quotient of that first twisted quotient is nonzero. The displayed affine integrals above have their own coefficient vectors and do not compute any specific matrix coefficient of this $G_4$ representation. [Adrian–Liu, §3.1, pp. 5–6](https://arxiv.org/pdf/1310.2585v4) · [Zelevinsky II, §§3.1–3.5, pp. 180–182](https://www.numdam.org/item/10.24033/asens.1379.pdf)

In the actual NuPair producer, an injection from a simple left derivative class $S$ lets this pairing produce a right quotient $Q=S^\vee\nu^{t-1}$. The first normalized Jacquet letter is $\alpha=S\nu^{-t/2}$, from the negative half of the parabolic modulus. After normalizing the right letter and applying the inherited dual reversal, the last letter is
$$
(Q\nu^{-t/2})^\vee = S\nu^{1-t/2}=\alpha\nu .
$$
For the segment example $t=2$, this gives $\alpha=\rho$ and $\alpha\nu=\rho\nu$. The calls to `pair_deriv` in both NuPair assemblies use the same convention. The complementary-series assembly uses `DerFin` for the finite-length input that provides its simple submodule. That assembly feeds the adjacent-pair reducibility input `NR.rhoNuRhoReducibleC` named in [§12.4.10](#12410-producing-the-increasing-segment-from-adjacent-pairs). The general Gelfand–Kazhdan distributional result, Whittaker uniqueness and heredity, and the full local Langlands correspondence retain their separate status.

#### Remarks on normalization, scope and attribution

The unit-ball examples fix $a_0=1$. For arbitrary $a_0$, the high-dimensional example uses two product Haar integrations, one in $B$ and one in the column average, so its coefficient has the factor $a_0^m\lambda^m(L_c)$. The finite certificate checks the unit-normalized values. In a separate polar integration formula, mass one for the angular probability measure concerns that factor. The mass of the compact subgroup for the ambient measure requires the full formula. In a local coordinate argument, a derivative computed at the origin gives first-order information there. An exact derivative formula throughout a neighborhood requires a pointwise calculation.

Bernstein–Zelevinsky use the same mirabolic group, character stabilizer and coinvariant quotients. Their normalized $\Phi^-$ action is the bare action here multiplied by $\nu^{-1/2}$ on each side. These two half-powers absorb the single Haar factor of step 4. In their convention a $\xi$-pairing satisfies $\xi(g)B(gv,gv')=B(v,v')$. The mirabolic group module is $\nu^{-1}$, so their module-pairing input has bare covariance $\nu$. To compare an initial bare exponent $s$, temporarily twist the right input by $\nu^{1-s}$, which is trivial on the last column and commutes with the quotient. Their proof of Proposition 3.8 explains why restriction to the compactly induced submodules retains left separation. Proposition 3.7 then descends this pairing on those submodules to a module-pairing on the normalized twisted quotients. On the smaller mirabolic this still has covariance $\nu$. Removing the temporary right twist and restoring the two bare actions gives exponent $s+1$. Conjugation by $\operatorname{diag}(-I_m,1)$ negates the last column and fixes the embedded $P_m$, so their same-character quotient on the right is isomorphic to the inverse-character quotient used here. The representation-theoretic conclusion is a specialization of the classical pairing theorem. This section explains A2's conductor-box proof and its source-level connection to NuPair. [Bernstein–Zelevinsky I, §§1.8–1.9, pp. 444–445, and §§3.1–3.8, pp. 450–453](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0.pdf) · [Bernstein–Zelevinsky 1976, §§5.3–5.4 and §§5.9–5.12, pp. 44–48](https://www.uni-muenster.de/imperia/md/content/theoretische_mathematik/topologie/bernstein-zelevinsky.pdf)

**Reading status.** Author-level local R3 reading of the pinned archive, with same-source preliminary acceptance incorporating the Haar normalization correction. The same-source review accepted the general cutoff and pairing results and corrected the higher-dimensional example for arbitrary Haar normalization. The [Lean, read] tags refer to the cited A2 proof bodies. Kernel replay, proof-term dependencies from Main and review of the claimed RH proof remain open at this scope.

#### Lean source map for the Haar pairing

A2 joined archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Paths begin at the archive root. R3 refers to local reading at the specified proof spans. R2 records a definition, statement or dependency interface. R1 records a named pointer. See the reading status in the section.

**Newly read**

| Level | Declaration or use | Full archive path and line span |
|---|---|---|
| R3 | `pairing_phi`, hypotheses, eventual-value uniqueness, four bilinear laws and assembly | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantPairingMirabolicSmooth.lean:22–65` |
| R2 | `uM`, `shearGL`, `piHaar`, `wt`, `coef`, `TwInv`, `JJ`, `EvVal` | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShearGL.lean:20–48` |
| R2 | Product boxes, `HasConductor`, the Haar absolute value and the local-field instance for the examples | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCompactSubgroupSmallAnnihilator.lean:14–46`; `lean/src/Development/AbelianVarietyTheory/Definitions/Foundations/MatrixMeasurableSpace.lean:15–34`; `lean/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean:13–44,66–82` |
| R3 | Continuous character is trivial near zero, then the largest trivial ball from nontriviality and discreteness | `lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AddCharConductorAndHaarIntegersExist.lean:13–76` |
| R3 | Compact integrability and both additive and homogeneous laws at a common threshold | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicEvaluationLinear.lean:13–112`; duplicate coefficient continuity `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicCoefficientContinuous.lean:8–30` |
| R3 | Bounds on conjugated small shears for all scales, left and right fixed-vector neighborhoods, finite right orbit | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShearPreservesBoxMembership.lean:11–137`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothVectorFixedSmallShear.lean:13–133`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShearOrbitFinite.lean:14–120` |
| R3 | Shear on columns, determinant of absolute value one and transport from a frequency twist to the right vector | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShearGLMulVecAndNabsDet.lean:9–29`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicPairingDepthVanishing.lean:15–50` |
| R3 | Coefficient transformation with the two opposite shifts, and conjugation by the Levi matrix | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicCoefficientTranslation.lean:14–74,83–109` |
| R3 | Orthogonality by translation, conductor dual box, weighted Fubini and cancellation by its positive mass | `lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean:54–114`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedBoxIntegralIdentity.lean:9–100` |
| R3 | Uniform preimage-box bound by fixing both vectors, then choosing the identity and substituting `t=c/r` | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicPairingConductorBound.lean:15–81`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicPairingConductorVanishing.lean:10–27` |
| R3 | Enlarging the threshold to contain the translating vector, and the two character laws | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicPairingDepthInduction.lean:16–100` |
| R3 | Product Haar scaling on diagonal matrices and transvections, then set-integral change of variables | `lean/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocallyConstantAddChar.lean:105–146`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SetIntegralInvMulVec.lean:10–40` |
| R3 | Weight fixed by the smaller mirabolic, product of determinant factors, and threshold transported by a matrix bound | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicPairingConductorShift.lean:16–111,117–134` |
| R3 | Compact-open coset representatives, finite-stage nonvanishing using the actual twisted relation space | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompactSetFiniteCosetRepresentatives.lean:6–42`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicTwistedKernelNonvanishing.lean:13–151` |
| R3 | Uniform threshold over a finite right orbit, then contradict finite-stage nonvanishing by the zero case of the cutoff identity | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicPairingConductorExtension.lean:20–120` |
| R3 | Kill the two relation spaces, successive `liftQ` maps and use quotient representatives to prove covariance and left separation | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedInvariantPairingCharacter.lean:14–84` |
| R2 | Algebraic relation space and quotient, last-column character and unnormalized action | `lean/src/Development/AbelianVarietyTheory/Definitions/Foundations/SmoothPartStable.lean:21–26`; `lean/src/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/MirabolicDerivatives/ColMatMulGlEmbMat.lean:41–51,82–86,148–170`; `lean/src/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/MirabolicDerivatives/UnipApplyCastSuccLast.lean:16–29` |

The companion-theory bodies give the mathematical content. Each exported `GlobalTheory.T` delegation used here was traced through the same-named `Statement.lean` import to the above proof, including the depth identity, compact shear orbit, and Fourier cutoff.

**Inherited interfaces and actual consumers**

| Level | Actual use | Full archive path and line span |
|---|---|---|
| R3 inherited, call rechecked | Iteration adds one per twisted step, then ordinary descent preserves the accumulated exponent. The ordinary descent itself consumes joint-kernel detection. | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsSmoothIterPhi.lean:128–171`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantPairingMirabolicVanishing.lean:53–93,101–154` |
| R3 inherited, call rechecked | `nuPair` calls `pair_deriv` with the evaluation pairing at the highest order. The dual quotient and normalized Jacquet extraction follow. | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NuPairOfDerivativesJacquet.lean:67–132` |
| R3 inherited, call rechecked | Complementary-series `nuPair_of` also calls `pair_deriv`, then uses `DerFin` and a simple submodule. The `CuspPairIrr` route feeds the adjacent-pair reducibility input of §12.4.10. | `lean/src/Development/WeilBound/RepresentationTheoryGL/GenericUnitaryGL/ComplementarySeries/NontrivialOfIsIrreducible.lean:57–140`; `lean/src/Development/WeilBound/RepresentationTheoryGL/GenericUnitaryGL/ComplementarySeries/CuspPairIrr.lean:13–16`; `lean/src/Development/WeilBound/RepresentationTheoryGL/GenericUnitaryGL/ComplementarySeries/CuspPair.lean:16–54` |
| R3 inherited | Smooth dual and irreducible quotient, negative half-modulus of Jacquet, and the conditional dual-reversal bridge | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PairingTwistedDeterminantSubquotient.lean:15–67`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DerivativeJacquetHolds.lean:68–238,250–341`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JmThetaHolds.lean:20–133` |

The two test functions, the affine and higher-dimensional frequency-space representations, and the deletion tests are textbook examples [Expository]. The bounded determinant calculation on their quotients is a check of the production theorem's convention. The actual NuPair consumer uses a smooth irreducible general linear representation and its smooth dual. The $G_4$ segment instance uses Zelevinsky's derivative formula and the cited compact-induction construction. Its coefficients were not identified with the test functions.

**Named retained inputs**

| Level | Boundary | Full archive path and line span |
|---|---|---|
| R2 [Lean] | Joint-kernel Fourier detection for the highest-order choice and the final ordinary step. The one-step proof uses only the conductor indicator identity, read above. | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirabolicFourierExpansion.lean:74`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsNontrivialDerivative.lean:80–92`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantPairingMirabolicVanishing.lean:59–71` |
| R2 [Lean] | Irreducible admissibility, smooth dual irreducibility and Jacquet finite length in the consumer. | `lean/src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IrreducibleAdmissibleGL.lean:10–13`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NuPairOfDerivativesJacquet.lean:82–97`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DerivativeJacquetHolds.lean:321–322` |
| R2 [Lean] | Whittaker dimension bound, heredity and cuspidal genericity in the adjacent-reducibility argument | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ReducibleCuspidalPairNongenericSubquotient.lean:116–140`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerHeredityStatement.lean:7–8`; `lean/src/Development/WeilBound/RepresentationTheoryGL/GenericUnitaryGL/WhittakerCuspidal/WhitCuspOfSegCuspGeneric.lean:14–19` |
| R1/R2 [Open] | General distributional Gelfand–Kazhdan and full local Langlands. The misleading local-Langlands wrapper in the consumer supplies GKLocal. | `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalLanglandsOfIrreducibleAdmissible.lean:13–17`; `lean/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EquivContra.lean:97` |
| R1/R2 | Mathlib foundations for integration, topology of units, matrix induction and quotient constructors are used at their interfaces. | Named calls in `lean/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocallyConstantAddChar.lean:105–146`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedBoxIntegralIdentity.lean:48–62`; `lean/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedInvariantPairingCharacter.lean:55–83` |
The one-step mirabolic pairing and its Haar inputs are traced in the [§12.4.11 source map](#lean-source-map-for-the-haar-pairing).


- **P15, Chapter 12, §12.4.11.** Use shrinking frequency boxes and growing column boxes to produce the mirabolic pairing. Prove stabilization by small shears and conductor orthogonality, then descend to both twisted Jacquet quotients. The examples compute Haar mass and determinant scaling over $\mathbb Q_3$. [Section](../chapters/12-galois-representations-and-local-langlands.md#12411-from-a-conductor-ball-average-to-the-mirabolic-pairing)

- **P15, §12.4.11, scoped R3.** The conductor cutoff, fixed-vector shear identity and finite-orbit separation give the eventual pairing with covariance $\nu^{s+1}$. `pair_iter` and `pair_deriv` use this one-step result. The ordinary final step, joint-kernel detection and general GK retain their recorded standing. [Production map](../chapters/12-galois-representations-and-local-langlands.md#12411-from-a-conductor-ball-average-to-the-mirabolic-pairing)
### Chapter 12, §12.4.11 · The mirabolic Haar and conductor pairing

- **Alpöge–Claude A2.** SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The companion-theory bodies establish the uniform conductor cutoff, eventual-value pairing, and its covariance and descent. [Full paths and original-source attribution](../chapters/12-galois-representations-and-local-langlands.md#12411-from-a-conductor-ball-average-to-the-mirabolic-pairing)
- **Bernstein–Zelevinsky I**, DOI 10.24033/asens.1333, pp. 443–445, 450–453, 454–456. The authors give normalized localization, module-pairing descent and the highest derivative application. PDF SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`, retrieved 2026-11-26. [Numdam](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0.pdf)
- **Bernstein–Zelevinsky (1976)**, DOI 10.1070/RM1976v031n03ABEH001532, English pp. 44–48. The authors identify Fourier stalks and the unnormalized mirabolic sequence. Translation PDF SHA-256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`, retrieved 2026-11-26. [English text](https://www.uni-muenster.de/imperia/md/content/theoretische_mathematik/topologie/bernstein-zelevinsky.pdf)
- **Zelevinsky II**, pp. 180–182, and **Adrian–Liu v4**, pp. 5–6, supply the actual segment example and its cuspidal seed, with the references and hashes listed under §12.4.10. The LUMI guide supplies chapter context on partial local Langlands. [Pinned community guide](https://github.com/aapolipponen/rh-lean-check-lumi/blob/c6d0e2bc06ae4562d6656c6ef118739670d19eeb/docs/05-galois-representations.md#L37)
- **Chapter 12, §12.4.11.** Hongmin Li with AI assistance gives a textbook reading of the Alpöge–Claude conductor-box proof, explicit local examples and a normalization comparison with Bernstein–Zelevinsky. The section traces the classical pairing to the existing NuPair consumer. [Section](chapters/12-galois-representations-and-local-langlands.md#12411-from-a-conductor-ball-average-to-the-mirabolic-pairing)

## 12.5 Remarks, formalization notes, and Masullo's counterpart

### 12.5.1 Comparison with Harris–Taylor, Henniart, Shin, and Caraiani

| Aspect | Classical published theorems | Lean archive (`Row0b` & `RecTExists`, P14–P15) |
|---|---|---|
| **Local Langlands for $\mathrm{GL}_n(E_w)$** | Full bijection uniquely pinned down on all supercuspidals by local $\gamma$/$\varepsilon$-factors of pairs (`[HarrisTaylor2001]`, `[Henniart2000]`, `[BushnellKutzko1993]`). | `RecTExists` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:78`): 12-clause `LawsT`, pinned down on `Good` (toral + twists of $\mathbb Q_g$ depth-zero cuspidals via `TypeLaw`); wild positive-depth supercuspidals satisfy only dimension, irreducibility, norm-twist, and $\lvert\omega\rvert$ `[Lean, read]`. |
| **Global Galois attachment ($E$ CM)** | Attached for all regular algebraic conjugate-self-dual cuspidal $\pi$ on $\mathrm{GL}_a(\mathbb A_E)$ (`[HarrisTaylor2001]`, `[ClozelHarrisTaylor2008]`, `[Shin2011]`). | `Row0b` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69`): continuous semisimple $r : G_E \to \mathrm{GL}_a(\overline{\mathbb Q}_\ell)$ with exact Hodge–Tate weights `(a-1)/2 - z` and conjugate purity `HT(τ∘c) = wt - HT(τ)` `[Lean, read]`. |
| **Local–global compatibility ($w \nmid \ell$)** | Full Frobenius-semisimplified Weil–Deligne isomorphism including monodromy $N$ at all places $w \nmid \ell$ (`[Shin2011]`, `[Caraiani2012]`). | `AwayB` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:26`): exact equality on `Tor` with $N = 0$; inertia charpoly + $N = 0$ on tame squarefree parameters over $\mathbb Q_g$ ($g > 16a^2$); dimension only when $N \neq 0$ `[Lean, read]`. |
| **Local–global compatibility ($w \mid \ell$)** | Potentially semistable everywhere above $\ell$, crystalline at spherical places, full WD match (`[Caraiani2014]`). | `AboveB` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:39`): crystalline + de Rham + HT jumps at spherical places; de Rham + pst + `AwayB` in `Tor` or tame $\mathbb Q_g$ cases with $N = 0$ `[Lean, read]`. |

*(Non-vacuity check on `AboveB`.)* Notice that `PropsB.above` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:64`) quantifies over
period-ring data `∀ P AI, Nonempty (LocTied l P AI) → ...`; community vacuity audits (`LUMI doc 05` &
`vacuity-check.md` [Community]) verified that `GlobalTheory.MemLoc.exists_locPrime_tied`
(`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281` `[Lean]`)
proves `LocTied` is inhabited, so `AboveB` is genuinely non-vacuous! The prime-wise choices and their use at an actual index and place are followed in [§6.4.23](06-stepanovs-method-and-multiplicity.md#local-record-inertia-polynomial).

### 12.5.2 Masullo's counterpart: $\mathrm{GL}_1$ Tate theory in Chapter 3 vs. higher-rank Langlands

Comparing Chapter 12 with Masullo's *The Music of the Primes* highlights the sharpest structural divide
between the two November 2026 manuscripts [Paper; Masullo pp. 117–154, 302–310, 536]:

- **Masullo stays entirely inside $\mathrm{GL}_1$ (Tate's thesis `[Tate1967]`):** In **Chapter 3
  ("Idelic Zeta Functions", pp. 117–154)** — covering Riemann surfaces of continuous quasi-characters
  (§3.1, pp. 118–121), global idelic zeta functions (§3.2, pp. 122–127), $S$-local idelic zeta functions
  (§3.3, pp. 128–140), and eigendistributions / Weil's identity (§3.4, pp. 141–154) — together with
  **Section 6.3 ("Local and Global Converse Theorems", pp. 302–310)**, Masullo works exclusively on
  the abelian idele group $\mathrm{GL}_1(\mathbb A_F)$ and idele class group $C_F = \mathrm{GL}_1(\mathbb A_F)/F^\times$
  [Paper; Masullo pp. 117–154, 302]. In the language of `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:58`, all of Masullo's
  representation theory sits inside the single $n = 1$ clause `LawsT.one` (local and global class field
  theory / Pontryagin duality on abelian locally compact groups), with zero $\ell$-adic Galois
  representations and zero Shimura varieties!
- **Higher rank left open in §14.3 (p. 536):** At the very end of his manuscript (**Section 14.3,
  "The higher rank case", p. 536**), Masullo remarks briefly that extending his orbital Hardy–Sobolev
  trace-formula framework from $\mathrm{GL}_1(\mathbb A_F)$ (Hecke $L$-functions) to $\mathrm{GL}_n(\mathbb A_F)$
  ($n \ge 2$, standard automorphic $L$-functions, i.e. ERH / Grand Riemann Hypothesis) remains a future
  direction [Paper; Masullo p. 536]. Conversely, Alpöge's proof of **$\mathrm{GL}_1$** GRH (for Dirichlet
  $L$-functions!) climbs all the way up to $\mathrm{GL}_a$ over CM fields with $a = r_0 + m t \asymp x^{9/2 + O(\varepsilon)}$
  in order to manufacture $m \asymp \sqrt{x}$ layers of Stepanov multiplicity!

---

## 12.6 Lean counterpart for this chapter

The [§12.4.11 Lean source map](#12411-from-a-conductor-ball-average-to-the-mirabolic-pairing) follows the conductor cutoff, the pairing on the two twisted Jacquet quotients and their use in NuPair.

| Declaration | File:line | Mathematical content / role in Sections 12.3–12.4 | Tag |
|---|---|---|---|
| `GoodCusp`, `Good`, `Toral`, `TypeLaw`, `LawsT`, `IsRecT`, `RecTExists`, `RecTUnique`, `AbConverse`, `lawsT_of_laws`, `isRecT_of_isRec` | `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:20,24,26,35,55,76,78,82,87,91,106` | Definition 12.1: defines `Good` / `Toral` representations, depth-zero Green inertia `TypeLaw`, the 12-clause partial local Langlands structure `LawsT`, and `RecTExists` (import cone 1,063). | [Lean, read] |
| `UpperTheory.Zero.LLC.recTExists` | `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20` | Proposition 12.1: proves `RecTExists` from local Artin reciprocity `artEx`, supercuspidal seeds `cuspEx`, and Langlands multisegments `exists_isLExt` (top file `R3`; 26,672-module cone `[Lean]` / `[Open]`). | [Lean, read] |
| `IsQpBig`, `IsQpBig.isQp`, `AwayB`, `Away.big`, `AboveB`, `PropsB`, `Row0b`, `Props.big`, `Row0.row0b` | `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:15,18,26,33,39,54,69,75,84` | Definition 12.2 & Proposition 12.3: CM automorphic $\ell$-adic Galois representation predicate `Row0b` with Hodge–Tate weights and weak local–global compatibility `AwayB` / `AboveB` (cone 3,150). | [Lean, read] |
| `UpperTheory.One.M.recT`, `UpperTheory.One.M.Row`; `Unl1`, `PotUnl`, `WitA`, `RowT`, `PlainRec`, `ARead`, `aRead_of` | `src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean:4,6`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean:19,23,27,47,49,98,105` | Definition 12.2 & Proposition 12.2(1): aliases `Row` / `RowT` for `Row0b recT` and proof `aRead_of` upgrading `AwayB` to exact Weil–Deligne equality on `Tor` + `mono0` places. | [Lean, read] |
| `galoisLocalGlobalStrong_recParameter`; `galoisRepresentations_of_thetaLift`; `coreAll_of`, `rest`, `galoisLocalGlobal_of_geometry_lift`, `galoisLocalGlobalStrong_of_geometry_lift` | `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`; `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GaloisRepresentationsOfThetaLift.lean:6`; `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean:20,24,27,30` | Proposition 12.3: top-level spine proving `Row0b recT` from `geoOne_holds`, `wtLacEx_holds`, and `tLiftK` (top files `R3`; 66,167-module cone `[Lean]` / `[Open]`). | [Lean, read] |
| `weight_one_geometric_realization`, `geoOne_holds`; `UpperTheory.TP.K.tLiftK` | `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean:7,11`; `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean:4` | Proposition 12.3 & Section 12.4.4: odd-rank Kuga–Sato / algebraic holomorphic Lefschetz seed (`geoOne_holds`, cone 45,859) and stable-range definite-unitary theta lift (`tLiftK`, cone 20,485) (top wrappers `R3`; internal cones `[Open]`). | [Lean, read] |
| `everyCharacter_of_row`, `everyCharacter`, `riemannHypothesis` | `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7,10,13` | Proposition 12.2(2): master root assembly passing `Row0b recT` and `recTExists` into `OpenLiteratureStatements` and `vwin_of_row` (cone 175,173). | [Lean, read] |
| `exists_locPrime_tied` | `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281` | Section 12.5.1: inhabits Fontaine period-ring tie `LocTied`, confirming non-vacuity of `PropsB.above` (`[Community]` vacuity check). | [Lean] |

**Summary of the chapter.** In `MainConclusion.lean`, the entire archive reduces to two foundational
theorems: `RecTExists` (node **P15**) and `Row0b recT` (node **P14**) [Lean, read]. Instead of
formalizing wild supercuspidal $\varepsilon$-factors or nearby-cycle monodromy $N \neq 0$, `LawsT`
(`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:55`) pins down local Langlands on `Good` representations (built from characters
and $\mathbb Q_g$ depth-zero Green cuspidals) and extends by Langlands multisegments (`recTExists`,
Proposition 12.1), while `PropsB` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:54`) universally quantifies over every
`IsRecT` map to assert exact Weil–Deligne matching on `Tor` ($N = 0$) places and crystalline/pst
Hodge–Tate jumps above $\ell$ (`aRead_of`, Proposition 12.2) [Lean, read]. Inside the 66,167-module
cone of `RowSrc.lean`, odd-rank seed representations arise from Kuga–Sato étale cohomology and an
algebraic holomorphic Lefschetz trace comparison over $\mathbb C$, extend to all odd-rank weights by
$\ell$-adic congruences and pseudo-characters, and cover even ranks via two disjoint stable-range theta
lifts (`TLiftK`) [Community], `[Open]`. How `OpenLiteratureStatements` fans `Row0b` and `RecTExists`
out into Green's finite-general-linear theorem and ~250 named classical propositions — and how human
auditors verify statement fidelity — is the subject of **Chapter 13**.
