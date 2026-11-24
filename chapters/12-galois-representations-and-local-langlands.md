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
6. *The denominator.* Choose a form $f_0$ of degree $n$ that vanishes neither at the generic point nor at any point of $S\cup T$ (<code>EtProj.exists_form_genericPoint_cxPts</code>, [Lean]). Classically this is an avoidance argument over the infinite field $\mathbb C$.

Now we verify (i)–(iii).

*Property (i).* Let $z$ be a complex point at which $f_0$ and all $F_j$ vanish. If $z\in D(h)$, then $z\in T$ by step 4, which contradicts the choice of $f_0$. If $h(z)=0$, then $g_j(z)=F_j(z)-c_jh(z)=0$ for all $j$, so $z\in S$ by step 1, again a contradiction. Hence the open set $D(f_0)\cup\bigcup_jD(F_j)$ contains every complex point. On a scheme of finite type over $\mathbb C$, an open set containing all complex points is the whole scheme (<code>MaxPt.eq_top_of_forall_cxPts_mem</code>, [Lean]). The generic point lies in each $D(F_j)$ because $c_j\ne a_j$.

*Property (ii).* Let $y\in S$. Then $f_0(y)\ne0$, and $h/f_0\in\mathfrak m_y^2$ gives $h(y)=0$. Since also $g_j(y)=0$, we get $F_j(y)=0$.

*Property (iii).* Let $z\in D(f_0)$ be a complex point at which all $F_j/f_0$ vanish. If $z\in S$, step 1 says that the $g_j/f_0$ span the cotangent space. Since $F_j/f_0=g_j/f_0+c_j\,h/f_0$ and $h/f_0\in\mathfrak m_z^2$, the $F_j/f_0$ span it as well. If $z\notin S$, then $h(z)\ne0$, since otherwise $z\in S$ as in (i). So $z\in D(h)$, and by step 4 the $F_j/h$ have a transversal zero at $z$. The ratio $h/f_0$ is a unit near $z$ and $F_j/f_0=(F_j/h)(h/f_0)$, so the $F_j/f_0$ have a transversal zero at $z$ as well (<code>EtProj.span_ratio_of_span_ratio</code>, [Lean]). $\square$

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
| <code>EtProj.Transv.exists_forms_transversal</code>, <code>exists_transversal_forms_first_separate</code>, <code>mem_ptsIn_fOpen_iff</code>, <code>evHom_fRatio_eq_zero_iff</code>, <code>frac_smul_deg</code>, <code>fRatio_add_smul</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFormsTransversalAtComplexPoints.lean:22–75,83–226,234–258</code>; statement <code>ExistsFormsTransversalAtComplexPointsStatement.lean:7–17</code> | Lemma 2. R3 [Lean, read] for the bodies. Of the six named inputs, the jet forms, the Sard step and the finiteness of the transversal zeros are read in the following subsections; three stay at statement level. |
| <code>EtProj.isFinCover_of_forms</code>, <code>isFinite_formMap</code>, <code>isCoordFamily_fRatio</code>, <code>formMap_preimage</code>, <code>rat_formMap</code>, <code>exists_finCover_of_isFinite</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSmoothFiniteCoverOfFormsNoCommonZero.lean:29–175</code>; statement <code>IsSmoothFiniteCoverOfFormsNoCommonZeroStatement.lean:8–9</code> | Lemma 1. R3 [Lean, read] for the bodies; chart inputs at statement level. |
| <code>isReduced_quotient_of_artinian_of_maximal_le</code>, <code>quotient_maximal_le_sq</code>, <code>pow_eq_self_of_le_sq</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsReducedQuotientOfArtinianOfMaximalLe.lean:7–77</code> | Lemma 4. R3 [Lean, read]. |
| <code>MaxPt.exists_cxPts_ker_eq</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplexPointKerEvalEqMaximal.lean:13–44</code> | Lemma 5. R3 [Lean, read]. |
| <code>isArtinianRing_fib_quot</code>, <code>finite_quotient_of_integral</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsArtinianRingFibQuot.lean:7–96</code> | Artinian fibre ring. R3 [Lean, read]. |
| <code>fOpen</code>, <code>fRatio</code>, <code>fRatio_self</code>; <code>IsAffCover</code>, <code>ffAlg</code>; <code>IsProjOver</code>, <code>PSpace</code>; <code>IsFinCover.of_charZero</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FRatioSelf.lean:16–29</code>, <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/IsAffCoverSpec.lean:64–65,79–84</code>, <code>src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsCompletedStrictHens.lean:16–23</code>, <code>src/Development/AbelianVarietyTheory/Definitions/Divisors/DlogRatioVolumeFormNeZero.lean:103–107</code> | Definitions and the characteristic-zero constructor. Read. |
| <code>etaleCorrespondence_fieldExtension_statement</code>, <code>red_of_fu</code>, <code>fin_quot</code>, <code>upB_fu</code>, <code>map_upB_span_tco</code>; <code>SepIdem.formallyUnramified_of_isReduced</code> | <code>src/Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCorrespondenceFieldExtensionStatement.lean:9–209</code>, <code>src/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormallyUnramifiedOfIsReduced.lean:7–17</code> | The proposition. R3 [Lean, read]; <code>isFinCover_pull</code>, <code>mem_rB_pull</code> and <code>rA_finite</code> at statement level. |
| Actual call | <code>src/Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/HolomorphicLefschetzFiniteEtaleIntegral.lean:103–139,156,198,206–225</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/TraceEqZeroOfBot.lean:52–65</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/ResidueOfTraceIsFiberSum.lean:26–40</code>, <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PFieldLe.lean:216–221,323</code> | From the target fibre to <code>Y1.red</code>, <code>orig</code> and <code>off</code>, and on to <code>RedFib</code>. Prior R3 (1123n, 1124a), rechecked for these lines. |

R3 covers the named bodies. The following are used at their interfaces.

- Three inputs of Lemma 2: <code>MaxPt.eq_top_of_forall_cxPts_mem</code>, <code>EtProj.span_ratio_of_span_ratio</code> and <code>EtProj.exists_form_genericPoint_cxPts</code>. The other three are read later: <code>EtProj.Jets.exists_jet_forms</code> (jets and base locus) in the [jet forms](#forms-with-prescribed-jets-at-finitely-many-points), <code>AlgSard.main</code> (the Sard step) in the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets), and <code>TransvZeros.finite_transv_zeros</code> (finiteness of the transversal zeros) in [why the transversal zeros are finite](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes).
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

*Step 2, the reference chart.* Choose a linear form $g_0$ that vanishes neither at the generic point nor at any point of $S$ (<code>EtProj.exists_form_genericPoint_cxPts</code>, used at its statement; classically, a linear form avoiding finitely many points of $\mathbb P^N$). Put $a=g_0^{\,n}$; then $D(a)=D(g_0)$ is affine and contains $S$. For $y\in S$ and $u\in\mathfrak m_y\subset\Gamma(X,D(a))$, Lemma 3(c) with $k=n-1\ge|S|$ produces $g\in V_S(n)$ with $u-g/a\in\mathfrak m_y^2$. So Lemma 4 applies: for each $y\in S$ the jet map $J_y:V_S(n)\to\Gamma(X,D(a))/\mathfrak m_y^2$ has range equal to the image of $\mathfrak m_y$, of dimension $d$.

*Step 3, the induction.* We show for $k\le d$: there are $c_1,\ldots,c_k\in V_S(n)$ such that (α) no $c_i$ vanishes at the generic point; (β) every point $x\notin S$ lying in $V(c_1,\ldots,c_k)$ has coheight at least $k$; (γ) for every $y\in S$ the jets $J_y(c_1),\ldots,J_y(c_k)$ are linearly independent. For $k=0$ there is nothing to prove. Suppose $c_1,\ldots,c_k$ are found and $k<d$. Let $Z=V(c_1,\ldots,c_k)\cap X$, a closed set, and let $T$ be the finite set of generic points of its irreducible components (<code>Generic.exists_finite_gen</code>, from <code>NoetherianSpace.exists_finite_set_isClosed_irreducible</code>; [Stacks 0052](https://stacks.math.columbia.edu/tag/0052)). Consider the following subspaces of $V_S(n)$:

- $V_S(n)_\xi$ for the generic point $\xi$ of $X$; this is proper by Step 1, since $\xi\notin S$ when $d>0$ (<code>hgenS</code>: at a complex point whose underlying point is $\xi$, every section vanishing there is zero by integrality, <code>eq_zero_of_generic</code>, while a cotangent basis element is a nonzero section);
- $V_S(n)_t$ for each $t\in T\setminus S$; proper by Step 1;
- $J_y^{-1}\bigl(\operatorname{span}(J_y c_1,\ldots,J_y c_k)\bigr)$ for each $y\in S$; proper because the range of $J_y$ has dimension $d>k$.

A vector space over an infinite field is not a finite union of proper subspaces (<code>Submodule.exists_forall_notMem_of_forall_ne_top</code>, Mathlib). Choose $c_{k+1}\in V_S(n)$ outside all of them. Then (α) holds for $c_{k+1}$, and (γ) holds by the choice outside the third family (<code>linearIndependent_fin_snoc</code>). For (β), let $x\notin S$ lie in $Z\cap V(c_{k+1})$. Some $t\in T$ specializes to $x$. If $t\in S$, then $t$ is a closed point and $x=t\in S$, which is excluded. So $t\notin S$, hence $t$ has coheight at least $k$ by (β) for $k$, and $t\in D(c_{k+1})$ by the choice outside the second family while $x\notin D(c_{k+1})$. Thus the specialization $t\rightsquigarrow x$ is strict, and the coheight of $x$ is at least that of $t$ plus one (<code>Generic.coheight_step</code>, from <code>Order.coheight_add_one_le</code>), that is, at least $k+1$.

*Step 4, the forms.* Take $c_1,\ldots,c_d$ from Step 3 with $k=d$ and put $g_j=c_j$. Let $Z=V(g_1,\ldots,g_d)\cap X$ and let $T$ be the generic points of its components. By Step 1, the subspaces $V_S(m)_t\subset V_S(m)$ for $t\in T\setminus S$ are proper; choose $q\in V_S(m)$ outside all of them, and put $h=q^2$, a form of degree $n$.

*Verification.* Clause 1 is (α). Clause 2 holds because $g_j\in V_S(n)$. For clause 3, let $z$ be a complex point with $h(z)=0$ and all $g_j(z)=0$, and suppose its underlying point $x$ is not in $S$. Then $x\in Z$; pick $t\in T$ with $t\rightsquigarrow x$. If $t\in S$ then $x=t$, excluded. Otherwise $q\notin\mathfrak p_t$, so $h\notin\mathfrak p_t$ and $t\in D(h)$, while $x\notin D(h)$; by (β) the coheight of $t$ is at least $d$, so that of $x$ is at least $d+1$, contradicting the bound $d$. Hence $x\in S$, and then $z\in S$ by <code>pt_inj</code>. For clause 4, fix $y\in S$ and $f_0$ of degree $n$ with $f_0(y)\ne0$. First, $h/f_0=q^2/f_0\in\mathfrak m_y^2$ by Lemma 5, since $q\in V_S(m)$. Second, in the reference chart $D(a)$ the $d$ classes $J_y(g_1),\ldots,J_y(g_d)$ are linearly independent in the $d$-dimensional range of $J_y$, hence span it (<code>Submodule.eq_of_le_of_finrank_eq</code>). Since the range is the image of $\mathfrak m_y$, every $u\in\mathfrak m_y$ satisfies $u\equiv\sum_jb_j\,g_j/a$ modulo $\mathfrak m_y^2$, that is, $\mathfrak m_y\subset(g_1/a,\ldots,g_d/a)+\mathfrak m_y^2$ in $\Gamma(X,D(a))$. Finally the denominator is changed from $a$ to $f_0$ (<code>EtProj.span_ratio_of_span_ratio</code>, used at its statement): if the spanning relation holds in $\Gamma(X,D(a))$ for a point $y\in D(a)\cap D(f_0)$, it holds in $\Gamma(X,D(f_0))$ for the ratios $g_j/f_0$. Classically, on $D(a)\cap D(f_0)$ one has $g_j/f_0=(g_j/a)\cdot(a/f_0)$ with $a/f_0$ a unit near $y$, and both rings have the same local ring at $y$; the archive's proof of this transport is not read here. $\square$

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
- The following are used at their statements and not read here: the cotangent basis <code>CotDim.exists_cotangent_basis</code>, the coheight bound <code>AffineCover.coheight_le_of_smooth</code>, the avoidance form <code>EtProj.exists_form_genericPoint_cxPts</code>, the denominator change <code>EtProj.span_ratio_of_span_ratio</code>, the algebra lemma <code>exists_linear_mod_sq</code>, and the linearity of ratios <code>fRatio_linear</code>. The finite projection keeps the level recorded in the previous subsection; the Sard step is read in the [Sard step](#the-sard-step-translation-parameters-that-keep-the-jets).

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
| <code>EtProj.exists_form_genericPoint_cxPts</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsProjFormNonvanishingGenericPointComplexPoi.lean:32–34</code> | Form avoiding the generic point and $S$. Statement level [Lean]. |
| <code>EtProj.span_ratio_of_span_ratio</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/RatioSpanCotangentChangeDenominator.lean:47–58</code> | Change of denominator in the spanning clause. Statement level [Lean]. |
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

The existence of charts has two parts, both read (<code>exists_etale_coords</code>, <code>exists_of_etale</code>). First, smoothness of relative dimension $d$ gives, around every point, an affine open on which the structure map is standard smooth, and then $d$ sections forming an étale map to $\mathbb A^d$ (Mathlib's <code>RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial</code>, a corollary of <code>Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial</code>; classically [Stacks Project, Lemma 29.37.21](https://stacks.math.columbia.edu/tag/054L)). Second, at a complex point the étale coordinates have a holomorphic local inverse whose composite with every section is holomorphic. This is a holomorphic implicit function theorem for étale algebras (<code>EtaleFamily.exists_holomorphic_sections</code>, used at its statement), followed by the passage from holomorphy on the affine $U$ to holomorphy of every section on every open (<code>CxPts.holo_of_affine</code>, read: write a section on a basic open as $a/r^n$). Classically, these charts express that a smooth point of a complex variety is a manifold point of the associated analytic space. In GAGA a point of an analytic space is *simple* when the space is isomorphic to $\mathbb C^n$ near it, equivalently when its analytic local ring is regular ([GAGA, §1, no. 4, p. 6](https://doi.org/10.5802/aif.59)), and the algebraic and analytic local rings of a variety have the same completion (§2, no. 6, Proposition 3, pp. 9–10). Serre's own *algebraic charts* are a different notion. They are biregular isomorphisms of Zariski-open sets onto locally closed subsets of an affine space, possibly singular, and Proposition 2 of §2, no. 5 (p. 8) makes them analytic using only that polynomials are holomorphic (Lemma 1 there), with no implicit function theorem. In this subsection they correspond to the embedding of Lemma 1, not to <code>AlgChart</code>.

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
- The following are used at their statements and not read here: the holomorphic implicit function theorem <code>EtaleFamily.exists_holomorphic_sections</code>, the cotangent basis <code>CotDim.exists_cotangent_basis</code>, the basic value lemmas of the point topology (<code>valR_add</code>, <code>valR_mul</code> and their companions), and the Mathlib lemmas listed below. The jet forms, <code>EtProj.exists_form_genericPoint_cxPts</code>, <code>EtProj.span_ratio_of_span_ratio</code> and <code>MaxPt.eq_top_of_forall_cxPts_mem</code> keep the levels recorded in the previous subsections; <code>TransvZeros.finite_transv_zeros</code> is read in the [next subsection](#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes).

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
| <code>EtaleFamily.exists_holomorphic_sections</code> | <code>src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolomorphicSections.lean:74</code> | Holomorphic implicit functions for étale algebras. Statement level [Lean]. |
| <code>CotDim.exists_cotangent_basis</code> | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsCotangentBasis.lean:108–112</code> | Cotangent basis at a complex point of an affine open. Statement level [Lean]. |
| Actual call | <code>src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFormsTransversalAtComplexPoints.lean:100–162,195–201,211–222,226</code> | Consumer. Body read in the reduced auxiliary projection; the Sard call and the choice of $c$ rechecked here. |

Mathlib supplies <code>addHaar_image_eq_zero_of_det_fderivWithin_eq_zero</code> (<code>Mathlib/MeasureTheory/Function/Jacobian.lean:645</code>), <code>measure_biUnion_null_iff</code> (<code>Mathlib/MeasureTheory/OuterMeasure/Basic.lean:107</code>), <code>TopologicalSpace.isOpen_iUnion_countable</code> (<code>Mathlib/Topology/Bases.lean:914</code>), <code>Homeomorph.secondCountableTopology</code> (<code>Mathlib/Topology/Homeomorph/Lemmas.lean:37</code>), <code>Matrix.exists_mulVec_eq_zero_iff</code> (<code>Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean:163</code>), <code>LinearMap.det_eq_zero_iff_ker_ne_bot</code> (<code>Mathlib/LinearAlgebra/Determinant.lean:359</code>), <code>HasFDerivAt.restrictScalars</code> (<code>Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:56</code>), <code>Algebra.FiniteType.iff_quotient_mvPolynomial''</code> (<code>Mathlib/RingTheory/FiniteType.lean:174</code>), <code>MvPolynomial.isNoetherianRing</code> (<code>Mathlib/RingTheory/Polynomial/Basic.lean:935</code>), <code>LocallyOfFiniteType.finiteType_of_affine_subset</code> (<code>Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:51</code>), <code>RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial</code> and <code>Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial</code> (<code>Mathlib/RingTheory/RingHom/StandardSmooth.lean:253,200</code>), <code>MeasureTheory.Measure.pi_hyperplane</code> (<code>Mathlib/MeasureTheory/Constructions/Pi.lean:409</code>) and <code>IsOpen.measure_pos</code> (<code>Mathlib/MeasureTheory/Measure/OpenPos.lean:47</code>); all are cited at their statements.

The [jet forms](#forms-with-prescribed-jets-at-finitely-many-points), the [reduced auxiliary projection](#from-a-general-projection-to-a-reduced-origin-fibre), the [reduced-fibre trace](#from-the-finite-algebra-trace-to-the-reduced-fibre), the [global boundary](#from-fixed-point-vanishing-to-a-global-čech-boundary) and the [local Koszul weights](#from-a-finite-étale-chart-to-the-local-lefschetz-weight) keep the reading levels recorded there.

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
3. *The denominator (line 162).* <code>hfin.toFinset</code> turns $T$ into a finite set, and <code>EtProj.exists_form_genericPoint_cxPts</code> gives a form $f_0$ of degree $n$ that vanishes neither at the generic point nor at any point of $S\cup T$. This avoidance needs a finite set; a nonzero form vanishes on a whole hypersurface.
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
- The following are used at their statements and not read here: Mathlib's <code>set_has_maximal_iff_noetherian</code>, <code>Algebra.FiniteType.isNoetherianRing</code> (Hilbert's basis theorem), <code>LocallyOfFiniteType.finiteType_of_affine_subset</code>, <code>RingHom.FiniteType.of_surjective</code>, <code>RingHom.ker_isMaximal_of_surjective</code>, <code>Ideal.comap_map_of_surjective'</code>, <code>Ideal.map_isPrime_of_surjective</code>, <code>IsAffineOpen.SpecMap_appLE_fromSpec</code> and <code>Set.Finite.of_finite_image</code>, together with the archive's evaluation lemmas <code>CxPts.ev_eq</code> and <code>CxPts.ev_algX</code>, whose definitions are read in the Sard step. The jet forms, the Sard step, <code>EtProj.exists_form_genericPoint_cxPts</code>, <code>EtProj.span_ratio_of_span_ratio</code>, <code>MaxPt.eq_top_of_forall_cxPts_mem</code>, <code>EtaleFamily.exists_holomorphic_sections</code> and <code>CotDim.exists_cotangent_basis</code> keep the levels recorded in the previous subsections.

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
proves `LocTied` is inhabited, so `AboveB` is genuinely non-vacuous!

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
