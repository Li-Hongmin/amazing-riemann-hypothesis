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
and the [global Čech comparison](#from-fixed-point-vanishing-to-a-global-čech-boundary).

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
   reduced fiber there. Pull the affine cover back along $c_1$. In the
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
| `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsFiniteCoverProjSpaceReducedFibreOriginStatement.lean:8–9`, `src/Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCorrespondenceLocalParametersStatement.lean:162–163`, `src/Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCorrespondenceFamilyStatement.lean:160–165` | Named inputs for the reduced fiber, matrix conjugacy and cocycle-level pull–trace comparison [Lean]. |
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
  <code>trace_cechCochain_fraction_eq_sum_fibre</code>.

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
their interfaces. The diagonal supplies <code>ZFam</code>, <code>ZEx</code>,
<code>ZId</code> and <code>PrB</code>, while <code>GMap</code>,
<code>LCupRel</code>, <code>EdgeB</code> and <code>TrLin</code>
supply the join, boundary and trace comparisons. Their inner proofs,
the producers <code>yBig_of</code> and <code>yCmpT_of</code>,
the imported Koszul exactness and local form bases
(<code>koszulExactBelowLengthOfWeaklyRegular_of_htpy</code>,
<code>koszulTwoInjective_of_gl1</code>, <code>koszulThree_of_det</code>,
<code>locForms_of</code>), and the supplier
<code>trace_cechCochain_fraction_eq_sum_fibre</code> are further [Lean]
inputs. The following subsection proves the <code>yCmpG_of</code> comparison under its named chart and column supplies.

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

**Lemma (lifting column primitives).** Let $D=D_C+D_K$ on a finite total complex graded by $(p,q)$, with $D_C$ raising $p$, $D_K$ raising $q$, $D^2=0$, and $D_K=(-1)^p d_K$ in each column. Suppose a total degree $n$ cocycle $w$ has no components in $q>d$. Assume $H^q(d_K)=0$ in every column for $q<d$, and that the $q=d$ component in each column of degree $p=n-d$ is a $d_K$-boundary. Then $w$ is a total boundary.

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

**Why the hypotheses matter [Expository].** On $\mathbb P^1$, take the two standard affine charts with coordinates $t$ and $u=1/t$. The overlap cocycle $\eta=dt/t$ has zero class on restriction to each single chart. For a two-chart cover a boundary has the form $f(u)\,du-g(t)\,dt$. Written in $t$, this is $-f(1/t)t^{-2}dt-g(t)dt$. The first term has powers at most $-2$ and the second powers at least $0$. The coefficient of $t^{-1}dt$ therefore distinguishes $\eta$ from every boundary. Conversely all other Laurent monomials lie in the image, so this quotient is one-dimensional. The affine cover computes $H^1(\mathbb P^1,\Omega^1)$ by the affine-intersection Čech comparison. Even a test by the representative's value at an origin can miss this class: use the chart in $\mathbb P^1$ obtained by removing the point $t=1$, together with the chart obtained by removing $t=0$. With $z=t/(t-1)$, these are the $z$ and $1/z$ affine charts. The same class generator $dz/z$ on the overlap has representative $(z-1)dz/z=dz-dz/z$ whose value at $z=1$ is zero, and whose Laurent coefficient at $z^{-1}dz$ is $-1$. Thus local exactness of restrictions and even a vanishing value on the overlap leave a global obstruction. The lifting lemma removes it only for a compatible total cocycle with the specified column exactness and a primitive at the highest Koszul degree. [Stacks Project, Lemma 30.2.6](https://stacks.math.columbia.edu/tag/01XD)

**The actual consumer.** In <code>yMain_of</code>, Chinese remaindering gives $h$ with values equal to the local quotient at the fixed evaluations and zero elsewhere on the origin fibre. The pulled diagonal is $c'=gY(j_2)(c)$, where $c$ is the chosen diagonal-system cocycle. The test for $s$ comes from <code>ValG</code>; the specialization <code>hsv</code> multiplies the chosen values of $h$ by the nonzero determinants. The combined cocycle $v$ is the <code>c1</code> returned by <code>hBig</code>. At the actual <code>hCG</code> call, the arguments are $h$, $s$, that valuation identity, the combined cocycle and its prescribed component, and the pulled diagonal and its prescribed component. The second boundary is supplied by <code>hCT</code> on restriction to the $T$ indices. Its singleton support condition uses the support of $v$ supplied by <code>YBig</code>. Adding the two boundaries cancels $\operatorname{top}v$ and compares the pulled diagonal to the edge image of the logarithmic representative from the preceding subsection. The reduced-fibre trace and the actual geometric and group-side matching enter later, through the named supplies recorded above.

**Reading and sources.** The proof follows A2, joined archive SHA-256 <code>9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc</code>. See the path and reading-level table below. For the commutative-algebra steps, the Stacks Project gives maximal-ideal localization detection and the Koszul homotopy in homological indexing. The archive uses cochain indexing and checks the twisted coefficients and the two Čech directions explicitly. [Stacks Project, Lemma 10.23.1](https://stacks.math.columbia.edu/tag/00HN) · [Lemma 15.29.5](https://stacks.math.columbia.edu/tag/0626)

| Declaration | A2 source | Reading |
|---|---|---|
| <code>yMain_of</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYMain.lean:111–239</code> | Actual consumer. Lines 209–239 apply <code>hCG</code> and <code>hCT</code> and cancel the middle mixed cochain. Prior R3, rechecked. |
| <code>pyc_local</code> and its local helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYCmpG.lean:11–163</code> | Prior R3, rechecked. Compares normalized degree-$d$ components modulo the parameter ideal. |
| <code>pyc_colZ</code>, <code>collapsed_column_origin</code> and <code>yCmpG_of</code> | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYCmpG.lean:170–366</code> | R3. Normalizes by the homogeneous units, invokes affine detection, checks all singleton pairs, and projects the total boundary. |
| <code>yCols_of</code> and its helpers | <code>src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/LocalMaximality/PYCols.lean:7–151</code> | R3. Assembles admissibility, below-$d$ exactness and all-degree exactness off the origin column. |
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
<code>koszulThree_of_det</code>, <code>yBig_of</code>, <code>yCmpT_of</code>,
<code>GMap</code>, <code>ZFam</code>, <code>ZEx</code>, <code>ZId</code>,
<code>PrB</code>, <code>LCupRel</code>, <code>EdgeB</code> and <code>TrLin</code>
are used through their interfaces in this subsection. The separate
<code>trace_cechCochain_fraction_eq_sum_fibre</code> proof, the geometry of
<code>FixK_holds</code> and the group-side matching
<code>MarkWeightedFixedPointEqDefinitePairOdd</code> and
<code>TraceDefinitePairsEqAutomorphicTrace</code> retain their [Lean] / [Open] status.

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
