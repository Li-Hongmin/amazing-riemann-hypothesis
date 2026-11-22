# Chapter 12. Galois representations and partial local Langlands

> **Status tags used in this chapter:** `[Lean, read]` for declarations and `sorry`-free proof
> bodies read line by line in `MainConclusion.lean`, `WeightsConjBis.lean`, `RecT.lean`,
> `WeakOfAtt.lean`, `RowSrc.lean`, `GaloisRepresentationsOfThetaLift.lean`,
> `IntegralStructures/Development.lean`, `WeightOneGeometricRealization.lean`, `TLiftK.lean`,
> `IsRecTOfIsRec.lean`, and `LocalCentralUnits/RecTExists.lean` (`R3`); `[Lean]` for statement-level
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
theorem in `Main.lean` rests on two foundational existence theorems proved inside the archive**:

1. **Node P14 (`Row0b` / `Row`, `WeightsConjBis.lean:69`, `RowSrc.lean:6`, import cone 66,167 modules):**
   To every regular algebraic polarized (conjugate-self-dual) cuspidal automorphic representation
   $\pi$ of $\mathrm{GL}_a(\mathbb A_E)$ over a CM field $E$, the archive attaches a continuous
   semisimple $a$-dimensional $\ell$-adic Galois representation
   $r : G_E \to \mathrm{GL}_a(\overline{\mathbb Q}_\ell)$ with prescribed Hodge–Tate weights and
   **weak local–global compatibility** (`PropsB`, `AwayB`, `AboveB`) — the formal counterpart of the
   Kottwitz / Clozel / Harris–Taylor / Shin / Caraiani construction `[HarrisTaylor2001]`,
   `[ClozelHarrisTaylor2008]`, `[Shin2011]`, `[Caraiani2012]`, `[Caraiani2014]`.
2. **Node P15 (`RecTExists` / `IsRecT` / `LawsT`, `IsRecTOfIsRec.lean:55,76,78`, `RecTExists.lean:20`, import cone 26,672 modules):**
   At every finite place $w$ of any number field $E$, there exists a map `rc` from irreducible smooth
   representations of $\mathrm{GL}_n(E_w)$ to $n$-dimensional Weil–Deligne representations obeying a
   restricted 12-clause axiom package `LawsT` — a **deliberately weakened partial local Langlands
   correspondence** (compare Harris–Taylor `[HarrisTaylor2001]`, Henniart `[Henniart2000]`, and
   Bushnell–Kutzko `[BushnellKutzko1993]`).

Part III (Chapters 12–13) opens the foundations built inside the archive to inhabit `MainConclusion.lean`.
This chapter examines `Row0b` and `RecTExists`: why weak compatibility and partial local Langlands
suffice for Part II, why universal quantification over `IsRecT h rc` inside `Row0b` keeps their
interaction logically airtight, what `WeightsConjBis.lean` and `IsRecTOfIsRec.lean` state clause by
clause, how `RecTExists.lean` and `IntegralStructures/Development.lean` assemble them at the top
level, and how the 66,167-module Shimura-variety / congruence / even-rank theta-lift proof cone is
organized.

---

## 12.1 Motivation

### 12.1.1 Where Part II actually used Galois representations and local Langlands

Why did an analytic prime-sum bound ever need $a$-dimensional $\ell$-adic Galois representations of
$\mathrm{GL}_a(\mathbb A_E)$ over CM fields [Expository]? Look back at the exact places in Chapters 7,
10, and 11 where `Row0b` and `RecTExists` were consumed:

1. **Along the $m$-step theta-lift chain (Chapters 7 and 10):**
   - In Chapter 7 (`PairLiftOfHoweDualityBernstein.lean:17`, `SiegelEisensteinSecondTermHypotheses.lean:44`),
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
   In `VwinOfRow.lean:4` and `TopMainZj.lean:47,71` [Lean, read], `Row0b` enters as
   `OpenImageCondition.mk h` and `gal : RowT`, supplying:
   - the $2$-dimensional $\mathrm{GL}_2$ Galois representations and local–global compatibility needed
     by Kato's Euler system (`KatoUse`, `KatoUse.lean:15`);
   - the $3$-dimensional (and $\mathrm{GSp}_4$-transferred) Galois representations $\rho : G_K \to \mathrm{GL}_3(\overline{\mathbb Q}_\ell)$
     attached to cohomological forms on $U(3)$ whose Frobenius trace differences build the nonzero
     annihilator integer `NN` in `PropGK` (`KatoUse.lean:36,60`); and
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
  theta-lift chain and in `PropGK` / `WeakOfAtt.lean`, local–global compatibility is needed at
  **spherical (unramified) places** and **abelian/toral Iwahori-level places** (`Tor` with monodromy
  `mono0`, i.e. $N = 0$), plus **depth-zero cuspidal types** inflated from $\mathrm{GL}_n(\mathbb F_g)$
  over $\mathbb Q_g$ (`TypeLaw`, using Green's characters from Chapter 13!).
- **Why weakening `IsRecT` does NOT create a loophole in `Row0b`:** A skeptical reader might worry:
  *"If `IsRecT` leaves `rc` unconstrained on wild supercuspidals, could `recTExists` define `rc` to
  be some trivial dummy map and make `Row0b` vacuously easy to prove?"* Look at the quantifier order
  in `PropsB.away` (`WeightsConjBis.lean:58–59`) [Lean, read]:
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
   (`WeightsConjBis.lean:60–63`) at $a = 1$:
   $$\mathrm{HT}(\tau_0) = \frac{1 - 1}{2} - k = \{-k\}, \qquad
   \mathrm{HT}(\tau_0 \circ c) = \frac{1 - 1}{2} - (-k) = \{+k\} = \{0 - (-k)\},$$
   satisfying `weights_conj` with purity weight $\mathrm{wt} = 0$! Under Weil's $\ell$-adic
   construction (`HeckeLAdicCharacter` via global Artin reciprocity `[Tate1967]`), at every odd split
   prime $p = \varpi \bar\varpi \equiv 1 \pmod 4$ in $\mathbb Z[i]$ (say $p = 5 = (2 + i)(2 - i)$)
   with $p \neq \ell$, the attached $1$-dimensional Galois character $r : G_{\mathbb Q(i)} \to \overline{\mathbb Q}_\ell^\times$
   sends geometric Frobenius at $\mathfrak p = (2 + i)$ (normalized so $(2 + i) \equiv 1 \pmod{2+2i}$)
   to $(2 + i)^{-k} (2 - i)^k \in \overline{\mathbb Q}(i)^\times \hookrightarrow \overline{\mathbb Q}_\ell^\times$,
   matching `LawsT.one` (`rc (.ofChar χ) = lpOfChar (χ ∘ a)`) via `AwayB.tor`!

2. **Rank $a = 2$: testing the three regimes of `AwayB` (`WeightsConjBis.lean:26–32`):**
   Suppose $\pi$ is a regular algebraic polarized cuspidal representation of $\mathrm{GL}_2(\mathbb A_E)$
   (for instance, the base change to $E = \mathbb Q(i)$ of a classical weight-$2$ holomorphic newform
   $f \in S_2(\Gamma_0(N))$ corresponding to an elliptic curve $A / \mathbb Q$, where
   $\frac{a - 1}{2} = \frac{1}{2}$ shifts unitary normalization to arithmetic Hodge–Tate weights
   $\{0, 1\}$ with $\mathrm{wt} = 1$). Look at a prime $w \nmid \ell$ of $E$ and compare what
   `AwayB (wdOf r) (rc (algNorm σ))` asserts in three classical local cases:
   - **Case A — Principal series $\sigma_w = \operatorname{Ind}_B^{\mathrm{GL}_2(E_w)}(\chi_1 \otimes \chi_2)$ (`Toral` $\implies$ `Tor` and `mono0`):**
     Here the cuspidal support consists of two $1$-dimensional characters $\chi_1, \chi_2$ (`y.1 = 1` in
     `Toral`, `IsRecTOfIsRec.lean:26`), and for generic unlinked $\chi_1, \chi_2$ the Weil–Deligne
     monodromy operator vanishes ($N = 0$, i.e. `y.mono0`). Then `AwayB.tor` (`WeightsConjBis.lean:29`)
     fires and gives **full isomorphism of Weil–Deligne representations** `x = y`! In particular, at
     every unramified prime $w$ of norm $q_w$, $r(\mathrm{Frob}_w)$ has exact characteristic polynomial
     $X^2 - a_w(f) X + q_w$!
   - **Case B — Special / Steinberg twist $\sigma_w = \mathrm{St}_2 \otimes \chi$ (`Tor` true, `mono0` false):**
     Classically (Caraiani `[Caraiani2012]`), the Weil–Deligne parameter has $N = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix} \neq 0$,
     corresponding to multiplicative (Tate-curve) bad reduction of $A$ at $w$. Because `y.mono0` is
     **false**, neither `AwayB.tor` nor `AwayB.tame0` fires: `AwayB` asserts **only `x.lpDim = y.lpDim`**
     ($2 = 2$)! The archive deliberately avoids formalizing weight-monodromy on nearby cycles because
     Part II never needs local–global compatibility at Steinberg places!
   - **Case C — Depth-zero supercuspidal at a split rational prime $E_w \cong \mathbb Q_g$ (`g > 16 a^2 = 64`):**
     Suppose $E_w \cong \mathbb Q_g$ ($g > 64$ prime) and $\sigma_w$ is compactly induced from a
     cuspidal Green character $\tau_\theta$ of $\mathrm{GL}_2(\mathbb F_g)$ (`Inflates σ τ` in `TypeLaw`,
     `IsRecTOfIsRec.lean:35–53`, attached to a regular character $\theta : \mathbb F_{g^2}^\times \to \mathbb C^\times$
     with $\theta^g \neq \theta$). Then `TypeLaw` forces `y.mono0` ($N = 0$) and pins down the inertia
     characteristic polynomial on $I_{\mathbb Q_{g^2}}$ as $(X - \theta(z))(X - \theta(z^g))$
     (squarefree since $\theta(z) \neq \theta(z^g)$!), so `AwayB.tame0` (`WeightsConjBis.lean:31`)
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
using *only* its odd-rank theorem plus a stable-range theta lift (`TLiftK`, `TLiftK.lean:4`)? Check
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

### 12.3.1 Partial local Langlands (`IsRecTOfIsRec.lean`)

**Definition 12.1 (`GoodCusp`, `Good`, `Toral`, `TypeLaw`, `LawsT`, `IsRecT`, and `RecTExists`, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:20,24,26,35,55,76,78`).** [Lean, read]

Let $E$ be a number field with algebraic closure $\Omega$, $w$ a finite place of $\mathcal O_E$ with
completion $k := E_w$, and $h : \mathrm{IsPlaceOver}\,A\,w$ ($A \subset \Omega$ a valuation subring above $w$).

1. **The `Good` and `Toral` representation classes (`IsRecTOfIsRec.lean:20–27`):** For an irreducible
   smooth representation $x \in \mathrm{IrrGL}(k)$ of $\mathrm{GL}_{x.1}(k)$:
   - `GoodCusp y` (`:20`): either $\dim(y) = y.1 = 1$ (a smooth character of $k^\times$), **or**
     $k \simeq_{\mathrm{top}} \mathbb Q_g$ ($g$ prime) and $y = y_0 \otimes (\chi \circ \det)$ is a
     character twist of a **depth-zero** supercuspidal $y_0$ (having nonzero invariants under the
     principal congruence subgroup $K_1 = 1 + g M_n(\mathbb Z_g)$: `fixed y₀.rep (KOne k (Fin y₀.1)) ≠ ⊥`);
   - `Good x` (`:24`): $x$ has Bernstein–Zelevinsky cuspidal support $s$ consisting entirely of
     `GoodCusp` representations (`∀ y ∈ s, GoodCusp y`);
   - `Toral x` (`:26`): $x$ has cuspidal support consisting entirely of $1$-dimensional characters
     (`∀ y ∈ s, y.1 = 1`, i.e. subquotients of principal series).
2. **Depth-zero Green-type inertia law (`TypeLaw h rc`, `:35–53`):** Whenever $k \simeq \mathbb Q_g$,
   $E'/E$ is unramified or tamely unramified at $g$ (`g ∉ (w')^2`) with residue field $K \cong \mathbb F_{g^n}$,
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

**Definition 12.2 (`IsQpBig`, `AwayB`, `AboveB`, `PropsB`, `Row0b`, and `Row` / `RowT`, `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:15,26,39,54,69`, `…/SatakeParameters/RecT.lean:6`, and `…/AutomorphyLifting/WeakOfAtt.lean:47`).** [Lean, read]

Fix a local-reciprocity predicate `Rc : RecNotion` (instantiated as `recT := fun h rc => IsRecT h rc`,
`RecT.lean:4`), a CM number field $E$ with maximal real subfield $E^+$, a prime $\ell$, an isomorphism
$\iota : \overline{\mathbb Q}_\ell \simeq \mathbb C$, and a rank $a \ge 1$.

1. **Local compatibility away from $\ell$ (`IsQpBig`, `AwayB`, `WeightsConjBis.lean:15, 26–32`):**
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
   **`UpperTheory.One.M.Row`** (`RecT.lean:6`) and **`UpperTheory.V.Z.Win.RowT`** (`WeakOfAtt.lean:47`) —
   two identical aliases for `Row0b (fun h rc => IsRecT h rc)`!

---

## 12.4 Lemmas and proofs

We now prove the `R3`-verified top-level theorems in `IsRecTOfIsRec.lean`, `RecTExists.lean`,
`WeightsConjBis.lean`, `WeakOfAtt.lean`, `IntegralStructures/Development.lean`, and `MainConclusion.lean`,
and then map out the 66,167-module internal Shimura-variety / congruence / theta-lift proof cone.

### 12.4.1 Multisegment assembly of partial local Langlands (`RecTExists.lean`)

**Proposition 12.1 (Constructing `RecTExists` from local Artin reciprocity, supercuspidal seeds, and Langlands multisegments).**
*`UpperTheory.Zero.LLC.RecTExists` holds.*
*(Lean: `lawsT_of_laws` and `isRecT_of_isRec`, `…/LocalLanglands/IsRecTOfIsRec.lean:91,106`;
`UpperTheory.Zero.LLC.recTExists`, `…/LocalLanglands/LocalCentralUnits/RecTExists.lean:20`.)* [Lean, read]

*Proof.* Open `RecTExists.lean:20–66` (`R3` for this file; `R2` `[Lean]` for the imported sub-lemmas
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

Next let us verify two crisp `R3` deductions: first, `aRead_of` (`WeakOfAtt.lean:105–114`), which shows
in 9 lines how downstream consumers upgrade `AwayB` to **exact Weil–Deligne equality** `x = rc (algNorm σ)`;
second, `MainConclusion.lean:7–14`, which wires P14 + P15 + P12 + P18 into `EveryCharacter` and `RiemannHypothesis`!

**Proposition 12.2 (Upgrading `AwayB` on unlinked/toral places via `aRead_of`, and closing `MainConclusion.lean`).** [Lean, read]

1. *(`aRead_of`, `WeakOfAtt.lean:105–114`)* *Assume `PlainRec` (`:49–53`, asserting that local components
   $\sigma$ satisfying the window/unlinked condition `WinAt π t w` are `PlainTor`, so `rc (algNorm σ)`
   satisfies `Tor` and `mono0`). Then `ARead` (`:98–103`) holds: for every regular algebraic $\pi$ with
   attached Galois representation $r$ satisfying `WitA ι r` (`:27–30`), at every place $w$ with either
   $w \nmid \ell$ or `Unl1 r w` (flag characters $\kappa_i \neq \kappa_j \chi_{\mathrm{cyc}}$ on $D_w$),
   **every** $x \in \mathrm{WD}(h)$ satisfying `AwayB x (rc (algNorm σ))` satisfies **`x = rc (algNorm σ)`**!*
2. *(`everyCharacter_of_row` and `everyCharacter`, `MainConclusion.lean:7,10`)* *Given `galoisLocalGlobalStrong_recParameter : Row0b recT`
   (`RowSrc.lean:6`) and `recTExists : RecTExists` (`RecTExists.lean:20`), `OpenLiteratureStatements`
   (`EveryCharacterOfLiteratureOfVWin.lean:215`) and `VWin` (`VwinOfRow.lean:4`) are both inhabited,
   proving `UpperTheory.EveryCharacter` and `RiemannHypothesis`!*

*Proof.*
(1) Fix $w$ satisfying $(w \nmid \ell) \vee \mathrm{Unl1}\,r\,w$ (`WeakOfAtt.lean:106`). If $w \mid \ell$,
the first clause of `WitA` (`hW.1`, `:28`) upgrades `Unl1 r w` to `PotUnl r w` (`:110`); thus in both
cases $(w \nmid \ell) \vee \mathrm{PotUnl}\,r\,w$ holds, so the second clause of `WitA` (`hW.2`, `:29–30`)
produces `hwin : WinAt π t w` (`:108–111`). Feeding `hwin` into `PlainRec` (`:112`) yields `h2 : Tor (rc (algNorm σ))`
and `h3 : (rc (algNorm σ)).mono0`. Therefore, for *any* $x$ satisfying `k : AwayB x (rc (algNorm σ))`,
projecting `k.tor h2 h3` (`:113`) gives `x = rc (algNorm σ)` immediately!

(2) Look at `EveryCharacterOfLiteratureOfVWin.lean:215–218` [Lean, read]:
```lean
structure UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop where
  caraianiLocalGlobalDual : _root_.UpperTheory.One.M.Row
  localLanglandsExists : _root_.UpperTheory.Zero.LLC.RecTExists
  galoisRepOfPolarizedPairLit : _root_.UpperTheory.One.M.Row
```
Since `UpperTheory.One.M.Row` (`RecT.lean:6`) is definitionally `Row0b (fun h rc => IsRecT h rc)`, a
single proof `h` of `Row0b recT` fills **both** the first and third fields of `OpenLiteratureStatements`,
while `recTExists` fills the second field: `⟨h, recTExists, h⟩ : OpenLiteratureStatements`
(`MainConclusion.lean:8`)! Simultaneously, Theorem 11.4 (`vwin_of_row h`) produces `VWin`. Passing both
into `every_character_of_literature_of_vWin` proves `EveryCharacter`, and applying it to
`h := galoisLocalGlobalStrong_recParameter` proves `everyCharacter` (`:10–11`)! $\square$

### 12.4.3 Top-level spine of `galoisLocalGlobalStrong_recParameter` (`RowSrc.lean`, `Development.lean`)

Let us read the top four files of node **P14** in full (`R3` / `[Lean, read]`): `RowSrc.lean` (8 lines),
`GaloisRepresentationsOfThetaLift.lean` (8 lines), `IntegralStructures/Development.lean` (33 lines),
`WeightOneGeometricRealization.lean` (13 lines), and `TLiftK.lean` (5 lines).

**Proposition 12.3 (Top-level assembly of `Row0b recT` from Shimura geometry, congruences, and stable-range theta lifts).**
*Assume:*
- *`geoOne_holds : GeoOne` (`WeightOneGeometricRealization.lean:11`, proved from the algebraic
  holomorphic Lefschetz fixed-point formula `lefschetz_fixedPoint_finite_etale_correspondence`, `:7–9`),*
- *`wtLacEx_holds` (lacunary $\ell$-adic weight interpolation, giving `CongFinOdd` via `congFinOdd_of_ex`, `Development.lean:28`), and*
- *`tLiftK : TLiftK` (`TLiftK.lean:4`, stable-range global theta-lift non-vanishing on definite unitary groups).*

*Then `Row0 recT` and `Row0b recT` hold (`galoisLocalGlobalStrong_recParameter`, `RowSrc.lean:6`).* [Lean, read]

*Proof (top-level proof terms in `Development.lean:20–32` and `WeightsConjBis.lean:75–86`).*
1. `seedFinOdd_of_geoOne geoOne_holds` (`Development.lean:28` `[Lean]`) cuts out odd-rank "seed" Galois
   representations from the cohomology of the PEL/Kuga–Sato variety (`GeoOne`).
2. `limFinOdd_of seed cong` (`:22` `[Lean]`) passes to $\ell$-adic congruence limits via `CongFinOdd`,
   and `toCoreK up congPhi_holds descOffT ...` (`:22` `[Lean]`) invokes `up : TLiftK` **once** to extend
   from odd rank to even rank (by the two-lift subtraction trick of Example 12.2.2) and `coreAll_of_core`
   (`:21` `[Lean]`) extends to all CM fields (`CoreAll`).
3. `rest` (`:24–25` `[Lean]`) combines `CoreAll` with spherical local–global compatibility
   (`galoisCompat_unlinkedSupport_of_spherical`) and Iwahori-fixed unlinked compatibility
   (`localGlobalCompatAtIwahoriFixed_of_unlinked`) to inhabit `Row0 recT` (which uses `Away` with
   `IsQp w` in place of `IsQpBig w n`).
4. Finally, `Row0.row0b` (`WeightsConjBis.lean:84–86` `[Lean, read]`) applies `IsQpBig.isQp` (`:18–20`:
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
     (`lefschetz_fixedPoint_finite_etale_correspondence`, `WeightOneGeometricRealization.lean:9` `[Lean]`)
     and transferred to $\ell$-adic étale cohomology by a Faltings-style crystalline Hodge–Tate comparison
     (`PadicHodgeComparison/`, 538 files `[Open]`) [Community]!
2. **All odd-rank forms via $\ell$-adic congruences and pseudo-characters (`CongFinOdd`, `limFinOdd_of`):**
   Following the Bellaïche–Chenevier / Chenevier congruence philosophy `[BellaicheChenevier2009]` on
   compact definite unitary groups (`[ClozelHarrisTaylor2008]`), arbitrary odd-rank weights and types
   are approximated $\ell$-adically by seed forms, and Taylor/Rouquier pseudo-characters reconstruct a
   semisimple limit representation (`exists_limit_rep`), while Kisin-style Breuil–Kisin frame closedness
   (`ClosedAtL`) preserves crystallinity and Hodge–Tate jumps at unramified places above $\ell$ [Community], `[Open]`.
3. **Even-rank reduction (`TLiftK.lean`, cone 20,485):**
   Notice a naming subtlety pointed out by community readers (`LUMI doc 05` [Community]): although the
   top wrapper is named `galoisRepresentations_of_thetaLift`, the stable-range theta lift `tLiftK`
   (proved via Rallis's inner-product doubling method `[Rallis1984]`, `[KudlaRallis1994]`) is used
   **only once**, in `ToCoreK.lean` (`Development.lean:22`), to reduce even rank $a$ to odd rank $a + t$
   by the two-lift character-peeling argument (`TwoUp`, `PeelAll`) of Example 12.2.2!

---

## 12.5 Remarks, formalization notes, and Masullo's counterpart

### 12.5.1 Comparison with Harris–Taylor, Henniart, Shin, and Caraiani

| Aspect | Classical published theorems | Lean archive (`Row0b` & `RecTExists`, P14–P15) |
|---|---|---|
| **Local Langlands for $\mathrm{GL}_n(E_w)$** | Full bijection uniquely pinned down on all supercuspidals by local $\gamma$/$\varepsilon$-factors of pairs (`[HarrisTaylor2001]`, `[Henniart2000]`, `[BushnellKutzko1993]`). | `RecTExists` (`IsRecTOfIsRec.lean:78`): 12-clause `LawsT`, pinned down on `Good` (toral + twists of $\mathbb Q_g$ depth-zero cuspidals via `TypeLaw`); wild positive-depth supercuspidals satisfy only dimension, irreducibility, norm-twist, and $\lvert\omega\rvert$ `[Lean, read]`. |
| **Global Galois attachment ($E$ CM)** | Attached for all regular algebraic conjugate-self-dual cuspidal $\pi$ on $\mathrm{GL}_a(\mathbb A_E)$ (`[HarrisTaylor2001]`, `[ClozelHarrisTaylor2008]`, `[Shin2011]`). | `Row0b` (`WeightsConjBis.lean:69`): continuous semisimple $r : G_E \to \mathrm{GL}_a(\overline{\mathbb Q}_\ell)$ with exact Hodge–Tate weights `(a-1)/2 - z` and conjugate purity `HT(τ∘c) = wt - HT(τ)` `[Lean, read]`. |
| **Local–global compatibility ($w \nmid \ell$)** | Full Frobenius-semisimplified Weil–Deligne isomorphism including monodromy $N$ at all places $w \nmid \ell$ (`[Shin2011]`, `[Caraiani2012]`). | `AwayB` (`WeightsConjBis.lean:26`): exact equality on `Tor` with $N = 0$; inertia charpoly + $N = 0$ on tame squarefree parameters over $\mathbb Q_g$ ($g > 16a^2$); dimension only when $N \neq 0$ `[Lean, read]`. |
| **Local–global compatibility ($w \mid \ell$)** | Potentially semistable everywhere above $\ell$, crystalline at spherical places, full WD match (`[Caraiani2014]`). | `AboveB` (`WeightsConjBis.lean:39`): crystalline + de Rham + HT jumps at spherical places; de Rham + pst + `AwayB` in `Tor` or tame $\mathbb Q_g$ cases with $N = 0$ `[Lean, read]`. |

*(Non-vacuity check on `AboveB`.)* Notice that `PropsB.above` (`WeightsConjBis.lean:64`) quantifies over
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
  [Paper; Masullo pp. 117–154, 302]. In the language of `IsRecTOfIsRec.lean:58`, all of Masullo's
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
| `galoisLocalGlobalStrong_recParameter`; `galoisRepresentations_of_thetaLift`; `coreAll_of`, `rest`, `galoisLocalGlobal_of_geometry_lift`, `galoisLocalGlobalStrong_of_geometry_lift` | `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`; `…/GaloisRepresentationsOfThetaLift.lean:6`; `…/GaloisRepresentations/IntegralStructures/Development.lean:20,24,27,30` | Proposition 12.3: top-level spine proving `Row0b recT` from `geoOne_holds`, `wtLacEx_holds`, and `tLiftK` (top files `R3`; 66,167-module cone `[Lean]` / `[Open]`). | [Lean, read] |
| `weight_one_geometric_realization`, `geoOne_holds`; `UpperTheory.TP.K.tLiftK` | `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean:7,11`; `…/ThetaParseval/ThetaKernels/TLiftK.lean:4` | Proposition 12.3 & Section 12.4.4: odd-rank Kuga–Sato / algebraic holomorphic Lefschetz seed (`geoOne_holds`, cone 45,859) and stable-range definite-unitary theta lift (`tLiftK`, cone 20,485) (top wrappers `R3`; internal cones `[Open]`). | [Lean, read] |
| `everyCharacter_of_row`, `everyCharacter`, `riemannHypothesis` | `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7,10,13` | Proposition 12.2(2): master root assembly passing `Row0b recT` and `recTExists` into `OpenLiteratureStatements` and `vwin_of_row` (cone 175,173). | [Lean, read] |
| `exists_locPrime_tied` | `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281` | Section 12.5.1: inhabits Fontaine period-ring tie `LocTied`, confirming non-vacuity of `PropsB.above` (`[Community]` vacuity check). | [Lean] |

**Summary of the chapter.** In `MainConclusion.lean`, the entire archive reduces to two foundational
theorems: `RecTExists` (node **P15**) and `Row0b recT` (node **P14**) [Lean, read]. Instead of
formalizing wild supercuspidal $\varepsilon$-factors or nearby-cycle monodromy $N \neq 0$, `LawsT`
(`IsRecTOfIsRec.lean:55`) pins down local Langlands on `Good` representations (built from characters
and $\mathbb Q_g$ depth-zero Green cuspidals) and extends by Langlands multisegments (`recTExists`,
Proposition 12.1), while `PropsB` (`WeightsConjBis.lean:54`) universally quantifies over every
`IsRecT` map to assert exact Weil–Deligne matching on `Tor` ($N = 0$) places and crystalline/pst
Hodge–Tate jumps above $\ell$ (`aRead_of`, Proposition 12.2) [Lean, read]. Inside the 66,167-module
cone of `RowSrc.lean`, odd-rank seed representations arise from Kuga–Sato étale cohomology and an
algebraic holomorphic Lefschetz trace comparison over $\mathbb C$, extend to all odd-rank weights by
$\ell$-adic congruences and pseudo-characters, and cover even ranks via two disjoint stable-range theta
lifts (`TLiftK`) [Community], `[Open]`. How `OpenLiteratureStatements` fans `Row0b` and `RecTExists`
out into Green's finite-general-linear theorem and ~250 named classical propositions — and how human
auditors verify statement fidelity — is the subject of **Chapter 13**.
