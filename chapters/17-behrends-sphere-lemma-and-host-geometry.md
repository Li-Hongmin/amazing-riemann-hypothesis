# Chapter 17. Host-field geometry and Behrend's sphere lemma: inside `P5` and `HostOfField`

> **Status tags used in this chapter:** `[Lean, read]` for declarations and `sorry`-free proof
> bodies read line by line in `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean`,
> `src/Lemmata/GeneralBFactSecondLast/Imports.lean`, `src/Formalism/FrobeniusOrbits/HostThickExists.lean`,
> `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean`,
> `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean`,
> `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean`,
> `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean`,
> `src/Formalism/LocalRingCardinality/Params.lean`, `src/Formalism/LocalRingCardinality/DataHost.lean`,
> `src/Development/AutomorphicArithmetic/ThickFrames/MarkedLow.lean`,
> `src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean`,
> `src/Development/AutomorphicArithmetic/ThickFrames/topsChoiceH.lean`,
> `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean`,
> `src/Development/AutomorphicArithmetic/CoprimeRanks/SecondSetNoRelation.lean`,
> `src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean`,
> `src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean`,
> `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/LogConductorMulHeightLeOfPageN.lean`,
> `src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/NoThreeConsecutiveThickPlaces.lean`,
> `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AtMostTwoThickInWindowLongOrbit.lean`,
> `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickSetDensityLeInvFourLw.lean`, and
> `src/Formalism/BehrendSets/FinalE.lean` (`R3`); `[Lean]` for statement-level inspections of
> imported Bernoulli-sampling and prime-supply sub-lemmas (`topsBase`; `shortNorm`, which counts primes
> represented by the norm form `NormOne`; `R2`); the small-prime deduction is read in §17.4.5.
> The exceptional-zero production and weighted-interval budget have their own local reading scope
> in §17.4.10.
>
> `[Paper]` for citations to Alpöge's `remark.pdf` and Masullo's draft; `[Community]` for public
> audit reports; `[Expository]` for classical additive-combinatorial background and worked
> lattice-sphere calculations; `[Open]` only where explicitly noted for external side cones.

In Chapters 4, 5, and 11 we treated the assembly of the concrete `Host R` record (`hostOfField`,
`src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8`) as a black box supplying
the host-side hypothesis `EAtH` of `core_gm` (`P6`) alongside the subexponential conductor-height
inequality `log_conductor_mul_height_le_of_pageN` (`P12`). Opening that box reveals one of the
cleanest, most self-contained gems of classical mathematics in the entire 175,187-file archive:
a **generalized Behrend sphere construction** (`hostThickExists` in
`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:181` and `thickFrame2` in
`src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean:29`), built directly atop
Mathlib's formalization of F. A. Behrend's 1946 theorem `[Behrend1946]`
(`Behrend.exists_large_sphere`, `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:245`)
[Lean, read]!

Every proof in this engine sits in tiny import cones (`0` to `1,314` archive modules) and uses
nothing beyond **strict Euclidean convexity of spheres in $\mathbb Z^S$, carry-free signed base-$B$
expansion, the pigeonhole principle, and the arithmetic-geometric mean inequality**. Better yet,
reading it line by line (`R3`) simultaneously:

1. explains **why** the CM host group $\varphi.\Psi$ must be partitioned into *top*, *thick*, and
   *thin* places (`src/Formalism/LocalRingCardinality/DataHost.lean:129–136`) before the chain-slope and Schur bounds of Part II can
   close;
2. exhibits the exact mechanism by which strict sphere convexity caps every Frobenius progression
   window of length $L_w$ at **at most two thick places** (`hostThickOrbit`, `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean:132`,
   and `LongWindow.main`, `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AtMostTwoThickInWindowLongOrbit.lean:27`) while keeping the thick-set
   cardinality subexponentially close to the full group order ($\lvert T_2 \rvert \ge x^{-\varepsilon}\,\varphi.\mathrm{ord}$);
3. resolves a subtle structural puzzle from `remark.pdf` (p. 4, item 19) [Paper; remark p. 4] and
   early community scans (`LUMI doc 06` [Community]): why Behrend sets were dropped from the
   Iwasawa window pigeonhole of node **P12** (`VWin`), yet remain **load-bearing on the main
   `src/Main.lean` spine** inside host-field assembly (`src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8`)!

---

## 17.1 Motivation

### 17.1.1 Why CM host places split into `topPlaces`, `thickPlaces`, and `IsThin`

Recall from Chapters 4 and 5 how a host field $E \subset \mathbb Q(\zeta_N)$ ($2^{e+2} \mid N$,
$q \equiv 3 \pmod 8$, $d \equiv 7 \pmod{16}$) is organized by its finite Galois frame `φ : Frame`
(`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:15`)
[Lean, read]:

- The core abelian group `φ.A = Fin φ.ord` has order $\varphi.\mathrm{ord} = n \asymp x^{2 + 8\varepsilon}$,
  containing a distinguished cyclic $2$-power subgroup `φ.A0 = ⟨φ.a0⟩` of order
  $n_0 := \operatorname{addOrderOf}(\varphi.a_0) \mid 2^e$ (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean:249`) and bounded index
  $o := \varphi.\mathrm{ord} / n_0 \le C_o$ (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:68–70`).
- Multiplying `φ.MA` (the multiplicative copy of `φ.A`) by the four-element sign group
  $G_0 = \mathbb Z^\times \times \mathbb Z^\times = \{(\pm 1, \pm 1)\}$ tracking the quadratic
  subfields $\mathbb Q(\sqrt{-q})$ and $K = \mathbb Q(\sqrt{-d})$ forms the ambient host Galois
  group `φ.GG = G0 × φ.MA` of order $4\,\varphi.\mathrm{ord}$ (`natCard_GG`, `:137`).
- Inside `φ.GG`, the index-$2$ subgroup `φ.Psi := ker φ.chD` (consisting of elements with second
  sign $+1$, cardinality $f = 2\,\varphi.\mathrm{ord}$, parametrizing the archimedean CM type of $E$!)
  decomposes into **two disjoint sheets** of size $\varphi.\mathrm{ord}$ (`mem_Psi_iff_tau`,
  `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean:136`):
  $$\varphi.\Psi \;=\; \tau_1(\varphi.A) \;\sqcup\; \tau_2(\varphi.A),
  \qquad
  \tau_1(t) = \bigl((+1, +1),\, \iota(t)\bigr),
  \quad
  \tau_2(t) = \bigl((-1, +1),\, \iota(t)\bigr).$$

Now open `src/Formalism/LocalRingCardinality/DataHost.lean:129–136` [Lean, read] and look at how a
host `H : Host R` partitions the $2\,\varphi.\mathrm{ord}$ places of `R.Psi` into **three disjoint
classes**:

1. **`topPlaces := H.TT.image R.tau1` (`:129`):** A subset of the $+1$ sheet $\tau_1(R.A)$ of
   cardinality $\lvert TT \rvert \asymp \delta_1 n = x^{-\varepsilon/8} n$, selected via probabilistic
   Bernoulli sampling (`topsChoiceH`,
   `src/Development/AutomorphicArithmetic/ThickFrames/topsChoiceH.lean:30`) so that it equidistributes
   across prime residue classes (`Shares`) while avoiding bad concentration (`BadOK`). In Chapters 5
   and 6, `topPlaces` carries the high Harish-Chandra weight $a_T$ that detects the Riesz prime sum `ASK`!
2. **`thickPlaces := H.T2.image (fun s => R.tau2 (R.dig s + H.u0))` (`:133–134`):** A translated
   subset inside the $-1$ sheet $\tau_2(R.A)$ (automatically disjoint from `topPlaces` because
   $\tau_1(t) \neq \tau_2(t')$ on the first sign coordinate! `FactTopsThick`, `:195`), indexed by a
   subset $T_2 \subseteq \{1, \dots, \lfloor n_0 / (4 L_w) \rfloor\}$ along the cyclic generator
   orbit $\mathrm{dig}(s) = s \cdot a_0 \in A_0$.
3. **`IsThin g` (`:136`):** Every remaining place $g \in R.\Psi \setminus (\mathrm{topPlaces} \cup \mathrm{thickPlaces})$.

Why does the chain of theta lifts need **both** `topPlaces` and a second "thick" set `thickPlaces`
with delicate additive-combinatorial geometry [Expository]? Follow the two competing pressures on
`H.T2` along the $m$-step chain of Chapters 6–9:

- **Pressure A — Avoiding clustering along Frobenius orbits (upper local-density pressure):**
  When an inert or signal prime $p$ acts on CM places $g \in R.\Psi$ by powers of its Frobenius
  element $\varphi \in R.\mathrm{GG} \setminus R.\Psi$ ($\varphi \neq \mathrm{cc}$), the induced
  place orbit `placeOf (φ^i * τ)` marches along an **arithmetic progression**
  $$i \longmapsto t_0 + i \cdot h \qquad \bigl(t_0 = \iota^{-1}(\tau_2),\ h = \iota^{-1}(\varphi_2) \in R.A\bigr)$$
  (`src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AtMostTwoThickInWindowLongOrbit.lean:20–24`). In the Harish-Chandra and Schur lattice bounds of
  Part II (`win_thick` in `src/Formalism/LocalRingCardinality/DataParams₂.lean:175`, `src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/NoThreeConsecutiveThickPlaces.lean:222`, and
  `LongWindow.main` in `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AtMostTwoThickInWindowLongOrbit.lean:27`), whenever $\varphi$ generates a
  long orbit ($4 L_w < \operatorname{ord}(h)$, where the window length is
  $L_w = \mathrm{Lwv}(s) = \lceil 405\log x \rceil + \lceil 30/\varepsilon \rceil \asymp \log x$),
  **hitting three or more thick places inside a single window of length $L_w$ — or three consecutive
  orbit steps $i, i+1, i+2$ — would cause local slope/weight contributions to pile up linearly in
  $L_w$ and wreck the error brackets of `SizeData₂`!** Even stronger: to rule out *any* three hits
  $i_0 \le a < b < c < i_0 + L_w$ along $t_0 + i \cdot h$, it is **not enough** for $T_2$ merely to
  avoid $3$-term arithmetic progressions ($s_2 - s_1 = s_3 - s_2$, corresponding to $c - a = 2(b - a)$)!
  Cross-multiplying $(b - a)(s_c - s_a) = (c - a)(s_b - s_a)$ requires $T_2$ to avoid **all
  non-trivial affine integer relations**
  $$j\,(s_2 - s_1) \;=\; i\,(s_3 - s_1) \qquad \bigl(0 < \lvert i \rvert, \lvert j \rvert \le L_w,\ i \neq j\bigr),$$
  formalized as `NoRel T2 Lw` (`src/Formalism/FrobeniusOrbits/HostThickExists.lean:13`)!
- **Pressure B — Keeping $\lvert T_2 \rvert$ nearly linear in $n_0$ (lower global-size pressure):**
  At the same time, averaging over coset shifts $u_0 \in R.A$ (`coverS_carry` in Chapter 6) divides
  total chain budgets by the thick-frame share $\lvert T_2 \rvert / \varphi.\mathrm{ord}$. For that
  share loss to be absorbed into $x^{O(\varepsilon)}$, `thickFrame2` (`src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean:34`)
  demands the **near-full lower bound**
  $$\lvert T_2 \rvert \;\ge\; x^{-\varepsilon}\,\varphi.\mathrm{ord}!$$

### 17.1.2 Why greedy/Sidon sets fail polynomially while Behrend spheres win — and the two "Behrend" threads

Pause and test whether a naive construction of $T_2 \subset \{1, \dots, N\}$ ($N := \lfloor n_0 / (4 L_w) \rfloor$)
could satisfy both `NoRel T2 Lw` and $\lvert T_2 \rvert \ge x^{-\varepsilon}\,\varphi.\mathrm{ord}$ [Expository]:

1. **Why Sidon ($B_2$) or greedy sets fail by a polynomial factor $x^{1 + 3\varepsilon}$:**
   A Sidon set $T \subset \{1, \dots, N\}$ (in which all pairwise differences $s_2 - s_1$ are
   distinct) has $\binom{\lvert T \rvert}{2} \le N$, so $\lvert T \rvert \le \sqrt{2N} + 1 \ll n_0^{1/2} \asymp x^{1 + 4\varepsilon}$.
   Even a greedy set avoiding $j(s_2 - s_1) = i(s_3 - s_1)$ for $\lvert i \rvert, \lvert j \rvert \le L_w$
   without geometric structure only guarantees $\lvert T \rvert \gg (N / L_w^2)^{1/2} \asymp x^{1 + 4\varepsilon} / (\log x)^{3/2}$
   — falling short of $x^{-\varepsilon}\,\varphi.\mathrm{ord} \asymp x^{2 + 7\varepsilon}$ by more
   than **$x$**!
2. **Why Behrend's Euclidean sphere trick achieves $\exp(-C\sqrt{\log n_0 \cdot \log L_w})$:**
   In a celebrated two-page note in 1946 `[Behrend1946]`, Felix Behrend noticed two elementary miracles
   about the Euclidean sphere $\mathbb S_k := \{v \in \{0, \dots, d-1\}^S : \sum_{m=0}^{S-1} v_m^2 = k\}$
   in high dimension $S$:
   - **Strict convexity kills ALL collinear triples at once — not just midpoints!** Any three
     distinct points on a Euclidean sphere cannot lie on a common straight line in $\mathbb R^S$.
     Hence **no** non-trivial affine relation $v_2 - v_1 = \frac{i}{j}(v_3 - v_1)$ ($j \neq 0$,
     $i \neq j$, $v_r$ distinct) can ever hold on $\mathbb S_k$ (`sphere_rel`, `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:36`)!
   - **Carry-free base-$B$ projection preserves linear relations when $B = 4 L_w d$:** Encoding each
     vector $v \in \{0, \dots, d-1\}^S$ as the base-$B$ integer $\sum_{m=0}^{S-1} v_m B^m$ with base
     $B := 4 L_w d$ leaves enough digit headroom ($\lvert j(v_{2,m}-v_{1,m}) - i(v_{3,m}-v_{1,m}) \rvert \le 2 L_w(d-1) < B$)
     that no carry can ever propagate between adjacent digits when testing $j(s_2 - s_1) = i(s_3 - s_1)$!
   - **Pigeonholing $d^S$ box points into $\le S d^2$ squared radii costs only $S d^2$, balanced at
     $S \asymp \sqrt{\log n_0 / \log L_w}$:** Because $(4 L_w)^S$ costs $\exp(S \log(4 L_w))$ while
     $S d^2$ costs $\exp(2 \frac{\log n_0}{S})$, balancing $S \log L_w \approx \frac{\log n_0}{S}$
     picks dimension $S \asymp \sqrt{\frac{\log n_0}{\log L_w}}$ and loses only
     $$\exp\Bigl(-O\bigl(\sqrt{\log n_0 \cdot \log L_w}\bigr)\Bigr)!$$
   Since $\log n_0 \asymp \log x$ and $\log L_w \asymp \log\log x$, the Behrend loss factor
   $\exp\bigl(-64\sqrt{\log n_0 \cdot \log L_w}\bigr) = \exp\bigl(-O(\sqrt{\log x \cdot \log\log x})\bigr)$
   grows **slower than $x^\varepsilon$ for every fixed $\varepsilon > 0$** (by weighted AM–GM, Theorem
   17.4 below; contrast Roth's 1953 upper bound $O(N / \log\log N)$ for 3-AP-free sets `[Roth1953]`)!

3. **Clearing up the two "Behrend" threads in the archive (`P12` vs `HostOfField`):**
   In `remark.pdf` (p. 4, item 19 and fn. 7) [Paper; remark p. 4], Alpöge mentioned an October step
   using Behrend sets to tune the Iwasawa tower in `VWin` (`P12`) and remarked that it looked
   unnecessary. Indeed, as we saw in Chapter 11 (Section 11.5.1), on the **P12 `VWin`** branch the
   Iwasawa root-avoidance window uses the elementary pigeonhole count `BConst.J`
   (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:20`), while the 14-file folder `src/Formalism/BehrendSets/`
   is an evolutionary remnant whose top export `Formalism.BehrendSets.FinalE.trivStab`
   (`src/Formalism/BehrendSets/FinalE.lean:12`, proved in `src/Formalism/BehrendSets/BehrendVariance/TotientLeOfIsPrimitiveRoot.lean:65`) is
   actually a Minkowski cyclotomic matrix torsion-freeness lemma (still imported inside the
   congruence-subgroup cone!). **By contrast, Behrend's genuine sphere projection was never dropped
   from the proof of RH:** it lives in `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean`
   and `src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean`, called directly on
   the `src/Main.lean` spine via:

   > `src/Main.lean` $\to \cdots \to$ `src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean:8` $\to$ `src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8` $\to$ `src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:76` $\to$ `src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean:37` $\to$ `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:302` $\to$ `Behrend.exists_large_sphere`!

---

## 17.2 Worked examples

Before stating the general Lean types, let us compute two small-dimensional Behrend sphere encodings
and the AM–GM scale balance completely by hand [Expository].

### 17.2.1 Lattice spheres in $\mathbb Z^2$ and $\mathbb Z^3$ encoded in base $B = 4 L d$

**Example A: Dimension $S = 2$, box side $d = 6$, radius $k = 25$, and window bound $L = 2$.**
Inside the $6 \times 6$ integer grid $\mathrm{box}(2, 6) = \{0, 1, 2, 3, 4, 5\}^2$ of $6^2 = 36$
points, squared Euclidean norms $v_0^2 + v_1^2$ lie in $\{0, 1, \dots, 2 \cdot 5^2 = 50\}$. On the
circle $v_0^2 + v_1^2 = 25$, there are **four** grid points:
$$v^{(1)} = (5, 0),\qquad v^{(2)} = (4, 3),\qquad v^{(3)} = (3, 4),\qquad v^{(4)} = (0, 5).$$
Set $L = 2$, so the archive's carry-free base (`noRel_image`, `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:86`) is
$$B \;:=\; 4 L d \;=\; 4 \times 2 \times 6 \;=\; 48.$$
Applying `Behrend.map 48` ($v \mapsto v_0 + 48\,v_1$) maps the four circle points injectively to the
four natural numbers:
$$T \;=\; \bigl\{5,\; 148,\; 195,\; 240\bigr\} \;\subset\; \{0, 1, \dots, 48^2 - 1 = 2{,}303\}$$
($5 + 48\cdot 0 = 5$, $4 + 48\cdot 3 = 148$, $3 + 48\cdot 4 = 195$, $0 + 48\cdot 5 = 240$).

Let us verify **by hand** that no three distinct elements $s_1, s_2, s_3 \in T$ can satisfy
$j(s_2 - s_1) = i(s_3 - s_1)$ for **any** nonzero integers $i \neq j$ with $\lvert i \rvert, \lvert j \rvert \le L = 2$:

1. **Test a concrete triple:** Take $s_1 = 5$, $s_2 = 148$, $s_3 = 195$, so $s_2 - s_1 = 143$ and
   $s_3 - s_1 = 190$. Since $\gcd(143, 190) = 1$, an equality $j \cdot 143 = i \cdot 190$ with
   $j \neq 0$ requires $190 \mid j$, impossible for $0 < \lvert j \rvert \le 2$!
2. **See why base $48$ kills carries for *every* triple at once:** Write $s_r = v_{r,0} + 48\,v_{r,1}$
   with $0 \le v_{r,m} \le 5$. An integer equality $j(s_2 - s_1) - i(s_3 - s_1) = 0$ rewrites as
   $$c_0 + 48\,c_1 \;=\; 0, \qquad\text{where}\qquad c_m := j(v_{2,m} - v_{1,m}) - i(v_{3,m} - v_{1,m}) \in \mathbb Z.$$
   Because $\lvert v_{r,m} - v_{1,m} \rvert \le 5 < d = 6$ and $\lvert i \rvert, \lvert j \rvert \le 2$,
   each signed coefficient $c_m$ satisfies
   $$\lvert c_m \rvert \;\le\; 2 \cdot 5 + 2 \cdot 5 \;=\; 20 \;<\; 48 = B!$$
   Reducing $c_0 + 48 c_1 = 0$ modulo $48$ gives $48 \mid c_0$, which together with $\lvert c_0 \rvert < 48$
   forces **$c_0 = 0$**, and dividing by $48$ then forces **$c_1 = 0$** (`goal1`, `src/Lemmata/GeneralBFactSecondLast/Imports.lean:5`)!
   Hence $j(v_2 - v_1) = i(v_3 - v_1)$ as vectors in $\mathbb Z^2$. Since $v_1, v_2, v_3$ lie on
   $x^2 + y^2 = 25$, substituting $v_2 - v_1 = \frac{i}{j}(v_3 - v_1)$ into
   $\lVert v_2 \rVert^2 - \lVert v_1 \rVert^2 = 0 = \lVert v_3 \rVert^2 - \lVert v_1 \rVert^2$ yields
   $i(i - j)\lVert v_3 - v_1 \rVert^2 = 0$, forcing $v_3 = v_1$ (if $i \neq 0$) or $v_2 = v_1$
   (if $i = 0$), contradiction!

**Example B: Dimension $S = 3$, box side $d = 4$, pigeonhole sphere $k = 9$, and orbit wrap-around check.**
In $\mathrm{box}(3, 4) = \{0, 1, 2, 3\}^3$, there are $4^3 = 64$ lattice points, while $\sum_{m=0}^2 v_m^2$
takes values in $\{0, 1, \dots, 3 \cdot 3^2 = 27\}$ ($28$ possible radii). By the pigeonhole principle
(`exists_large_sphere_aux`, `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:237`), at least one sphere has cardinality
$\ge \lceil 64 / 28 \rceil = 3$. In fact, at radius **$k = 9$**, the decompositions $9 = 3^2 + 0^2 + 0^2 = 2^2 + 2^2 + 1^2$
give **six** points in $\{0, 1, 2, 3\}^3$! With $L = 2$ and $B = 4 L d = 4 \cdot 2 \cdot 4 = 32$,
encoding via $\mathrm{map}_{32}(v_0, v_1, v_2) = v_0 + 32\,v_1 + 1{,}024\,v_2$ produces:

| Sphere vector $v \in \{0, 1, 2, 3\}^3$ | Check $v_0^2 + v_1^2 + v_2^2 = 9$ | Base-$32$ image $s = v_0 + 32 v_1 + 1024 v_2$ | Check $4 L s = 8 s$ |
|---|---|---|---|
| $(3, 0, 0)$ | $9 + 0 + 0 = 9$ | $3$ | $24$ |
| $(0, 3, 0)$ | $0 + 9 + 0 = 9$ | $96$ | $768$ |
| $(2, 2, 1)$ | $4 + 4 + 1 = 9$ | $1{,}090$ | $8{,}720$ |
| $(2, 1, 2)$ | $4 + 1 + 4 = 9$ | $2{,}082$ | $16{,}656$ |
| $(1, 2, 2)$ | $1 + 4 + 4 = 9$ | $2{,}113$ | $16{,}904$ |
| $(0, 0, 3)$ | $0 + 0 + 9 = 9$ | $3{,}072$ | $24{,}576$ |

Now embed $T_2 = \{3, 96, 1{,}090, 2{,}082, 2{,}113, 3{,}072\}$ into the cyclic $2$-group
$\mathbb Z / n_0 \mathbb Z$ at $n_0 = 2^{15} = 32{,}768$! Notice that every $s \in T_2$ satisfies
**$4 L s \le 24{,}576 < 32{,}768 = n_0$** (`second_set_range`, `src/Formalism/LocalRingCardinality/DataHost.lean:106`). Why is that
factor of $4 L$ in $4 L s < n_0$ so crucial? Because when we test three hits $t_0 + a h, t_0 + b h, t_0 + c h$
($0 \le a < b < c < L$) in $\mathbb Z / n_0 \mathbb Z$, cross-multiplying modulo $n_0$ only gives
$$n_0 \;\big|\; X := (c - a)(s_b - s_a) - (b - a)(s_c - s_a) \qquad\text{in }\mathbb Z!$$
Since $0 < c - a, b - a < L$ and $0 \le s < \frac{n_0}{4 L}$, both products $(c - a)(s_b - s_a)$
and $(b - a)(s_c - s_a)$ have absolute value strictly below $L \cdot \frac{n_0}{4L} = \frac{n_0}{4}$,
so **$\lvert X \rvert < \frac{n_0}{2} < n_0$**, upgrading modular divisibility $n_0 \mid X$ into the
**exact integer equality $X = 0$** (`ThickOrbit.key`, `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean:60–63`)!

### 17.2.2 Numerical check of the AM–GM bridge ($C = 32 \implies C_T = 64$) and conductor-height bound

Let us also check how the archive's explicit constants behave at $\varepsilon = \frac{1}{60} < \frac{1}{52}$:

1. **Turning $\exp(-32\sqrt{\log n_0 \cdot \log L_w})$ into $x^{-\varepsilon}$ (`src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean:38–146`):**
   Theorem 17.2 (`hostThickExists`) proves `HostThickExists` with constant **$C = 32$**, giving a
   `NoRel T Lw` set of size $\ge \frac{n_0}{L_w}\exp(-32 u)$ where $u := \sqrt{\log n_0 \cdot \log L_w}$.
   Setting $\delta := \frac{\varepsilon}{3 C} = \frac{1}{5{,}760}$, weighted AM–GM
   $u = \sqrt{(\delta\log n_0)(\frac{\log L_w}{\delta})} \le \frac{1}{2}\bigl(\delta\log n_0 + \frac{\log L_w}{\delta}\bigr)$
   gives
   $$32\,u \;\le\; \frac{32\delta}{2}\,\log n_0 + \frac{32}{2\delta}\,\log L_w
   \;=\; \frac{\varepsilon}{6}\,\log n_0 + \frac{3 \cdot 32^2}{2\varepsilon}\,\log L_w
   \;=\; \frac{\log n_0}{360} + 92{,}160\,\log L_w.$$
   Since $\log n_0 \le \log C_o + (2 + 8\varepsilon)\log x < \log C_o + 3\log x$, the first term is at
   most $\frac{\varepsilon}{2}\log x + \frac{\varepsilon}{6}\log C_o$ — **using up only half of our
   $\varepsilon\log x$ budget** — while $\log L_w = O(\log\log x)$ is $o(\log x)$, so the remaining
   $\frac{\varepsilon}{2}\log x$ absorbs $92{,}160\log L_w + \log(4 C_o L_w)$ for all large $x$, and
   erasing $0$ (`T.erase 0`) yields $C_T = 2 C = \mathbf{64}$!
2. **Checking `log_conductor_mul_height_le_of_pageN` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/LogConductorMulHeightLeOfPageN.lean:6`):**
   With $C_t = 401$, $2^e \le 2 x^{2 + 8\varepsilon}$ (`PageN`), $N \le 2^{e+2} m q d$, $t \le x^{401}$,
   and $\log(q d) \le x^{\varepsilon/4}$, taking logarithms gives
   $$\log(N t) \;\le\; 3\log 2 + \log m + (403 + 8\varepsilon)\log x + x^{\varepsilon/4}
   \;\le\; 3\log 2 + \log m + 404\log x + x^{\varepsilon/4}.$$
   Once $x^{\varepsilon/4}$ exceeds $2(3\log 2 + \log m)$ and $404\log x \le \frac{1}{2} x^{\varepsilon/4}$,
   the first three terms sum to at most $x^{\varepsilon/4}$, giving $\log(N t) \le 2 x^{\varepsilon/4}$!

---

## 17.3 Definitions

We now record the exact Lean definitions from Mathlib (`Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean`) and the archive's
`FrobeniusOrbits/`, `TotientGaloisClasses/`, `LocalRingCardinality/`, `ThickFrames/`, and
`ShortNorms/` directories.

### 17.3.1 Mathlib's `Behrend` box, sphere, and base-$B$ map (`Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` & `GeneralBFactSecondLast/Imports.lean`)

**Definition 17.1 (`Behrend.box`, `Behrend.sphere`, `Behrend.map`, `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:97,110,133`, and `goal1`, `src/Lemmata/GeneralBFactSecondLast/Imports.lean:5`).** [Lean, read]

1. **Integer box and discrete sphere (`Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:97–110`):** For natural numbers $S, d, k \in \mathbb N$,
   $$\mathrm{Behrend.box}(S, d) := \bigl\{v : \mathrm{Fin}\,S \to \mathbb N \;\big|\; \forall m,\ v(m) < d\bigr\}
   \qquad\bigl(\text{cardinality } d^S,\text{ `:103`}\bigr),$$
   $$\mathrm{Behrend.sphere}(S, d, k) := \Bigl\{v \in \mathrm{Behrend.box}(S, d) \;\Big|\; \sum_{m \in \mathrm{Fin}\,S} v(m)^2 = k\Bigr\}.$$
2. **Additive base-$B$ evaluation homomorphism (`Behrend.map`, `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:133–136`):** For any radix
   $B \in \mathbb N$, `Behrend.map B : (Fin S → ℕ) →+ ℕ` is the additive monoid homomorphism
   $$\mathrm{Behrend.map}(B)(v) \;:=\; \sum_{m \in \mathrm{Fin}\,S} v(m)\,B^{m.\mathrm{val}},$$
   injective on $\{v : \forall m, v(m) < B\}$ (`Behrend.map_injOn`, `:162`).
3. **Signed carry-free uniqueness (`Bl.general_b_fact_second_last.goal1`, `src/Lemmata/GeneralBFactSecondLast/Imports.lean:5–10`, wrapped as `coeff_zero` at `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:11`):**
   For any integer $B \in \mathbb Z$, dimension $S \in \mathbb N$, and signed coefficient tuple
   $c : \mathrm{Fin}\,S \to \mathbb Z$ satisfying $\lvert c(m) \rvert < B$ for all $m \in \mathrm{Fin}\,S$,
   $$\sum_{m \in \mathrm{Fin}\,S} c(m)\,B^{m.\mathrm{val}} = 0 \implies \forall m \in \mathrm{Fin}\,S,\ c(m) = 0.$$

### 17.3.2 `NoRel`, `HostThickOrbit`, `HostThickExists`, and `Frame` (`HostThickExists.lean`, `ZsmulGeneratorEqZeroOfProjection.lean`)

**Definition 17.2 (`NoRel`, `InTranslate`, `HostThickOrbit`, `HostThickExists`, `src/Formalism/FrobeniusOrbits/HostThickExists.lean:13,18,22,30`, and `Frame`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:15,68,70,72,89,112,118,120,122`).** [Lean, read]

1. **Bounded-ratio affine relation freeness (`NoRel`, `src/Formalism/FrobeniusOrbits/HostThickExists.lean:13–16`):** For a finite set
   $T \subset \mathbb N$ and window parameter $L \in \mathbb N$, `NoRel T L : Prop` asserts that for
   every three pairwise distinct elements $s_1, s_2, s_3 \in T$ ($s_1 \neq s_2$, $s_1 \neq s_3$,
   $s_2 \neq s_3$) and every pair of integers $i, j \in \mathbb Z$ satisfying
   $0 < \lvert i \rvert \le L$, $0 < \lvert j \rvert \le L$, and $i \neq j$,
   $$j \cdot \bigl((s_2 : \mathbb Z) - s_1\bigr) \;\neq\; i \cdot \bigl((s_3 : \mathbb Z) - s_1\bigr).$$
2. **Orbit-window intersection predicate (`InTranslate` and `HostThickOrbit`, `:18–28`):** For
   $T \subset \mathbb N$ and $u_0, x \in \mathbb Z/n\mathbb Z$, write `InTranslate T u₀ x` if
   $x = (s : \mathbb Z/n\mathbb Z) + u_0$ for some $s \in T$. Then `HostThickOrbit : Prop` asserts
   that whenever $n > 0$, $L \ge 2$, $\forall s \in T,\ 4 L s < n$, and `NoRel T L`, for all
   $u_0, t, h \in \mathbb Z/n\mathbb Z$:
   - *(long orbits)* if $4 L < \operatorname{addOrderOf}(h)$, then for every $i_0 \in \mathbb Z$,
     $\bigl\lvert \{i \in [i_0, i_0 + L) \cap \mathbb Z : \mathrm{InTranslate}(T, u_0, t + i \cdot h)\} \bigr\rvert \le 2$;
   - *(short orbits)* if $\operatorname{addOrderOf}(h) \le 4 L$, then
     $\bigl\lvert \{x \in \mathbb Z/n\mathbb Z : (\exists i \in \mathbb Z,\ x = t + i \cdot h) \wedge \mathrm{InTranslate}(T, u_0, x)\} \bigr\rvert \le 1$.
3. **Subexponential `NoRel` existence (`HostThickExists`, `:30–32`):** Asserts the existence of an
   absolute constant $C > 0$ such that for all $n, L \in \mathbb N$ with $L \ge 2$, there exists
   $T \subset \mathbb N$ satisfying $\forall s \in T,\ 4 L s < n$, `NoRel T L`, and
   $$\frac{n \cdot \exp\bigl(-C \sqrt{\log n \cdot \log L}\bigr)}{L} \;\le\; \lvert T \rvert.$$
4. **Abelian host frame (`Formalism.HC.Frame`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:15–23, 61–124`):**
   A `Frame` packages `(e, ord, grp, h0, gen0)` where `A := Fin ord` is a finite additive abelian
   group projecting surjectively via `h0 : A →+ Additive (HGrp e)` onto the $2$-adic cyclotomic
   quotient $(\mathbb Z/2^{e+2}\mathbb Z)^\times / \{\pm 1\} \cong \mathbb Z/2^e\mathbb Z$, and
   `a0 := gen0 ∈ A` satisfies `∀ k : ℤ, h0 (k • a0) = 0 → k • a0 = 0` (so `h0` is injective on the
   cyclic subgroup `A0 = ⟨a0⟩` of order `n0 := addOrderOf a0 ∣ 2^e` and index `o := ord / n0`, with
   digit map `dig s := s • a0` injective on `[0, n0)`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean:223–294`!). Its sign-extended
   group `GG := G0 × Multiplicative A` carries the CM subgroup `Psi := ker chD`, the place-folding
   map `placeOf g := if g.1.2 = 1 then g else cc * g` (`:118`), and the two sheet embeddings
   `tau1 t := ((1, 1), iota t)` and `tau2 t := ((-1, 1), iota t)` (`:120–122`).

### 17.3.3 `Ranks`, `Host`, `thickPlaces`, and `HostGood` (`src/Formalism/LocalRingCardinality/Params.lean`, `DataHost.lean`, `ThinScalesIffHostBound.lean`)

**Definition 17.3 (`Ranks`, `Host`, `topPlaces`, `thickPlaces`, `IsThin`, `secondSet_card_lower_bound`, and `HostGood`, `src/Formalism/LocalRingCardinality/Params.lean:6`, `src/Formalism/LocalRingCardinality/DataHost.lean:24,39,100–109,129–136,165`, and `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:61,101,120`).** [Lean, read]

1. **Chain rank extension (`Ranks extends Frame`, `src/Formalism/LocalRingCardinality/Params.lean:6–46`):** Extends `Frame` by the even
   word parameter $k$, even chain length $m$, and odd rank step $t > 3m$, setting $n := \mathrm{ord}$,
   $f := 2n$, base unitary rank $r := k + m - 1$ (odd), and step-$j$ rank $\mathrm{rankY}(j) = r + j t$.
2. **Concrete host record (`Host R extends HostAx R.toFrame`, `src/Formalism/LocalRingCardinality/DataHost.lean:39–109`):** Packages a
   CM number field $E = H.E$ with $\sqrt{-q}, \sqrt{-d} \in E$ (`sqq_sq`, `sqrtMinusD`), Galois
   isomorphism `gal : (E ≃ₐ[ℚ] E) ≃* R.GG`, conductor bound `QS ≤ R.n^2`, index bound `o^64 ≤ 2^R.e`,
   small-prime splitting bound `splitBound`, relative different factorization `𝔟 * conj(𝔟)`, auxiliary
   level primes `g 0, g 1, pde, pde' ∈ levelPrimes`, split ideal `ccK`, and the **two subset frames**
   (`:100–109`):
   - `TT : Finset R.A`, defining `topPlaces := TT.image R.tau1` (`:129`); and
   - `T2 : Finset ℕ`, shift `u0 : R.A`, window length `Lw : ℕ` (`2 ≤ Lw`), range bound
     `second_set_range : ∀ s ∈ T2, 4 * Lw * s < R.n0` (`:106`), affine-relation freeness
     `second_set_no_relation : NoRel T2 Lw` (`:107`), constant `CT2 : ℝ`, and
     `thickPlaces := T2.image (fun s => R.tau2 (R.dig s + u0))` (`:133–134`), with
     `secondSet_card_lower_bound` (`:165–166`):
     $$\frac{R.n_0 \cdot \exp\bigl(-H.\mathrm{CT2}\,\sqrt{\log R.n_0 \cdot \log H.L_w}\bigr)}{H.L_w} \;\le\; \lvert H.T_2 \rvert.$$
3. **Scale-admissible hosts (`HostGood`, `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:101–109`):** At scale $s : \mathrm{Scale}$,
   `HostGood s C8 C5 c6 Cb H q0` includes `HostVal`, `HostArith`, the second-set
   lower bound and density bound $4L_w|T_2|\le n_0$, `QDq`, `BoxW`, `ThinOK`, `BadOK`,
   and $|\mathrm{dlogH}\,H|\le x^\varepsilon$. Its remaining clauses prescribe disjointness,
   norm witnesses, congruences and the five level primes. The bound $x^{-\varepsilon}n\le |T_2|$
   and the window equality $L_w=\mathrm{Lwv}(s)$ enter the assembly through `hof_thick`
   and the `HostVal` data.

---

## 17.4 Lemmas and proofs

We now give complete, line-by-line human proofs of every `R3`-read theorem in this engine: signed
base-$B$ uniqueness (Lemma 17.1), strict sphere convexity and `hostThickExists` with $C = 32$
(Theorem 17.2), the Frobenius orbit intersection cap $\le 2$ (Proposition 17.3), and the AM–GM scale
bridge `thickFrame2` ($C_T = 64$), `hostOfField`, and `log_conductor_mul_height_le_of_pageN`
(Theorem 17.4).

### 17.4.1 Carry-free signed base-$B$ digit uniqueness (`goal1` & `map_lt`)

**Lemma 17.1 (Signed base-$B$ uniqueness and box range bound).** [Lean, read]

1. *(`Bl.general_b_fact_second_last.goal1`, `src/Lemmata/GeneralBFactSecondLast/Imports.lean:5–32`, and `coeff_zero`, `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:11`)*
   *Let $B \in \mathbb Z$, $S \in \mathbb N$, and $c : \mathrm{Fin}\,S \to \mathbb Z$. If
   $\lvert c(m) \rvert < B$ for all $m \in \mathrm{Fin}\,S$ and $\sum_{m \in \mathrm{Fin}\,S} c(m) B^{m.\mathrm{val}} = 0$,
   then $c(m) = 0$ for every $m \in \mathrm{Fin}\,S$.*
2. *(`map_lt`, `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:15–34`)* *For $B \in \mathbb N$ and $v : \mathrm{Fin}\,S \to \mathbb N$,
   if $v(m) < B$ for all $m$, then $\mathrm{Behrend.map}(B)(v) < B^S$.*

*Proof.*
(1) Induct on $S \in \mathbb N$ (`src/Lemmata/GeneralBFactSecondLast/Imports.lean:12–32`). For $S = 0$, `Fin 0` is empty (`m.elim0`). For
$S = n + 1$, evaluating $\lvert c(0) \rvert < B$ gives $0 \le \lvert c(0) \rvert < B$, hence $B > 0$
(`hB`, `:16`). Splitting off the $m = 0$ term (`Fin.sum_univ_succ`, `:17–23`) writes the sum as
$$c(0) + B \sum_{i \in \mathrm{Fin}\,n} c(i + 1)\,B^{i.\mathrm{val}} \;=\; 0.$$
Therefore $B$ divides $c(0)$ in $\mathbb Z$ (`hd`, `:24`). Since $\lvert c(0) \rvert < B$, the only
multiple of $B$ in $(-B, B)$ is $0$ (`Int.eq_zero_of_abs_lt_dvd`, `:25`), so $c(0) = 0$! Cancelling
$B \neq 0$ from $B \sum_{i \in \mathrm{Fin}\,n} c(i + 1) B^{i.\mathrm{val}} = 0$ (`hT`, `:27–30`) and
applying the induction hypothesis to $i \mapsto c(i + 1)$ gives $c(i + 1) = 0$ for all $i \in \mathrm{Fin}\,n$.

(2) Induct on $S$ (`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:17–34`): for $S = 0$, $0 < B^0 = 1$; for $S + 1$,
$\mathrm{map}_B(v) = v(0) + B\,\mathrm{map}_B(v \circ \mathrm{succ}) \le (B - 1) + B(B^S - 1) = B^{S+1} - 1 < B^{S+1}$. $\square$

### 17.4.2 Strict sphere convexity and `hostThickExists` with explicit constant $C = 32$ (`ThickExists.lean`)

**Theorem 17.2 (Sphere relation-freeness and subexponential `NoRel` existence with $C = 32$).** [Lean, read]

1. *(Strict convexity against arbitrary $(i, j)$-relations: `sphere_rel`, `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:36–72`)*
   *Let $v_1, v_2, v_3 : \mathrm{Fin}\,S \to \mathbb Z$ lie on the same sphere $\sum_m v_r(m)^2 = k$
   ($k \in \mathbb Z$), and suppose $i, j \in \mathbb Z$ satisfy $j \neq 0$, $i \neq j$, and
   $j\,(v_2(m) - v_1(m)) = i\,(v_3(m) - v_1(m))$ for all $m \in \mathrm{Fin}\,S$. Then $v_2 = v_1$.*
2. *(Carry-free sphere encoding: `noRel_image` and `card_image`, `:85–173`)*
   *For all $L, S, d, k \in \mathbb N$ with $L \ge 1$ and base $B := 4 L d$, the image
   $T := (\mathrm{Behrend.sphere}(S, d, k)).\mathrm{image}(\mathrm{Behrend.map}(4 L d))$ satisfies
   `NoRel T L` and $\lvert T \rvert = \lvert \mathrm{Behrend.sphere}(S, d, k) \rvert$.*
3. *(Explicit Behrend bound with $C = 32$: `hostThickExists`, `:181–334`)*
   *`HostThickExists` holds with $C = 32$: for all $n, L \in \mathbb N$ with $L \ge 2$, there exists
   $T \subset \mathbb N$ with $\forall s \in T,\ 4 L s < n$, `NoRel T L`, and*
   $$\frac{n \cdot \exp\bigl(-32\sqrt{\log n \cdot \log L}\bigr)}{L} \;\le\; \lvert T \rvert.$$

*Proof.*
(1) Subtracting $\sum_m v_1(m)^2 = k$ from $\sum_m v_2(m)^2 = k$ and $\sum_m v_3(m)^2 = k$ via the
algebraic identity $v_r^2 - v_1^2 = 2 v_1(v_r - v_1) + (v_r - v_1)^2$ gives (`hA`, `hB`, `:39–46`):
$$\sum_{m \in \mathrm{Fin}\,S} \Bigl(2 v_1(m)\bigl(v_2(m) - v_1(m)\bigr) + \bigl(v_2(m) - v_1(m)\bigr)^2\Bigr) = 0,$$
$$\sum_{m \in \mathrm{Fin}\,S} \Bigl(2 v_1(m)\bigl(v_3(m) - v_1(m)\bigr) + \bigl(v_3(m) - v_1(m)\bigr)^2\Bigr) = 0.$$
Now take $j^2$ times the first sum minus $i j$ times the second sum (`hW`, `:47–53`): using
$j(v_2(m) - v_1(m)) = i(v_3(m) - v_1(m))$, the linear $2 v_1(m)$ terms $2 i j^2 v_1(v_3 - v_1) - 2 i j^2 v_1(v_3 - v_1)$
cancel **identically**, leaving the pure quadratic identity
$$i(i - j) \sum_{m \in \mathrm{Fin}\,S} \bigl(v_3(m) - v_1(m)\bigr)^2 \;=\; 0!$$
If $i = 0$ (`:54–59`), then $j(v_2(m) - v_1(m)) = 0$ with $j \neq 0$ gives $v_2 = v_1$ directly. If
$i \neq 0$ (`:60–72`), then $i \neq j \implies i(i - j) \neq 0$, so $\sum_m (v_3(m) - v_1(m))^2 = 0$;
since squares in $\mathbb Z$ are nonnegative, $v_3(m) = v_1(m)$ for every $m$, whence
$j(v_2(m) - v_1(m)) = i \cdot 0 = 0$ and $j \neq 0 \implies v_2 = v_1$!

(2) Suppose $s_1, s_2, s_3 \in T$ are pairwise distinct images of $v_1, v_2, v_3 \in \mathrm{Behrend.sphere}(S, d, k)$
under $\mathrm{Behrend.map}(B)$ ($B = 4 L d$), and suppose $j(s_2 - s_1) = i(s_3 - s_1)$ with
$0 < \lvert i \rvert, \lvert j \rvert \le L$ and $i \neq j$ (`:88–101`). Since $0 \le v_r(m) < d$
(so $d \ge 1$ because $T$ has $\ge 3$ elements!), $\lvert v_r(m) - v_1(m) \rvert \le d - 1$, and
therefore for every $m \in \mathrm{Fin}\,S$ (`hbound`, `:102–124`):
$$\bigl\lvert j(v_2(m) - v_1(m)) - i(v_3(m) - v_1(m)) \bigr\rvert
\;\le\; L(d - 1) + L(d - 1) \;=\; 2 L(d - 1) \;<\; 4 L d = B!$$
Rearranging $j(s_2 - s_1) - i(s_3 - s_1) = 0$ gives $\sum_m \bigl(j(v_2(m) - v_1(m)) - i(v_3(m) - v_1(m))\bigr) B^m = 0$
(`hsum`, `:125–132`). Lemma 17.1(1) forces $j(v_2(m) - v_1(m)) = i(v_3(m) - v_1(m))$ for every $m$,
and part (1) gives $v_2 = v_1 \implies s_2 = s_1$, contradicting $s_1 \neq s_2$ (`:133–144`)! Similarly,
if $\mathrm{map}_B(v) = \mathrm{map}_B(w)$ for $v, w \in \mathrm{sphere}(S, d, k)$, then
$\lvert v(m) - w(m) \rvert < d \le 4 L d = B$, so Lemma 17.1(1) gives $v = w$, proving $\lvert T \rvert = \lvert \mathrm{sphere}(S, d, k) \rvert$
(`card_image`, `:146–173`).

(3) Fix $n, L \in \mathbb N$ with $L \ge 2$, and set $x := \log n$, $y := \log L > \frac{1}{2}$
(since $\log 2 > 0.693 > \frac{1}{2}$, `:192–196`), and $s := \sqrt{x y}$ (`:187–190`).
- **Small-$n$ regime (`:198–215`):** If $n e^{-32 s} / L \le 1$, take $T = \emptyset$ (when $n = 0$)
  or $T = \{0\}$ (when $n \ge 1$, where $4 L \cdot 0 = 0 < n$, `NoRel {0} L` holds vacuously since
  $\{0\}$ has no three distinct elements, and $\lvert \{0\} \rvert = 1 \ge n e^{-32 s}/L$!).
- **Main asymptotic regime (`:216–334`):** Assume $n e^{-32 s} / L > 1$, so $n \ge 1$, $e^x = n$,
  $e^y = L$, and **$x - 32 s - y > 0$** (`hpos`, `:223`). Multiplying by $y > 0$ and using $s^2 = xy$
  gives $s^2 - 32 y s - y^2 > 0$, forcing **$s > 32 y > 16$** (`hs32`, `hs16`, `:229–233`)! Now choose
  the dimension $S$, real log-side $a$, and integer box side $d$ (`:234, 244, 263`):
  $$S \;:=\; \lfloor s / y \rfloor \;\ge\; 32, \qquad
  a \;:=\; \frac{x - y - 3}{S}, \qquad
  d \;:=\; \Bigl\lfloor \frac{e^a}{4 L} \Bigr\rfloor.$$
  Verify the inequalities step by step:
  1. Since $\frac{s}{2 y} \le S \le \frac{s}{y}$, we have $x = \frac{s^2}{y} \le 2 s S$, so **$a \le 2 s$**
     (`ha2s`, `:251`), while $x - y - 3 > 32 s - 3 \ge (7 + y) S$ (using $s > 32 y$ and $y > \frac{1}{2}$,
     `:254–259`) gives **$a \ge 7 + y$** (`ha7`, `:254`).
  2. Consequently $e^a \ge e^{7 + y} = e^7 L \ge 8 L$ (`h8L`, `:272`, since $e^7 > 1{,}096 \ge 8$), so
     $\frac{e^a}{4 L} \ge 2$ and flooring loses at most a factor of $2$:
     $$1 \;\le\; \frac{e^a}{8 L} \;\le\; d \;\le\; \frac{e^a}{4 L} \;\le\; e^a$$
     (`hd1'`, `hQd`, `hdQ`, `:266–279`), whence $e^{a S} \le d^S (8 L)^S$ (`hdS`, `:280`) while
     $n = e^x = e^{a S} \cdot L \cdot e^3$ (`hn_eq`, `:285`).
  3. **Range bound $4 L m < n$ (`:305–319`):** By Mathlib's pigeonhole lemma `Behrend.exists_large_sphere S d`
     (`Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:245–259`, partitioning $\mathrm{box}(S, d)$ of size $d^S$ into the $\le S(d-1)^2 + 1 \le S d^2$
     spheres $\mathrm{sphere}(S, d, k)$ for $0 \le k \le S(d-1)^2$!), there exists a radius $k$ with
     $$\bigl\lvert \mathrm{Behrend.sphere}(S, d, k) \bigr\rvert \;\ge\; \frac{d^S}{S d^2}.$$
     Set $T := (\mathrm{sphere}(S, d, k)).\mathrm{image}(\mathrm{map}_{4Ld})$. Every $m = \mathrm{map}_{4Ld}(v) \in T$
     satisfies $m < (4 L d)^S \le e^{a S}$ by Lemma 17.1(2), so
     $$4 L m \;<\; 4 L\,(4 L d)^S \;\le\; 4 L e^{a S} \;\le\; e^3 L e^{a S} \;=\; n$$
     (since $e^3 > 20 > 4$, `:316–319`)!
  4. **Cardinality bound with $C = 32$ (`:260–261, 289–301, 320–334`):** Using $8 L \le e^{7 + y}$,
     $S \le e^S$, $e^{2a} = (e^a)^2$, $S y \le s$, $S \le 2 s$ (since $y > \frac{1}{2} \implies S \le \frac{s}{y} < 2s$),
     and $a \le 2s$, check the total exponent (`hexpb`, `:260`):
     $$3 + S(7 + y) + S + 2 a \;=\; 3 + 8 S + S y + 2 a \;<\; 3 + 16 s + s + 4 s \;<\; 32 s$$
     (since $s > 16 \implies 3 < s$!). Exponentiating gives $e^3 (8L)^S S e^{2a} \le e^{32 s}$ (`hprod`, `:289`), so
     $$n e^{-32 s}\,(S d^2) \;\le\; \bigl(d^S (8L)^S L e^3\bigr)\,e^{-32 s}\,(S e^{2a})
     \;=\; d^S L \cdot e^{-32 s}\bigl(e^3 (8L)^S S e^{2a}\bigr) \;\le\; d^S L.$$
     Dividing by $L \cdot S d^2 > 0$ yields $\frac{n e^{-32 s}}{L} \le \frac{d^S}{S d^2} \le \lvert \mathrm{sphere}(S, d, k) \rvert = \lvert T \rvert$! $\square$

### 17.4.3 From `NoRel` to the $\le 2$ Frobenius-orbit window bound (`ThickOrbit.lean`, `FrameFacts.lean`, `AtMostTwoThickInWindowLongOrbit.lean`)

**Proposition 17.3 (Orbit intersection cap $\le 2$ per length-$L_w$ window and thick density $\le \frac{1}{4 L_w}$).** [Lean, read]

1. *(`HostThickOrbit` on $\mathbb Z/n\mathbb Z$: `ThickOrbit.key`, `part_one`, `part_two`, `hostThickOrbit`, `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean:21,71,96,132`; lifted to `Frame.A` in `Frame.hostThickOrbit`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean:821`)*
   *Whenever $T \subset \mathbb N$ satisfies $\forall s \in T,\ 4 L s < n_0$ and `NoRel T L` ($L \ge 2$),
   every translate $\mathrm{dig}(T) + u_0 \subseteq \varphi.A$ meets any progression window
   $\{t + i \cdot h : i_0 \le i < i_0 + L\}$ of step order $\operatorname{addOrderOf}(h) > 4 L$ in
   **at most $2$ indices**, and meets the entire coset $\{t + i \cdot h : i \in \mathbb Z\}$ of any
   short step $\operatorname{addOrderOf}(h) \le 4 L$ in **at most $1$ element**.*
2. *(Downstream thick-place guarantees: `no_three_consecutive_thick_places`, `src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/NoThreeConsecutiveThickPlaces.lean:222`; `LongWindow.main`, `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AtMostTwoThickInWindowLongOrbit.lean:27`; and `thick_density_le`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickSetDensityLeInvFourLw.lean:7`)*
   *For any `H : Host R`, no Frobenius element $\varphi \notin R.\Psi$ ($\varphi \neq \mathrm{cc}$)
   produces three consecutive thick places ($i, i+1, i+2$), every long Frobenius word window
   ($4 H.L_w < \operatorname{ord}(\varphi_2)$) of length $H.L_w$ contains at most $2$ thick letters,
   and whenever $8 H.L_w < R.n$, the thick place density satisfies $\mathrm{de}_2 = \frac{\lvert T_2 \rvert}{R.n} \le \frac{1}{4 H.L_w}$.*

*Proof.*
(1) First consider a long step $h \in \mathbb Z/n\mathbb Z$ with $\operatorname{addOrderOf}(h) > 4 L$
(`ThickOrbit.key` and `part_one`, `:21–94`). Suppose toward a contradiction that the filtered window
$S \subseteq [i_0, i_0 + L)$ had $\lvert S \rvert \ge 3$; setting $a := \min S$, $c := \max S$, and
picking $b \in (S \setminus \{c\}) \setminus \{a\}$ gives three integers $i_0 \le a < b < c < i_0 + L$
with $t + a h = s_a + u_0$, $t + b h = s_b + u_0$, $t + c h = s_c + u_0$ in $\mathbb Z/n\mathbb Z$
for $s_a, s_b, s_c \in T$.
- *Distinctness of $s_a, s_b, s_c$ (`:32–46`):* If $s_a = s_b$, subtracting gives $(b - a) h = 0$ in
  $\mathbb Z/n\mathbb Z$, so $\operatorname{addOrderOf}(h) \mid (b - a)$; since $0 < b - a < L \le 4 L < \operatorname{addOrderOf}(h)$,
  this is impossible! Symmetrically $s_a \neq s_c$ and $s_b \neq s_c$.
- *Eliminating $h$ and lifting from $\mathbb Z/n\mathbb Z$ to $\mathbb Z$ (`:47–63`):* Define the integer
  $$X \;:=\; (c - a)(s_b - s_a) - (b - a)(s_c - s_a) \;\in\; \mathbb Z.$$
  In $\mathbb Z/n\mathbb Z$, $(b - a)((t + c h) - (t + a h)) - (c - a)((t + b h) - (t + a h)) = ((b - a)(c - a) - (c - a)(b - a)) h = 0$,
  so $(X : \mathbb Z/n\mathbb Z) = 0$, i.e., **$n \mid X$** (`hdvd`, `:51`)! Because $0 < b - a < c - a < L$
  and $0 \le 4 L s_r < n$, each of $(c - a) s_b$, $(c - a) s_a$, $(b - a) s_c$, $(b - a) s_a$ lies in
  $[0, n/4)$ (`bound_aux`, `:9–14`), whence $\lvert X \rvert < \frac{n}{2} < n$ (`habs`, `:60`)! Thus
  `Int.eq_zero_of_abs_lt_dvd` forces **$X = 0$ in $\mathbb Z$** (`:63`), violating `NoRel T L` at
  $i = b - a \neq j = c - a$ with $0 < i < j < L$ (`:64–69`)!

Next consider a short step $m := \operatorname{addOrderOf}(h) \le 4 L$ (`part_two`, `:96–129`). Given
any two intersection points $x = t + i h = s_1 + u_0$ and $y = t + i' h = s_2 + u_0$ ($s_1, s_2 \in T$),
multiplying $(s_1 - s_2 : \mathbb Z/n\mathbb Z) = (i - i') h$ by $m$ kills $m h = 0$ and gives
$n \mid m(s_1 - s_2)$ in $\mathbb Z$. Since $0 < m \le 4 L$ and $4 L s_r < n$, both $m s_1$ and $m s_2$
lie in $[0, n)$ (`int_mul_lt_of_le_four_mul`, `:15–19`), so $\lvert m(s_1 - s_2) \rvert < n \implies m(s_1 - s_2) = 0 \implies s_1 = s_2 \implies x = y$!
In `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean:714–821`, any equality $(q - p) \cdot h = (s_q - s_p) \cdot a_0$ in `φ.A` ensures
$(q - p) \cdot h \in A_0 = \langle a_0 \rangle \cong \mathbb Z/n_0\mathbb Z$, reducing `Frame.hostThickOrbit`
to the exact same divisibility argument modulo $n_0$.

(2) `LongWindow.main` (`src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AtMostTwoThickInWindowLongOrbit.lean:27–54`) applies `Frame.hostThickOrbit`
directly to `letter τ φ (i + k)` (whose `A`-coordinate is $\iota^{-1}(\tau_2) + (i + k)\cdot\iota^{-1}(\varphi_2)$
by `letter_snd`, `:20–24`; the place-coordinate identity `placeOf_snd` is used separately, inside
`thick_inTranslate`, `:10–18`, at `:16`), while `no_three` (`src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/NoThreeConsecutiveThickPlaces.lean:28–115`) handles
consecutive steps $i, i+1, i+2$ for *arbitrary* $\varphi \notin \Psi, \varphi \neq \mathrm{cc}$
(even without assuming $4 L_w < \operatorname{ord}(\varphi_2)$!) because $x := \iota^{-1}(\varphi_2) \neq 0$
forces $(s_3 - s_2) a_0 = x = (s_2 - s_1) a_0 \implies n_0 \mid (s_1 + s_3 - 2 s_2)$ with
$\lvert s_1 + s_3 - 2 s_2 \rvert < \frac{n_0}{2L} < n_0 \implies s_1 + s_3 = 2 s_2$, contradicting
`NoRel` at $(i, j) = (1, 2)$! Finally, in `thick_density_le` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickSetDensityLeInvFourLw.lean:7–55`),
$4 L_w s < n_0 \le n$ embeds $T_2 \subseteq \{0, 1, \dots, N - 1\}$ where $N := \lfloor (n - 1)/(4 L_w) \rfloor + 1 \ge 3$;
since $\{0, 1, 2\} \not\subseteq T_2$ (as $2(1 - 0) = 1(2 - 0)$ violates `NoRel` at $i = 1, j = 2$,
`:29–38`), $\lvert T_2 \rvert \le N - 1 = \lfloor (n - 1)/(4 L_w) \rfloor$, so $4 L_w \lvert T_2 \rvert < n$! $\square$

### 17.4.4 Scale balancing (`thickFrame2` with $C_T = 64$), `hostOfField`, and `log_conductor_mul_height_le_of_pageN`

**Theorem 17.4 (AM–GM scale bridge `thickFrame2`, full `Host` assembly, and subexponential conductor-height bound).** [Lean, read]

1. *(AM–GM scale bridge with $C_T = 64$: `thickFrame2`, `src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean:29–198`)*
   *With $C_T = 2 \cdot 32 = 64$, for every $0 < \varepsilon < \frac{1}{52}$ and $C_o, C_L > 0$,
   there exists $x_0$ such that for all $x \ge x_0$, every `φ : Frame`, and every $L_w \ge 2$ with
   $L_w \le C_L \log x$, $\varphi.o \le C_o$, and $\frac{1}{2} x^{2 + 8\varepsilon} \le \varphi.\mathrm{ord} \le C_o x^{2 + 8\varepsilon}$,
   there exists $T_2 \subset \mathbb N$ (`0 ∉ T2`) satisfying $\forall s \in T_2,\ 4 L_w s < \varphi.n_0$,
   `NoRel T2 Lw`,*
   $$\frac{\varphi.n_0 \cdot \exp\bigl(-64\sqrt{\log \varphi.n_0 \cdot \log L_w}\bigr)}{L_w} \;\le\; \lvert T_2 \rvert,
   \qquad
   x^{-\varepsilon}\,\varphi.\mathrm{ord} \;\le\; \lvert T_2 \rvert,
   \qquad\text{and}\qquad
   4 L_w \lvert T_2 \rvert \;\le\; \varphi.n_0.$$
2. *(Assembling `Host R` and `supplyOfAdm`: `hostOfFieldOf`, `src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:71,159`, and `hostOfField` / `supplyOfAdm`, `src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8,17`)*
   *Combining `thickFrame2` at $L_w = \mathrm{Lwv}(s) = \lceil 405\log x \rceil + \lceil 30/\varepsilon \rceil$
   with `topsChoiceH` (`src/Development/AutomorphicArithmetic/ThickFrames/topsChoiceH.lean:30`), `exists_host` (`src/Development/AutomorphicArithmetic/CoprimeRanks/SecondSetNoRelation.lean:100`),
   level primes $g_0,g_1$ represented by the norm form `NormOne` (supplied through `ShortNorm`) and
   small primes $\equiv 1$ modulo the level from `smallOne`, constructs a complete `Host R`
   satisfying `HostGood` and `Shares`, feeding `supplyOfAdm` (`src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:17`) and `supplyChi` (`src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean:8`).*
3. *(Conductor-times-height bound: `log_conductor_mul_height_le_of_pageN`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/LogConductorMulHeightLeOfPageN.lean:6–56`)*
   *For all $0 < \varepsilon < \frac{1}{52}$, $C_t \in \mathbb R$, and $m \in \mathbb N$, there exists
   $x_0$ such that for all $x \ge x_0$ and $N, t, e, q, d \in \mathbb N$ with $1 \le N \le 2^{e+2} m q d$,
   `PageN eps x e` ($2^e \le 2 x^{2+8\varepsilon}$), $1 \le t \le x^{C_t}$, and $\log(qd) \le x^{\varepsilon/4}$,
   we have*
   $$\log(N \cdot t) \;\le\; 2\,x^{\varepsilon/4}.$$

*Proof.*
(1) Let $C = 32$ be the constant of Theorem 17.2(3), and set $K := 1 + \frac{3 C^2}{2\varepsilon} > 0$,
$t := \frac{\varepsilon}{2 K} > 0$, and $\delta := \frac{\varepsilon}{3 C} > 0$ (`src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean:40–43, 102`).
By `thickFrame2_large` (`:18–27`, using $\log(t y / 2) \le t y / 2 - 1$), choose $x_0 = e^{y_0}$ so
that for $y = \log x \ge y_0$, both $\log(4 C_o) + \frac{\varepsilon}{6}\log C_o + K(\log C_L + \log y) \le K t y = \frac{\varepsilon}{2}\log x$
and $\log n_0 \ge \frac{\log 2}{C^2}$ hold (`:44–100`). Writing $u := \sqrt{\log n_0 \cdot \log L_w}$,
weighted AM–GM $p q \le \bigl(\frac{p + q}{2}\bigr)^2$ at $p = \delta \log n_0$ and $q = \frac{\log L_w}{\delta}$
gives (`hu_up`, `hCu`, `:104–126`):
$$C u \;\le\; \frac{C}{2}\Bigl(\delta\log n_0 + \frac{\log L_w}{\delta}\Bigr)
\;=\; \frac{\varepsilon}{6}\log n_0 + (K - 1)\log L_w.$$
Since $\log n_0 \le \log C_o + (2 + 8\varepsilon)\log x \le \log C_o + 3\log x$ (as $8\varepsilon < \frac{8}{52} < 1$, `:85–89`)
and $\log L_w \le \log C_L + \log\log x$, adding $\log(4 C_o) + \log L_w$ gives (`hgoal`, `:135–138`):
$$\log(4 C_o) + \log L_w + C u \;\le\; \frac{\varepsilon}{2}\log x + \frac{\varepsilon}{2}\log x \;=\; \varepsilon\log x,
\qquad\text{so}\qquad 4 C_o L_w e^{C u} \;\le\; x^\varepsilon!$$
Now invoke Theorem 17.2(3) (`hT φ.n0 Lw`) to get $T \subset \mathbb N$ with $\forall s \in T,\ 4 L_w s < n_0$,
`NoRel T Lw`, and $\lvert T \rvert \ge Q := \frac{n_0 e^{-Cu}}{L_w}$, and **erase $0$**: set
$T_2 := T \setminus \{0\}$ (`T.erase 0`, `:181`)!
- Removing $0$ preserves $\forall s \in T_2,\ 4 L_w s < n_0$ and `NoRel T2 Lw`, and since every
  $s \in T_2$ is $\ge 1$, $T_2 \subseteq [1, \max T_2]$ implies $4 L_w \lvert T_2 \rvert \le 4 L_w \max T_2 \le n_0$
  (`thickFrame2_card`, `:7–16, 197`)!
- Because $u \ge \frac{\log 2}{C}$ (`hu_low`, `:113`), we have $E := e^{Cu} \ge 2$, while
  $x^{-\varepsilon}\,\varphi.\mathrm{ord} \le \frac{C_o n_0}{4 C_o L_w E} = \frac{Q}{4}$ (`hX`, `:157–164`)
  and $x^{-\varepsilon}\,\varphi.\mathrm{ord} \ge \frac{1}{2} x^{2 + 7\varepsilon} \ge 1$ (`hX1`, `:165–170`),
  so $Q \ge 4$. Therefore $\lvert T_2 \rvert \ge \lvert T \rvert - 1 \ge Q - 1$: since $Q \ge 4$,
  $Q - 1 \ge \frac{Q}{2} \ge Q E^{-1} = \frac{n_0 e^{-2Cu}}{L_w}$ (giving $C_T = 2 C = 64$, `:186–195`)
  and $Q - 1 \ge \frac{Q}{4} \ge x^{-\varepsilon}\,\varphi.\mathrm{ord}$ (`:196`)!

(2) In `src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:58–69`, for $\log s.x \ge 1$, `hof_Lwv_le` bounds
$\mathrm{Lwv}(s) = \lceil 405\log s.x \rceil + \lceil 30/\varepsilon \rceil < (4084 + 60/\varepsilon)\log s.x$.
Feeding $C_L := 4084 + 60/\varepsilon$ into `thickFrame2` yields `hof_thick` (`:71–95`). Then
`hostOfFieldOf` (`:159–255`) assembles five distinct level primes
$g_0,g_1,p_{\mathrm{de}},p'_{\mathrm{de}},q_0$ (`:104,194`).
Writing $M=Q_Sqd$, the two distinguished primes satisfy $1$ modulo $\operatorname{lcm}(15,M)$
(`:205–206`), and $g_0,g_1,q_0$ satisfy $1$ modulo $M$ (`:208,215`).
The ideal $\mathfrak c_K$ is the unit ideal (`:104,109`). The primes $g_0,g_1$ come from
`levelData` (`:167`, built on `ShortNorm` and `SmallOne`) with
$(kb)^8\le g_i\le 2(kb)^8$, where $k$ is `R.k` and $b$ is `s.b`, and `NormOne d M g_i`. This is not a norm-one condition:
`NormOne d M p` says $A^2+dB^2=4p$ with $M\mid B$ and $2M\mid A-2-B$
(`src/Development/AbelianVarietyTheory/Definitions/Foundations/RayPrimes.lean:40–41`), and
`normOne_iff_host` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormOneIffOfSqrt.lean:128`)
turns it into a witness $\pi\in\mathcal O_E$ lying in the subfield `H.K` of the host with
$\pi\bar\pi=g_i$ and $\pi\equiv1 \pmod M$ (`:219`, `:229–230`). The norm of $\pi$ is $g_i$, not $1$;
`hgm` derives $g_i\equiv1 \pmod M$ from the same condition (`:208–209`). The proof takes
$T_2$ from `hof_thick` and the top set from `topsChoiceH`, then verifies `HostGood`
(`:225–255`). Specializing in `src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8,17`
gives `hostOfField` and `supplyOfAdm`.

(3) Fix $0 < \varepsilon < \frac{1}{52}$ and $r := \frac{\varepsilon}{4} > 0$ (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/LogConductorMulHeightLeOfPageN.lean:10`).
Since $\log x = o(x^r)$ and $x^r \to +\infty$ as $x \to +\infty$, choose $x_0 \ge 1$ (`:12–15`) such
that for all $x \ge x_0$, $(3 + \lvert C_t \rvert)\log x \le \frac{1}{2} x^r$ (`hKl`, `:21`) and
$3\log 2 + \log m \le \frac{1}{2} x^r$ (`hg`, `:13, 16`). From `PageN eps x e`, $2^e \le 2 x^{2 + 8\varepsilon}$,
so $e\log 2 \le \log 2 + (2 + 8\varepsilon)\log x \le \log 2 + 3\log x$ (since $8\varepsilon < 1$, `:50–56`).
Combining $N \le 2^{e+2} m q d$, $t \le x^{C_t}$, and $\log(qd) \le x^r$ gives (`:38–56`):
$$\log(N t) \;\le\; (e + 2)\log 2 + \log m + \log(qd) + C_t \log x
\;\le\; (3\log 2 + \log m) + (3 + \lvert C_t \rvert)\log x + x^r
\;\le\; \frac{1}{2} x^r + \frac{1}{2} x^r + x^r \;=\; 2\,x^{\varepsilon/4}! \quad \square$$

### 17.4.5 From congruence primes to a usable host-field scale

**Motivation.** The host needs two designated split primes and a third auxiliary
prime that all fit a power of the host modulus. The two norm-form primes
$g_0,g_1$ occupy a much larger interval. A uniform polynomial prime bound lets
us enlarge the modulus to avoid a prime already chosen, while retaining a
power bound in terms of the original modulus.

**Example.** For modulus $5$, take $11=2\cdot5+1$. Enlarge the modulus to
$5\cdot11=55$ and take $331=6\cdot55+1$. Trial division by
$2,3,5,7,11,13,17$ proves that $331$ is prime. It is $1$ modulo both $5$ and
$11$, so it differs from $11$. The third modulus is $5\cdot11\cdot331=18205$. The prime
$218461=12\cdot18205+1$ is $1$ modulo $5$, $11$ and $331$.
Trial division up to $467$ verifies primality. [Expository]

**Definitions.** `SmallOne` asserts that an absolute real $A\ge1$ works
for every natural modulus $M\ge2$: there is a prime $\ell\equiv1\pmod M$
with $\ell\le M^A$. Write $\pi_{M,a}(Y)$ for the number of primes
$\ell\le Y$ congruent to $a$ modulo $M$, with $\gcd(a,M)=1$. Its
increment across $(Y,Y(1+h)]$ counts distinct primes. Lean uses the finite
set of integers strictly above the natural floor of $Y$ and at most the
natural floor of $Y(1+h)$, filtered by primality and congruence.
At the host write $N=Q_Sqd$ for `condN`, where $Q_S$ is the
host base level and $q,d$ are the auxiliary pair from `PairGood`. The separate bounded parameter
called `M` in the signature of `hostOfFieldOf` satisfies $0<M\le C_0$.
The scale `s : Scale` has $x>1$, $0<\varepsilon<1/52$ and $J\ge1$.
Put $b=\exp(x^\varepsilon)$ and $k=R.k$.
(`src/Development/AutomorphicArithmetic/ShortNorms/ShortNorm.lean:13–16`,
`src/Formalism/GL3MeanSquares/SmoothedRemainderRealIntegralFormula.lean:105–110,126–130`,
`src/Formalism/LocalRingCardinality/DataParams₂.lean:9–29`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:54`.)

**The interval estimate.** Set $\operatorname{Li}(Y)=\int_2^Y dt/\log t$
and $E(Y)=\operatorname{Li}(Y)-\theta\operatorname{Li}(Y^\beta)$.
The archive's `PrimesRel` supplies absolute $0<c_1\le1/8$ and
positive $c_2,c_3,C_A,c_S$, uniformly for $M\ge3$. There is at most one
exceptional pair $(\chi,\beta)$ with $\chi^2=1$,
$1-c_1/\log M<\beta<1$, and $L(\beta,\chi_{\rm prim})=0$.
For this pair $1-\beta\ge c_S/(M^2\log M)$ and
$\theta=\chi(a)\in\{-1,1\}$. Without an exceptional pair take $\theta=0$.
For $Y\ge M^{c_2}$ one has
$$
|\varphi(M)\pi_{M,a}(Y)-E(Y)|
\le C_A\bigl(e^{-c_3\log Y/\log M}+e^{-\sqrt{c_3\log Y}}\bigr)E(Y).
$$
At $a=1$ the exceptional sign is $+1$, so subtraction can shrink
the main term. The gap keeps its growth large enough and the error is
measured relative to that corrected main term.
(`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ZerosDisc.lean:26–43`.)

Take $B=4M$, $C_r=C_A$, $c_r=\min(c_3,\sqrt{c_3})$, and
$\rho(B,Y)=C_r e^{-c_r\log Y/\log B}+C_r e^{-c_r\sqrt{\log Y}}$.
The old error factor is at most $\rho(B,Y)$ and the old gap
implies $1-\beta\ge c_S/(B^2\log B)$. For
$C_I=\max(c_2,60,2/c_S)$, $Y\ge B^{C_I}$, $h\le1$,
$\rho(B,Y)\le h/100$, and $B^7\le hY^{1/3}$, the interval estimate gives
$$
\pi_{M,a}(Y(1+h))-\pi_{M,a}(Y)\ge
\frac{h}{100}B^{-6}\frac{Y}{\log Y}.
$$

To see the subtraction in the proof, put $V=Y(1+h)$. The derivative
of $E(t)$ is $(1-\theta t^{\beta-1})/\log t$. Use $W=1$ for
$\theta=0,-1$, and $W=1-Y^{\beta-1}$ for $\theta=1$.
In the last case $(1-\beta)\log Y\ge2/B^2$ by the choice of $C_I$.
The inequality $1-e^{-v}\ge v/(1+v)$ therefore gives
$W\ge1/(2B^2)$. The numerator of the derivative is at least $W$
on $[Y,V]$ and at most $2W$ on $[4,V]$, using $V\le Y^2$.
With $T=WhY/\log Y$ integration gives $E(V)-E(Y)\ge T/2$.
The proof bounds $0\le E(Y)\le E(V)\le6+12WY/\log Y$ using
$E(4)\le6$ and $\operatorname{Li}(V)\le3V/\log V$. The two
endpoint errors together cost at most $(12h+24T)/100$. In the
general interval proof the auxiliary count and correction terms are
absorbed using $u=Y^{1/12}\ge1024$, $\log Y\le12u$ and
$B^7\le hu^4$, which give $4Bu^6\le12T/100$ and
$12h/100\le Bu^6$. The progression specialization sets the two
auxiliary terms to zero and uses $G=\varphi(M)\in[1,B]$.
After subtracting the endpoint error and these allowances from $T/2$,
$14T/100$ remains. This bound for the weighted count increment gives the
displayed estimate, using $W\ge1/(2B^2)$ and $B^{-3}\ge B^{-6}$.
The filtered interval count is exactly the difference by disjoint
union at $\lfloor Y\rfloor$. [Lean, read]
(`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimesAPIntervalOfPrimesRel.lean:12–87`,
`src/Formalism/GL3MeanSquares/HookFormulaTorsion/GlobalBoundRefinements.lean:22–246,366–433`,
`src/Formalism/GL3MeanSquares/HookFormulaTorsion/PrimesInProgressionCountLowerBound.lean:200–343`.)

**Lemma (one prime within a fixed power).** The interval estimate
implies `SmallOne`. [Lean, read]
(`src/Development/AutomorphicArithmetic/ShortNorms/SmallOneOf.lean:8–98`.)

*Proof.* Choose an integer $D\ge\max(C_I,21,\log(200C_r)/c_r)$,
put $K=D^2$ and take $A=3K+1$. For $M=2$ use $3\le2^A$.
For $M\ge3$ take $B=4M$, $Y=B^K$, $h=1$, and $a=1$.
Since $\log B\ge1$, we have $\log Y/\log B=K\ge D$ and
$\sqrt{\log Y}\ge D$. Each summand of $\rho(B,Y)$ is at most
$1/200$. The inequalities $K\ge C_I$ and $K\ge21$ yield the
other two size conditions $Y\ge B^{C_I}$ and $B^7\le Y^{1/3}$.
The count lower bound is strictly positive and supplies a prime
$\ell\equiv1\pmod M$. Since $4M\le M^3$,
$\ell\le2Y\le2M^{3K}\le M^A$. $\square$

**Lemma (three primes and the scale comparison).** For $N\ge30$,
`SmallOne` gives distinct primes $p,p',q_0$ with
$p,p'\equiv1\pmod{15N}$ and $q_0\equiv1\pmod N$, all at most
$N^{C_*}$ for $C_*=(1+2A+(2A+2)A)A$. [Lean, read]
(`src/Development/AutomorphicArithmetic/ShortNorms/ExistsThreePrimesOneModLeRpow.lean:7–70`,
`src/Development/AutomorphicArithmetic/ShortNorms/levelData.lean:10–77`.)

*Proof.* Apply the lemma to $15N$, then $p(15N)$, then $Npp'$.
Reducing modulo the factors gives the required residues. A later
prime is $1$ modulo each previously included prime, which has remainder
$0$ modulo itself. Since $15N\le N^2$, the first prime is at most
$N^{2A}$ and the second at most $N^{(2A+2)A}$. Multiplying the
bounds gives $Npp'\le N^{1+2A+(2A+2)A}$, yielding the stated common power.

For `levelData`, `ModAt` requires $d$ prime, $d\equiv3\pmod4$,
$d\ge100$, $N>0$, $d\mid N$, and
$\log N\le3x^{\varepsilon/5}(\log x)^2$. Thus $N\ge100$.
Choose the threshold $x_3$ so that $x\ge x_3$ implies $x\ge1$
and $4C_*\log x\le x^{\varepsilon/5}$ by
$\log x=o(x^{\varepsilon/5})$. Then $U=x^{\varepsilon/5}\ge1$ and
$\log x\le U$, so $3C_* U(\log x)^2\le3U^3/4<U^5=x^\varepsilon$.
Exponentiation yields $N^{C_*}<b\le(kb)^8$ because $k,b\ge1$.
The three primes lie below the norm-form interval $[(kb)^8,2(kb)^8]$.
`levelData` explicitly exports $p,p'\ne g_i$. Its output only needs
$q_0$ distinct from $p,p'$. Its threshold is $\max(x_1,\max(x_2,x_3))$
with $x_1$ from `typePrimesN` on the `ShortNorm` branch and
$x_2$ from `rank_basic_bounds`. $\square$

**Into the host.** The pair row and window in `hostOfFieldOf` give
$\log N\le2x^{\varepsilon/5}(\log x)^2$, and `qdBig` gives
$d\ge100$. Thus `ModAt` applies. The exponent used in the output is
$\max(C_0,C_*)$, enlarging the three upper bounds. The common scale
threshold is the maximum of the seven thresholds from `levelData`,
`thinH`, `topsChoiceH`, `pairRows`, `hof_thick`,
`hof_log_le_rpow` with multiplier $4$, and `qdBig`.
(`src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:159–204`.)

The congruence modulo $15N$ descends to one modulo $\operatorname{lcm}(15,N)$
and hence to one modulo each factor. For the three small primes
$\gcd(\ell,N)=\gcd(1,N)=1$ gives coprimality with $Q_S$ for
`level_coprimeS`. The two residues modulo $15$ give `pde_mod`
in the host record. The initial host data are chosen through `admitted`, which preserves the
specified level set. The two designated primes furnish the size clauses of
`HostVal` and the lcm congruences of `HostGood`. The $q_0$ clause
records primality, congruence, power bound and distinction from the
designated pair. The last clause records the set of all five primes.
(`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/DisjointExceptional.lean:205–212`,
`src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:97–124,205–241`,
`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean:78–91`,
`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:101–109`.)

For a prime $\ell\equiv1\pmod N$, we have $\ell\nmid N$.
The host Frobenius law gives the identity Frobenius from the residue $1$
and trivial inertia outside $N$. The entire decomposition stabilizer is
therefore trivial, and transitivity on primes above $\ell$ gives $[E:\mathbb Q]$
such primes. Also $4\mid Q_S$ and $\ell\equiv1\pmod d$ give
$\left(\frac{-d}{\ell}\right)=1$ by quadratic reciprocity.
Since $\ell$ avoids $Q_S,q,d$, its class is `splitK`. In `HostArith`
the two designated primes furnish the two counts of places, and all
five furnish the `splitK` clause. The congruences and norm witnesses
for $g_i$ come from their `NormOne` data. [Lean, read]
(`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NcardPrimesOverOfStabilizer.lean:12–110`,
`src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:208–241`.)

**Analytic boundary.** `primesRel_holds` chooses $c_1$ as the minimum
of $1/8$ and the positive cutoffs in the zero-free-region and Chebyshev
estimates. The former gives uniqueness, simplicity, $\beta\ge7/8$,
and the gap for the exceptional pair. It bounds other zeros
$\rho$ with $\Re\rho<1$ by
$\Re\rho\le1-c/\log(M(|\Im\rho|+2))$ for some positive $c$.
The Chebyshev estimate bounds the relative error of the von Mangoldt sum
$\psi_{M,a}(Y)=\sum_{n\le Y,\ n\equiv a\pmod M}\Lambda(n)$
after multiplication by $\varphi(M)$, using the main term
$Y-\theta Y^\beta/\beta$ and the same two exponential error shapes
starting at a uniform power of $M$. The prime-count transfer uses
$1\le\varphi(M)\le M$, $\beta\ge7/8$ in the exceptional case,
and $1-\beta\ge c_S/M^3$ via $\log M\le M$. The assembly and exports
are [Lean, read]. The deeper bounds are [Lean] with proof-level reading
[Open]. In particular the Chebyshev proof calls exceptional-zero
repulsion, a truncated explicit formula, and a zero-density sum over
characters. The thresholds here are expressed in terms of the archive
constants. The classical precedent for the polynomial conclusion is
Linnik's least-prime theorem ([Xylouris2009](https://arxiv.org/abs/0906.2749v1)). Dirichlet's infinitude theorem
supplies no uniform polynomial cutoff.
(`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimesInProgressionsRelativeError.lean:11–51`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimesInProgressionsRelativeErrorStatement.lean:8–9`,
`src/Development/AutomorphicArithmetic/ShortNorms/Primes.lean:7`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExceptionalDirichletZeroUniqueZeroFreeRegionStatement.lean:8–9`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChebyshevPsiProgressionRelativeError.lean:294–305`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RepulsionStatement.lean:8–9`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExplicitFormulaDirichletZerosRightHalfStatement.lean:8–9`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumRpowZerosLeStatement.lean:8–9`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeErrorStatement.lean:8–9`.)

All archive citations in this subsection refer to A1, `lean.tar.gz` SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

---

### 17.4.10 The exceptional zero in the trivial ray-class interval

The weighted interval estimate starts with a pole contribution of size $Y-X$. A simple real zero at $\beta$ contributes an interval term with the opposite sign. As $\beta$ approaches $1$, that term approaches $Y-X$ itself. The two questions for the lower bound are therefore how many such terms occur across the ray characters and how much of the pole contribution survives.

**Worked models. [Expository]** The following calculations use exact endpoint terms with optional remainder bounds. They specify the pole and zero contributions algebraically.

1. Take four characters, no exceptional zero and endpoints $X=100$, $Y=125$. Only the principal character has a main term. Its endpoint difference is $125-100=25$, so the normalized main term is $25/4$. If the two endpoint remainders have aggregate absolute bounds $1$ and $2$ before normalization, the normalized lower bound is $(25-1-2)/4=11/2$.
2. Let $m\ge 2$ be an integer and name the model zero $\beta=1-1/m$. Set $a=2m$, $X=a^m$ and $Y=(a+1)^m$. Then $Y/X=(1+1/a)^m\le e^{1/2}<2$. Suppose a two-character model assigns the zero to its nonprincipal character. The principal difference is $(a+1)^m-a^m$. The nonprincipal endpoints are $-m a^{m-1}/(m-1)$ and $-m(a+1)^{m-1}/(m-1)$, so their difference is $-m((a+1)^{m-1}-a^{m-1})/(m-1)$. For instance $m=4$ gives $X=4096$, $Y=6561$, and the endpoint magnitudes are $2048/3$ and $972$. The deduction is $868/3$ and the normalized remainder is $(2465-868/3)/2=6527/6$. Assigning the sole zero to the principal character puts both contributions in that character and gives the same normalized remainder. For the general model, the strip and gap conditions are exactly $c_9/B^A\le 1/m\le c_0/\ell(0)$, to be imposed if the model is used with those hypotheses. The numerical specialization illustrates the endpoint algebra.
3. To test omission of the deduction, take a two-character model, $X=4$, $Y=5$, $\beta=999/1000$, and zero remainder. Since $5<2^{1000}$, every $t\in[4,5]$ satisfies $1/2<t^{-1/1000}<1$. Thus $1/2<(5^\beta-4^\beta)/\beta<1$ by integration. The normalized interval value lies strictly between $0$ and $1/4$. Dropping the zero would predict a lower bound of $1/2$ with zero error, and even allowing an error of $1/4$ in the unnormalized sum would predict $3/8$. Both bounds fail in this exact model. This is a counterexample to dropping a term in the budget, with no assertion of a zero of an actual $L$-function.

**The family and its zeros. [Lean, read]** The input is the family constructed by `exists_lFam_ray` for a prime $d\ge100$ with $d\equiv3\pmod4$ and an integer $M\ge3$. Its field is $K=\mathbb Q(\sqrt{-d})$, its group $G$ is the ray class group for $(M)$ written additively, and its parameters are $B=4dM^2$ and $\kappa=2\pi/(\sqrt d\,M^2)$. The coefficient $a(g,n)$ counts ideals in the norm fiber, and $\lambda(g,n)$ carries the prime-power weight. The real-character convolution condition in the family comes from `conv_real_char`. The consumer specializes to this one family through `exists_lFam_normOne_of_mod_four_eq_three` and `exists_lam_zero_sum_shortInterval_ge`. In particular, all characters share $B$, including characters induced from smaller conductors.

Write $L_\chi(s)$ for the series of the character-weighted coefficients $a_\chi(n)$ and $D_\chi(s)$ for the series of the weights $\lambda_\chi(n)$. The regularized analytic function $F_\chi$ agrees on $\Re s>1$ with $(s-1)L_1(s)$ for the principal character and with $L_\chi(s)$ otherwise. It is analytic for $\Re s>1/2$, and the supplied Euler logarithmic derivative identity gives
$D_\chi(s)={\bf1}_{\chi=1}/(s-1)-F_\chi'(s)/F_\chi(s)$ for $\Re s>1$. Write $\ell(t)=\log(B(|t|+2))$, so $\ell(t)>2$. A real character satisfies $\chi^2=1$, which includes the principal character.

For $0<c_0\le1/20$, `ExcZ` specifies a set $Z_\chi$ of cardinality at most one. Each member is a real zero $\beta$ of $F_\chi$ with $1-c_0/\ell(0)\le\beta<1$ and $F_\chi'(\beta)\ne0$. Every complex zero in the closed region $\Re s\ge1-c_0/\ell(\Im s)$ must equal a member of $Z_\chi$. The definition is per character. The proof below is what makes the total number of pairs $(\chi,\beta)$ at most one.

**Lemma 1 (zero-free region and uniqueness from the local formula). [Lean, read]** Assume the archive's continuation, conjugation, Euler logarithmic derivative and local logarithmic derivative inputs. There are uniform $c_4,c_5>0$. A zero with real part at least $3/4$ and with either $\chi^2\ne1$ or nonzero imaginary part has real part strictly less than $1-c_4/\ell(\Im s)$. Among real characters there is at most one pair $(\chi,\beta)$ with $F_\chi(\beta)=0$, $\beta\ge3/4$ and $\beta\ge1-c_5/\ell(0)$, and its zero is simple.

*Proof.* The Euler identity supplies nonvanishing for $\Re s>1$. The local formula gives a finite zero sum over the disk of radius $3/5$ and an error in norm at most $C\ell(t)$ for $F_\chi'/F_\chi$ within radius $1/2$ of the same center, away from zeros. At $s=1+a+it$, $0<a\le1/2$, it bounds $\Re D_\chi(s)$ above by the principal pole term $a/(a^2+t^2)$ when $\chi=1$, plus $C\ell(t)$, minus the real parts of $1/(s-\rho)$ for any selected distinct zeros in the disk of radius $3/5$ about $5/4+it$. Each real part is nonnegative because $\Re\rho\le1$. The full formula weights it by the analytic order. We keep those orders for the real uniqueness argument. Analyticity and nonvanishing somewhere in the connected half-plane make each order finite.

The coefficient positivity used with this bound follows by writing the real part of the absolutely convergent series as a sum with weights $\lambda(g,n)n^{-\sigma}\ge0$. For $z=\chi(g)n^{-it}$, the polynomial $3+4\Re z+\Re(z^2)=2(1+\Re z)^2$ is nonnegative. Consequently $3D_1(\sigma)+4\Re D_\chi(\sigma+it)+\Re D_{\chi^2}(\sigma+2it)\ge0$. At real $\sigma>1$ the weights $1$, $1+\chi(g)$ and $(1+\chi(g))(1+\psi(g))$ likewise give nonnegative sums for real characters $\chi,\psi$.

Consider a zero $1-\delta+i\gamma$ with $0\le\delta\le\epsilon\le1/400$, $\epsilon>0$, in one of the cases to be excluded. If $\chi^2=1$ and $|\gamma|<30\epsilon$, then $\gamma\ne0$ and conjugation supplies the distinct zero $1-\delta-i\gamma$. Evaluate at $1+60\epsilon$. Both zeros are in the disk at height zero, by $1/4+\delta+|\gamma|<3/5$. Their contribution is at least $120/(4621\epsilon)$, since the numerator is at least $60\epsilon$ and the denominator is at most $(61^2+30^2)\epsilon^2=4621\epsilon^2$. For the principal character use positivity of $D_1$ directly. For a nonprincipal real character use positivity of $D_1+D_\chi$. Either way the pole and error allow at most $1/(60\epsilon)+2C\ell(0)$.

In the other case apply the trigonometric inequality at $\sigma=1+6\epsilon$, $t=\gamma$. The selected zero at height $\gamma$ lies within $1/4+\delta$ of its disk center and contributes at least $1/(7\epsilon)$, with weight four. The unshifted principal pole has weight three and contributes $3/(6\epsilon)$. A shifted pole can occur at height $\gamma$ only for $\chi=1$, or at $2\gamma$ only for $\chi^2=1$. In either instance its height has absolute value at least $30\epsilon$, and $6\epsilon/((6\epsilon)^2+(30\epsilon)^2)=1/(156\epsilon)$. The total error is at most $9C\ell(\gamma)$ using $\ell(0)\le\ell(\gamma)$ and $\ell(2\gamma)\le2\ell(\gamma)$. Hence
$4/(7\epsilon)\le3/(6\epsilon)+5/(156\epsilon)+9C\ell(\gamma)$.
Both cases imply $1/\epsilon\le K_0\ell(\gamma)$ for the archive's $K_0=300C$, by the displayed rational inequalities. Choose $c_4=1/(4K_0+400)$. A zero on or to the right of the claimed boundary would admit $\epsilon=1/((2K_0+200)\ell(\gamma))\le1/400$ and $\delta\le\epsilon$, contradicting that bound.

For uniqueness, write $l=\ell(0)$ and take $c_5=1/(100(C+1))$ with the constant from the real local bound. At $\sigma=1+2c_5/l$, the evaluation point lies within $1/2$ of $5/4$, and each qualifying real zero costs at least $l/(3c_5)$ per unit of multiplicity. The disk includes all selected zeros since $3/4\le\beta\le1$. Two units can arise from distinct zeros of one character, distinct characters, or a multiple zero. For the principal character alone use $D_1$. For one nonprincipal real character, or a pair with one principal member, use $D_1+D_\chi$. For distinct nonprincipal real characters use $D_1+D_\chi+D_\psi+D_{\chi\psi}$. Here $\chi\psi\ne1$, since each character is its own inverse. In every case there is only one principal pole and at most four local errors. The two units would imply $2l/(3c_5)\le l/(2c_5)+4Cl$, impossible because $1/(6c_5)>4C$. A vanishing first derivative would give order at least two, so applying the argument even with the same pair proves simplicity. $\square$

**Lemma 2 (power separation from $1$). [Lean, read]** Assume the archive's exponential-sum bounds, continuation and Euler inputs. There are uniform $A,c_9>0$ such that every real-character zero $\beta\ge3/4$ satisfies $1-\beta\ge c_9/B^A$.

*Proof.* First bound $|F_\chi(1)|$ from below. In the principal case it is $\kappa|G|\ge1/B$. For a nonprincipal real character put $P(t)=\sum_n a_1(n)e^{-tn}$, $Q(t)=\sum_n a_\chi(n)e^{-tn}$ and $\rho=\kappa|G|$. The exponential-sum input bounds $P(t)-\rho/t$ and $Q(t)$ in absolute value by $E\min(t,1/t)$ with $E=C B^{11}$, supplies exponential decay of $Q$ for $t\ge1$, and identifies $F_\chi(1)=L=\int_0^\infty Q(w)\,dw$. The archive uses
$W(y)=\int_0^\infty e^{-y/w-w}\,dw/w$. This is positive and decreasing for $y>0$. Its integrability and bound $W(y)\ll y^{-3}$ follow from $e^{-y/w}\le6w^3/y^3$. Expanding the two series and substituting $w\mapsto nw$ in the integrals gives, for $v>0$,
$\int_0^\infty P(v/w)Q(w)\,dw/w=\sum_{k\ge1}(a_1*a_\chi)(k)W(vk)$.
Absolute convergence here follows from $|a_1(m)|,|a_\chi(m)|\le14|G|m$ and the bound on $W$, which dominates the double sum by a constant times $\sum_{m,n\ge1}m^{-2}n^{-2}$. For each class the count at $x=n$ bounds an individual coefficient by $4n+10\sqrt n\le14n$, using nonnegativity and $\kappa\le4$. The first clause of the family's real convolution condition makes each convolution coefficient nonnegative. The coefficient at $1$ is $1$, so the integral is at least $W(v)$.

On the other hand, remove $\rho/(v/w)$ from $P(v/w)$. Using $\min(t,1/t)\le\sqrt t$ on its error, the integral is at most $\rho L/v+E^2\sqrt v\,J$, where $J=\int_0^\infty\min(w,1/w)\,dw/(w\sqrt w)$ is finite by the power bounds at zero and infinity. With $w_0=W(1)$ and $\eta=\min(1,w_0/(2(C^2 J+1)))$, set $v=(\eta/B^{22})^2$. Then $W(v)\ge w_0$ and the error is at most $w_0/2$. Since $\rho\le4B$, we get $|L|\ge\eta^2 w_0/(8B^{45})$. Thus both cases give $|F_\chi(1)|\ge b/B^{45}$ with $b=\min(1,\eta^2w_0/8)$.

For $|z-1|\le1/4$, the circle of radius $1/10$ about $z$ has real part at least $13/20$ and modulus at most $27/20$. The continuation bound $300B(|s|+1)^2$ is at most $1800B$ there. Cauchy's derivative estimate gives $|F_\chi'(z)|\le18000B$. A real zero with $\beta\ge3/4$ has $\beta\le1$ by the Euler input, so the real segment from $\beta$ to $1$ stays in this disk. Integrating the derivative gives $b/B^{45}\le |F_\chi(1)-F_\chi(\beta)|\le18000B(1-\beta)$. This gives the supplied exponent $A=46$ and positive constant $b/18000$. $\square$

**Conditional theorem (the weighted interval with the exceptional deduction). [Lean, read]** Take the preceding inputs and the endpoint estimate `rayClassFamily_psi_with_exceptional_zero` as hypotheses. There are uniform $A>0$, $0<c_9\le1$ and $c>0$. For any of the families above, take $X\ge1$, $\log B\le c\sqrt{\log X}$ and $e^{-c\sqrt{\log X}}\le h\le1$, and put $Y=X(1+h)$. The region with $c_0=\min(1/20,c_4,c_5)$ has at most one exceptional pair. If it exists then $3/4\le\beta<1$ and $\delta=c_9/B^A\le1-\beta$. In either case the interval weight $S=\sum_{X<n\le Y}\lambda(0,n)$ satisfies $S\ge(c_9/4)hX/B^{A+1}$.

*Proof.* Since $\ell(t)>2$, every zero in the $c_0$ region lies above $3/4$. Lemma 1 forces it onto the real axis and onto a real character, and gives uniqueness across that family and simplicity. Lemma 2 gives the uniform gap after capping its constant by $1$. The sets $Z_\chi$ obtained by collecting these real zeros satisfy all clauses of `ExcZ` simultaneously, even at equality on the region boundary. The three constants are chosen before the family, so the argument uses one constant for every character at the same modulus and the same constants for all allowed $d,M$.

For $u\ge2$ and $\log B\le\sqrt{\log u}$, the endpoint input states
$\psi_\chi(u)={\bf1}_{\chi=1}u-\sum_{\beta\in Z_\chi}u^\beta/\beta+e_\chi(u)$ with $|e_\chi(u)|\le Cu\exp(-c_7\sqrt{\log u})$, uniformly in the family and character for the chosen $c_0$. The sign follows from the logarithmic derivative: a local factor $(s-\beta)g(s)$ with $g(\beta)\ne0$ gives residue $-1$ in $D_\chi$ after meromorphic continuation. Multiplication by $u^s/s$ gives residue $-u^\beta/\beta$. The principal pole at $1$ contributes $+u$, since $F_1(1)\ne0$. Taking the endpoint at $Y$ minus the endpoint at $X$ gives $-Y^\beta/\beta+X^\beta/\beta$. A principal exceptional character carries both the pole and deduction. A nonprincipal real exceptional character carries only the deduction, while the principal character still supplies $Y-X$. The finite projection used here is the existing trivial-class identity $|G|S=\sum_\chi(\psi_\chi(Y)-\psi_\chi(X))$. Each character has coefficient $1$ in this identity.

Write $L_X=\sqrt{\log X}$ and take $c\le1$. Then $\log B\ge1$ forces $X\ge e$, both endpoints satisfy the endpoint hypotheses, and $X\le Y\le2X$. By the triangle inequality the endpoint differences contribute an aggregate error of magnitude at most $3BCX e^{-c_7 L_X}$. If there is a zero, its positive deduction size is
$(Y^\beta-X^\beta)/\beta=\int_X^Y t^{\beta-1}\,dt\le hX\exp(-(1-\beta)\log X)\le hX(1-\delta/2)$.
Here $0<\delta\le1$ and $e^{-\delta}\le 1/(1+\delta)\le1-\delta/2$. In the empty case the deduction is zero, so the same upper bound applies. The pole minus deduction is therefore at least $hX\delta/2$.

Use the archive's choice $c=\min(1,c_7/(2(A+2)),c_7c_9/(24C))$. Since $cL_X\ge1$, the inequality $e^v\ge1+v$ gives $12C\le c_9e^{c_7L_X/2}$. Multiplying the error by $4B^A/X$ yields
$12CB^{A+1}e^{-c_7L_X}\le c_9 e^{((A+1)c-c_7/2)L_X}\le c_9e^{-cL_X}\le c_9h$.
The error therefore consumes at most $hX\delta/4$. It follows that $|G|S\ge hX\delta/4$ and $|G|\le B$ gives the claim. The gap is used precisely to keep a positive portion of the pole term available for this last error comparison. $\square$

**Reading boundary.** The local logarithmic derivative formula, continuation and Euler identification are named inputs in Lemmas 1–2, as is `tsum_exp_mul_aChi_bounds` in Lemma 2. The endpoint formula is used with its precise uniform quantifiers. Its residue calculation explains the sign. The proof of the endpoint input, including the contour choice, subtracted logarithmic derivative and truncated Perron budget, is given in §17.4.11. The [source map](../sources/SOURCES.md#p13-exceptional-zero-in-the-trivial-ray-class-interval) identifies the proofs and the declaration-level inputs. Zaman, *Explicit estimates for the zeros of Hecke L-functions*, Theorem 1.1 and the remark after Corollary 1.2, give a classical precedent for family uniqueness and for the principal-character possibility. The constants in this section come from the pinned archive. [Zaman, arXiv:1502.05679v4](https://arxiv.org/abs/1502.05679)


### 17.4.11 Producing the ray-class endpoint formula

The weighted interval argument needs the same estimate at $X$ and $Y$. The pole at $1$ supplies the principal main term. A real zero near $1$ changes both endpoints. The rectangle must stay in the classified strip even at its top and bottom, and the Perron kernel must handle an integer endpoint.

**Two endpoint calculations. [Expository]**

1. In a four-character model with empty exceptional sets, take $X=81$ and $Y=100$. The endpoint main terms are $(81,0,0,0)$ and $(100,0,0,0)$. Subtraction and projection give $19/4$. If each character's remainders have bounds $1/4$ and $1/2$, the unnormalized interval error is at most $4(1/4+1/2)=3$ and the projected weight lies in $[4,11/2]$. The four error differences can have the same sign and attain $3/4$ each under these individual bounds. Using $3/4$ for the unnormalized error would underestimate it by a factor of four.
2. In a two-character model assume a simple real exceptional zero $\beta=1-1/m$ on the nonprincipal character. Put $a=2m$, $X=a^m$, $Y=(a+1)^m$ for integer $m\ge2$, so $Y/X\le e^{1/2}<2$. The principal difference is $(a+1)^m-a^m$. The exceptional endpoints are $-ma^{m-1}/(m-1)$ and $-m(a+1)^{m-1}/(m-1)$. For $m=3$ these are $-54$ and $-147/2$ at $X=216$, $Y=343$. Their difference is $-39/2$ and the projected main term is $(127-39/2)/2=215/4$. Using just the $Y$ term gives $107/4$, an underestimate by $27$. Using just the $X$ term gives $181/2$, an overestimate by $147/4$. If the zero belongs to the principal character, its two combined terms are $162$ and $539/2$, while the nonprincipal terms vanish. Projection again gives $215/4$. With the illustrative per-character error bounds of the first model the projected interval is $[53,109/2]$. The numerical case tests the algebra. Application of the general model requires $c_9/B^A\le 1/m\le c_0/\ell(0)$ and the modulus and endpoint conditions below.

**Family and hypotheses.** The record built by **exists_lFam_ray** (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLFamRay.lean:73–128) uses the additive form $G$ of the ray class group of $K=\mathbb Q(\sqrt{-d})$ at integer modulus $M$, with prime $d\ge100$, $d\equiv3\pmod4$, and $M\ge3$. It has $B=4dM^2$, $|G|\le B$ and norm-indexed weights $\lambda(g,n)\ge0$ with $\sum_g\lambda(g,n)\le2\Lambda(n)$. **exists_lFam_normOne_of_mod_four_eq_three** supplies this record to **normPrimes_short_interval_lower**, which calls the weighted interval estimate and then deweights. Its weighted supplier **trivialClass_shortInterval** obtains the uniform endpoint constant before choosing the family and passes the two evaluations to **sum_est** (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrivialClassShortInterval.lean:144–164,218–281). [Instantiation and proof locations](../sources/SOURCES.md#p13-ray-class-endpoint-explicit-formula)

Write $q_\chi(n)=\sum_{g\in G}\chi(g)\lambda(g,n)$ for lamChi, $\psi_\chi(u)=\sum_{1\le n\le u}q_\chi(n)$, and $\ell(t)=\log(B(|t|+2))$. Let $b_\chi$ be the principal-character indicator, and use the pole-removed $F_\chi$ of §17.4.10. Assume continuation of $F_\chi$ to an analytic function on $\Re s>1/2$ and the Euler identity on $\Re s>1$,
$$
D_\chi(s)=\frac{b_\chi}{s-1}-\frac{F_\chi'(s)}{F_\chi(s)}
=\sum_{n\ge1}q_\chi(n)n^{-s}.
$$
Fix the inherited $0<c_0\le1/20$. The ExcZ assumption says that in $\Re s\ge1-c_0/\ell(\Im s)$ all zeros of $F_\chi$ are exactly the members of $Z_\chi$, a set of at most one real simple zero, with $1-c_0/\ell(0)\le\beta<1$. The inherited family result gives at most one character-zero pair.

**Lemma (subtracted logarithmic derivative). [Lean, read]** Assume the uniform local zero formula below. For $t=\Im s$, $1-c_0/(2\ell(t))\le\Re s\le3$ and $s\notin Z_\chi$,
$$
\left|\frac{F_\chi'(s)}{F_\chi(s)}-\sum_{\beta\in Z_\chi}\frac1{s-\beta}\right|\le C\ell(t)^2
$$
with $C$ depending only on $c_0$ and the uniform inputs. This is **logDeriv_sub_exceptional_le** (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivSubExceptionalLe.lean:92–260).

*Proof.* For $\Re s<7/4$, put $z_t=5/4+it$, so $|s-z_t|\le1/2$. The local input supplies the finite set $W_t=\{w:|w-z_t|\le3/5,\ F_\chi(w)=0\}$ and the multiplicity bound $\sum_{w\in W_t}m(w)\le C_1\ell(t)$. At $s$ the function is nonzero by ExcZ, and the input gives
$$
\left|\frac{F_\chi'(s)}{F_\chi(s)}-\sum_{w\in W_t}\frac{m(w)}{s-w}\right|\le C_1\ell(t).
$$
For $w$ outside $Z_\chi$, the height difference is at most $3/5$, giving $\ell(\Im w)\le\ell(t)+\log(13/10)\le4\ell(t)/3$. The classified strip gives $\Re w<1-c_0/\ell(\Im w)$ and hence $\Re(s-w)\ge c_0/(4\ell(t))$. These terms cost at most $4C_1\ell(t)^2/c_0$. An exceptional zero in $W_t$ cancels with multiplicity one. An exceptional zero outside $W_t$ has $|s-\beta|\ge1/10$ by the difference of radii, so its subtraction costs at most $10$. For $\Re s\ge7/4$, the Euler series is bounded by $K_1=2\sum_{n\ge1}\Lambda(n)n^{-7/4}$, and each principal or exceptional reciprocal by $4/3$. The archive's $C=C_1+4C_1/c_0+10+K_1+3$ covers both ranges.

**Theorem (finite rectangle and uniform endpoints). [Lean, read]** For $u\ge2$ and $2\le T\le u$, put $r=1+1/\log u$, $\eta=c_0/(8\ell(T))$ and $H=C\ell(T)^2+2/\eta$. There exists $\sigma\in[1-4\eta,1-2\eta]$ such that
$$
\psi_\chi(u)=b_\chi u-\sum_{\substack{\beta\in Z_\chi\\\beta>\sigma}}\frac{u^\beta}{\beta}+R_\chi(u,T),
\qquad |R_\chi(u,T)|\le P\left(\frac{u(\log u)^2}{T}+\log u\right)+\frac{18Hu}{T}+4THu^\sigma .
$$
Here $P$ is the absolute coefficient Perron constant. Including all of $Z_\chi$ costs at most another $2u^{1-2\eta}$. If $\log B\le\sqrt{\log u}$, then
$$
\psi_\chi(u)=b_\chi u-\sum_{\beta\in Z_\chi}\frac{u^\beta}{\beta}+e_\chi(u),
\qquad |e_\chi(u)|\le C_7u e^{-c_7\sqrt{\log u}},
$$
where $c_7,C_7>0$ are uniform in the family, character and endpoint. The uniform claim is **psi_exceptional**, exported as **rayClassFamily_psi_with_exceptional_zero** (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyPsiWithExceptionalZero.lean:438–502 and src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyPsiWithExceptionalZeroStatement.lean:9–10).

*Rectangle proof.* Use $\sigma=1-2\eta$ for the empty set or for $\beta\le1-3\eta$, and $\sigma=1-4\eta$ otherwise. Then $|\sigma-\beta|\ge\eta$ and $1-\sigma\ge2\eta$. Throughout $\sigma\le\Re s\le r$, $|\Im s|\le T$, monotonicity gives $\ell(\Im s)\le\ell(T)$, hence $\sigma\ge1-c_0/(2\ell(\Im s))$. The only possible interior poles are $1$ and the real zero when $\beta>\sigma$. The horizontal edges have distance at least $T$ from these real points. Thus the specified height already avoids all zeros on the horizontal edges in this strip.

Write $J(s)=D_\chi(s)u^s/s$. At $1$, $F_\chi(1)\ne0$ by ExcZ, so the residue is $b_\chi u$. At a crossed zero factor $F_\chi(s)=(s-\beta)g(s)$ with $g(\beta)\ne0$. The logarithmic derivative is $1/(s-\beta)+g'(s)/g(s)$. Expanding $u^s/s=u^\beta/\beta+(s-\beta)h(s)$ with $h$ analytic gives residue $-u^\beta/\beta$. The kernel pole at zero lies outside the rectangle. For example, with a principal character and a conditional zero at $1-5\eta/2$, the actual choice is $\sigma=1-4\eta$. Its distance from the zero is $3\eta/2$. The two residues sum to $u-u^{1-5\eta/2}/(1-5\eta/2)$, and the left-side budget is $4THu^{1-4\eta}$. If instead $\beta=1-3\eta$, the chosen line is $1-2\eta$, and the zero term is supplied by the remainder allowance.

Let $A_\pm=\int_\sigma^r J(x\pm iT)\,dx$ and $V_x=\int_{-T}^T J(x+it)\,dt$. The positive boundary integral is $A_- - A_+ +iV_r-iV_\sigma$. The archive subtracts the principal parts, fills the removable singularities and applies Cauchy's rectangle theorem to the remainder. The integral of $1/(s-p)$ uses $\log(s-p)$ on the bottom, right and top and $\log(-(s-p))$ on the left. At the lower left the latter differs by $+i\pi$ and at the upper left by $-i\pi$, giving $2\pi i$ in the oriented boundary sum. Consequently
$$
\frac{V_r}{2\pi}=b_\chi u-\sum_{\substack{\beta\in Z_\chi\\\beta>\sigma}}\frac{u^\beta}{\beta}
+\frac{i(A_- - A_+)+V_\sigma}{2\pi}.
$$
On the three estimated sides the lemma and the reciprocal distances give $|D_\chi|\le H$. On each horizontal, $|s|\ge T$, $u^r=eu\le3u$, and the length is at most $3$ since $r\le3$. Each integral costs at most $9Hu/T$. On the left, $|s|\ge\sigma\ge1/2$ and the length is $2T$, giving $4THu^\sigma$. These are **shift**, **exists_line** and **contour** (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyPsiWithExceptionalZero.lean:14–125,160–355). A zero left of the line contributes no residue. Its endpoint term has size at most $2u^\sigma\le2u^{1-2\eta}$ because $\beta\ge1/2$.

*Perron truncation proof.* By positivity and $|\chi(g)|=1$, $|q_\chi(n)|\le2\Lambda(n)$. On the right, absolute convergence allows termwise integration by domination by a constant times $\sum_n|q_\chi(n)|n^{-r}$. For $y=u/n$ the normalized scalar kernel is
$$
K_{r,T}(y)=\frac1{2\pi}\int_{-T}^T\frac{y^{r+it}}{r+it}\,dt .
$$
The scalar input bounds its error against $\mathbf{1}_{y>1}$ for $y\ne1$ by $C_Ky^r\min(1,1/(T|\log y|))$. Take $C_K\ge1$. At $y=1$, the kernel is $\arctan(T/r)/\pi$, within $1$ of the inclusive indicator. Put $L=\log u$.

- For $n\le u/2$ or $n\ge2u$, use $|\log(u/n)|\ge1/2$, $\log n\le2L n^{1/(2L)}$, $u^r\le3u$, and $|q_\chi(n)|\le2\log n$. The errors sum to at most $24 C_K(uL/T)(1+2L)$ by the integral test for $\sum_{n\ge1}n^{-1-1/(2L)}$.
- For $u/2<n<2u$, use $y^r\le6$ and $\log n\le2L$. For $N=\lfloor u\rfloor$ the terms $N$ and $N+1$ each cost at most $32 C_K L$. For other terms put $k=N-n>0$ below or $k=n-(N+1)>0$ above. Then $|\log(u/n)|\ge |u-n|/\max(u,n)\ge k/(2u)$ and each term costs at most $32C_K L(2u/(Tk))$. Each harmonic sum is at most $1+L$, giving $32C_K L(2+(4u/T)(1+L))$ in total.

Adding with $L\ge1/2$ gives $P(uL^2/T+L)$ for $P=480 C_K$. This is the bound for $|\psi_\chi(u)-V_r/(2\pi)|$ including integer $u$, from **truncated_perron_of_le_two_vonMangoldt** (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronOfLeTwoVonMangoldt.lean:9–157).

*Uniformity proof.* Put $W=\sqrt{\log u}$ and $\delta=c_0/32$. If $\delta W\le1$, the inherited $\sum_{n\le u}\Lambda(n)\le2u$ yields $|\psi_\chi(u)|\le4u$. The main terms add at most $3u$, so $7u\le14u e^{-\delta W/2}$. Otherwise take $T=e^{\delta W}$. Here $2\le T\le u$, $W\ge1$, and $\ell(T)\le\log B+\log 2+\log T\le3W$. Thus $H\le K_2W^4$ for $K_2=9C+48/c_0$. Also $2\eta\log u=c_0 W^2/(4\ell(T))\ge c_0W/12\ge2\delta W$, giving $u^{1-2\eta}\le u/T^2$. This pays for the factor $T$ on the left edge. Using $u/T\ge1$, the combined error is at most $(2P+22K_2+2)uW^4/T$. The fourth Taylor term gives $W^4e^{-\delta W/2}\le24(2/\delta)^4$. The archive takes $c_7=\delta/2$ and $C_7=14+(2P+22K_2+2)24(2/\delta)^4$.

**Corollary (two endpoints and projection).** For $2\le X<Y$ and $\log B\le\sqrt{\log X}$, both endpoints meet the uniform hypotheses. Subtract to get
$$
\sum_{X<n\le Y}q_\chi(n)=b_\chi(Y-X)-\sum_{\beta\in Z_\chi}\frac{Y^\beta-X^\beta}{\beta}+e_\chi(Y)-e_\chi(X).
$$
The floors give $(X,Y]$ even when the endpoints are integers. The inherited orthogonality **sum_psi** (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrivialClassShortInterval.lean:103–113) gives
$$
|G|\sum_{X<n\le Y}\lambda(0,n)
=Y-X-\sum_\chi\sum_{\beta\in Z_\chi}\frac{Y^\beta-X^\beta}{\beta}
+\sum_\chi(e_\chi(Y)-e_\chi(X)).
$$
The double sum has zero or one term. The total remainder is bounded in modulus by $|G|C_7(Xe^{-c_7\sqrt{\log X}}+Ye^{-c_7\sqrt{\log Y}})$. For $Y\le2X$ this is at most $3BC_7Xe^{-c_7\sqrt{\log X}}$ before division, as in §17.4.10. After normalization the character factor cancels. Separation and deweighting are the earlier inputs of this chapter.

**Reading boundary.** Local R3 covers the direct endpoint, contour, coefficient Perron and subtracted logarithmic-derivative proofs, with the principal-part and rectangle proof bodies specified in the source map. The [Lean] inputs used at declaration level are **truncated_perron_kernel**, **rayClassLFunctionFamily_continuation_growth**, **rayClassFamily_logDeriv_re_gt_one**, **rayClassLFunction_logDeriv_local_formula** (its production is read in §17.4.12), and **sum_vonMangoldt_le_two_mul**. Their source locations and the direct continuation and Euler declarations are listed in the source map. Zaman's Theorem 1.1 and the remark after Corollary 1.2 give precedent for a shared family and a possible principal exceptional character. [Zaman, pp. 2–3](https://arxiv.org/pdf/1502.05679v4) · [Archive source map](../sources/SOURCES.md#p13-ray-class-endpoint-explicit-formula)

### 17.4.12 Producing the finite local zero formula

Sections 17.4.10 and 17.4.11 consumed one analytic input at declaration level: for every family $\mathcal F$, character $\chi$ and height $t$, the logarithmic derivative of $F_\chi$ near $5/4+it$ equals a finite sum over the zeros in a disk of radius $3/5$ plus a remainder of size $C\ell(t)$. It fixed the constant $C$ in the subtracted logarithmic derivative, and through it every constant of the endpoint formula. This subsection reads its production. The archive proves a generic statement on the unit disk, with explicit dependence on two radii, and then moves the unit disk by an affine map onto the disk of radius $7/10$ about $5/4+it$. The two radii $3/5$ and $1/2$ are the images of $6/7$ and $5/7$ under that map. The conductor and the height enter only through one logarithm.

**Two local calculations. [Expository]** Both use model functions with the shape of $F_\chi$ and exact rational arithmetic. They test the bookkeeping of the formula, not any property of an actual $L$-function.

1. *A simple zero and a boundary zero.* Take $t=0$, so the center is $z_0=5/4$, and the model $F(s)=(s-4/5)(3-s)$. The zero $4/5$ has distance $9/20$ from the center, inside both the zero disk of radius $3/5$ and the evaluation disk of radius $1/2$. The zero $3$ is at distance $7/4$ and is excluded. At $s=1$ the exact value is $F'(1)/F(1)=1/(1-4/5)-1/(3-1)=5-1/2=9/2$. The finite zero sum is $5$ and the remainder is $-1/2$. On the unit disk, with $f(z)=F(5/4+7z/10)$, one has $f(0)=F(5/4)=(9/20)(7/4)=63/80$ and a growth bound $M\le(9/20+7/10)(7/4+7/10)=1127/400$. The logarithmic budget is $L=\log(M/|f(0)|)=\log(1127\cdot 80/(400\cdot 63))\approx1.27$, and the count bound of the theorem below gives $N\le L/\log(7/6)\approx8.3$ for the actual $N=1$. Now move the zero to $3/5$. Its distance from the center is $13/20$, inside the growth disk of radius $7/10$ but outside the zero disk. It is not in the finite sum. At $s=1$ its reciprocal $1/(1-3/5)=5/2$ must be paid by the remainder. This is what the gap between the zero radius $6/7$ and the growth radius $1$ pays for in the generic theorem, through the two logarithms $\log(7/6)$ and $\log7$ below.

2. *A double zero next to the principal pole.* Take the principal character, $t=0$, and the model $F_1(s)=(s-9/10)^2(5/2-s)$. The factor $s-1$ has already removed the pole of $L_1$, so $F_1$ is analytic and the local formula applies to it. Then $D_1(s)=1/(s-1)-F_1'(s)/F_1(s)$. At $s=5/4$ the pole term is $4$, the zero sum with multiplicity two is $2/(5/4-9/10)=40/7$, and the remainder is $-1/(5/2-5/4)=-4/5$. Hence $F_1'/F_1(5/4)=40/7-4/5=172/35$ and $D_1(5/4)=4-172/35=-32/35$. If the double zero were counted once, the remainder would have to absorb an extra $20/7$ at $s=5/4$. At $s=9/10+\varepsilon$ it would have to absorb $1/\varepsilon$, which is $10$, $100$, $1000$ for $\varepsilon=1/10,1/100,1/1000$, while the true remainder stays between $-5/8$ and $-2/3$. On the unit disk, $f(0)=(7/20)^2(5/4)=49/320$, $M\le(21/20)^2(39/20)=17199/8000$, $M/|f(0)|=351/25$ and $L\approx2.64$. The count bound gives $N\le L/\log(7/6)\approx17.1$ for the actual $N=2$. The zero sits at $z=-1/2$ in the unit disk coordinate, inside radius $6/7$. The multiplicity enters the count through $|f(0)|\le R^N|g(0)|$: here $g(0)=(7/10)^2(5/4)=49/80$ and $(6/7)^2\cdot49/80=9/20\ge49/320$. A zero of order two costs two factors of $R$.

**Definitions.** For $f$ analytic near a point $w$, the order $m_f(w)$ is the exponent of the first nonzero Taylor coefficient, with $m_f(w)=0$ when $f(w)\ne0$. Mathlib's `analyticOrderNatAt` returns this natural number and returns $0$ for a function vanishing identically near $w$; the proofs below first exclude that case. For $0<r<R<1$ write
$$
c_1=\log\frac1R,\qquad c_2=\log\frac1{1-R},\qquad A=\frac{8R}{(R-r)^2},\qquad C(r,R)=\frac1{c_1}+A\left(1+\frac{c_2}{c_1}\right).
$$
For the ray-class family, $z_t=5/4+it$, $\ell(t)=\log(B(|t|+2))$, and $W_t=\{w:|w-z_t|\le3/5,\ F_\chi(w)=0\}$.

**Lemma 1 (stripping the zeros). [Lean, read]** Let $U\subseteq\mathbb C$ and let $f$ be analytic on a neighborhood of $U$. Let $S$ be a finite set of points of $U$ at each of which $f$ has finite order. There is $g$, analytic on a neighborhood of $U$, with
$$
f(z)=\prod_{w\in S}(z-w)^{m_f(w)}\,g(z)\quad\text{for all }z,\qquad g(w)\ne0\ \text{for all }w\in S.
$$
This is `exists_factor` (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormOneSubConjMul.lean:19–47), built on `exists_factor_order` (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsFactorOrder.lean:7–41).

*Proof.* One point first. Mathlib's characterization of finite order at $w$ gives $h_0$ analytic at $w$ with $h_0(w)\ne0$ and $f(z)=(z-w)^{m}h_0(z)$ near $w$, $m=m_f(w)$. Define $h(z)=f(z)/(z-w)^m$ for $z\ne w$ and $h(w)=h_0(w)$. Near $w$ this agrees with $h_0$, so $h$ is analytic at $w$. Away from $w$ it is a quotient of analytic functions with nonvanishing denominator. The identity $f=(z-w)^mh$ holds everywhere, at $w$ by the local expansion. Now induct on $S$. Given the factorization for $S$ and a new point $a\notin S$, the finite product $P_S(z)=\prod_{w\in S}(z-w)^{m_f(w)}$ is analytic and nonzero at $a$, so the order of $f$ at $a$ equals the order of the current $g$ at $a$ (Mathlib's additivity of orders under multiplication). Strip $a$ from $g$ by the one-point case. The new quotient is nonzero at $a$ by construction and nonzero at each old $w\in S$ because the old $g$ was nonzero there and $(w-a)^{m}\ne0$. $\square$

**Lemma 2 (the zero count from one logarithm). [Lean, read]** Let $f$ be analytic on a neighborhood of the closed unit disk, $f(0)\ne0$, $|f|\le M$ on the disk, and $0<R<1$. The set $Z_R=\{w:|w|\le R,\ f(w)=0\}$ is finite and $N=\sum_{w\in Z_R}m_f(w)$ satisfies $R^N\le M/|f(0)|$, that is, $N\le L/c_1$ with $L=\log(M/|f(0)|)$.

*Proof.* Since $f(0)\ne0$, the order at $0$ is $0$, hence finite. The closed unit disk is preconnected, so the order is finite at every point of it (Mathlib `AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected`). Zeros of an analytic function with finite orders are isolated, so the zero set is codiscrete in the disk and its intersection with the compact disk of radius $R<1$ is finite. Apply Lemma 1 with $S=Z_R$ to get $f=Pg$. At the origin $|f(0)|=\prod|w|^{m_f(w)}\,|g(0)|\le R^N|g(0)|$. To bound $|g(0)|$, use the reflected factors. For $|z|=1$ and any $w$, $|1-\bar wz|=|\bar z-\bar w|\,|z|=|z-w|$, which is `norm_one_sub_conj_mul` (`:117–123`). The function $G(z)=\prod_{w\in Z_R}(1-\bar wz)^{m_f(w)}g(z)$ is analytic on a neighborhood of the closed disk and satisfies $|G(z)|=|P(z)||g(z)|=|f(z)|\le M$ on the unit circle. The maximum modulus principle (`norm_le_of_sphere`, `:108–115`) gives $|g(0)|=|G(0)|\le M$. Hence $|f(0)|\le R^NM$, and taking logarithms gives $Nc_1\le L$. $\square$

**Lemma 3 (the remainder from Borel–Carathéodory). [Lean, read]** Let $0<r<R$, $K>0$, and let $g$ be differentiable and nonvanishing on the open disk $|z|<R$ with $|g(z)|\le|g(0)|e^K$ there. Then for $|z|\le r$,
$$
\left|\frac{g'(z)}{g(z)}\right|\le\frac{8R}{(R-r)^2}\,K .
$$
This is `norm_logDeriv_le` (`:49–106`).

*Proof.* The quotient $g'/g$ is differentiable on the disk. The disk is a ball, so it has a primitive $h$ with $h(0)=0$ (Mathlib's exactness on balls). The derivative of $g\,e^{-h}$ is $g'e^{-h}-g\,h'e^{-h}=0$, so $g(u)e^{-h(u)}=g(0)$ on the disk by connectedness, that is $g=g(0)e^h$. This is the branch choice: $h$ is the logarithm of $g/g(0)$ normalized to vanish at $0$, and no other branch is ever used. Taking moduli, $e^{\Re h(u)}=|g(u)|/|g(0)|\le e^K$, so $\Re h\le K$ on the disk. Mathlib's `Complex.borelCaratheodory_zero` gives $|h(u)|\le2K|u|/(R-|u|)$ for $|u|<R$. Fix $|z|\le r$ and put $\delta=(R-r)/2$. The closed disk of radius $\delta$ about $z$ lies in the open disk of radius $R$, since $|u|\le|z|+\delta\le r+\delta<R$. On its boundary circle $|u|<R$ and $R-|u|\ge R-r-\delta=\delta$, so $|h(u)|\le2KR/\delta$. Cauchy's estimate (Mathlib `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) gives $|h'(z)|\le2KR/\delta^2=8KR/(R-r)^2$, and $h'=g'/g$. $\square$

**Theorem 1 (the unit-disk formula with explicit constant). [Lean, read]** Fix $0<r<R<1$ and put $C=C(r,R)$. Let $f$ be analytic on a neighborhood of the closed unit disk with $f(0)\ne0$ and $|f|\le M$ on the disk, and let $L=\log(M/|f(0)|)$. Then $Z_R$ is finite,
$$
\sum_{w\in Z_R}m_f(w)\le C(1+L),
$$
and for every $z$ with $|z|\le r$ and $f(z)\ne0$,
$$
\left|\frac{f'(z)}{f(z)}-\sum_{w\in Z_R}\frac{m_f(w)}{z-w}\right|\le C(1+L).
$$
This is `GlobalTheory.LogDerivZeros.main` (`:125–241`).

*Proof.* Finiteness and $N\le L/c_1$ are Lemma 2, and $L/c_1\le C(1+L)$ since $1/c_1\le C$. Write $f=Pg$ as in Lemma 1 with $S=Z_R$. First bound $g$ on the unit circle. For $|u|=1$ and $w\in Z_R$, $|u-w|\ge1-|w|\ge1-R$, so $|P(u)|\ge(1-R)^N$ and $|g(u)|=|f(u)|/|P(u)|\le M/(1-R)^N$. By the maximum modulus principle the same bound holds on the closed disk. Next, $|f(0)|\le R^N|g(0)|\le|g(0)|$ because $R<1$. Therefore, for $|u|<R$,
$$
\frac{|g(u)|}{|g(0)|}\le\frac{M}{(1-R)^N|f(0)|}=\exp(L+Nc_2)\le\exp(1+L+Nc_2).
$$
The added $1$ makes the exponent positive, as Borel–Carathéodory requires. The function $g$ has no zero in the open disk of radius $R$: a zero of $f$ there belongs to $Z_R$ and has been divided out, and $g(w)\ne0$ at each such $w$ by Lemma 1. Lemma 3 with $K=1+L+Nc_2$ gives $|g'(z)/g(z)|\le AK$ for $|z|\le r$. Where $f(z)\ne0$, the product rule for logarithmic derivatives gives $f'/f=P'/P+g'/g$ and $P'(z)/P(z)=\sum_{w}m_f(w)/(z-w)$ (Mathlib `logDeriv_mul`, `logDeriv_prod`, `logDeriv_fun_pow`). Finally $N c_2\le c_2L/c_1$, so
$$
AK\le A\left(1+L+\frac{c_2}{c_1}L\right)\le A\left(1+\frac{c_2}{c_1}\right)(1+L)\le C(1+L).\qquad\square
$$

**Theorem 2 (the ray-class local formula). [Lean, read]** Assume the continuation and growth input and the Euler input of §17.4.11 at declaration level. Let $C_0=C(5/7,6/7)$ and $C=12C_0$. For every family $\mathcal F$, character $\chi$ and real $t$, the set $W_t$ is finite,
$$
\sum_{w\in W_t}m_{F_\chi}(w)\le C\,\ell(t),
$$
and for every $s$ with $|s-z_t|\le1/2$ and $F_\chi(s)\ne0$,
$$
\left|\frac{F_\chi'(s)}{F_\chi(s)}-\sum_{w\in W_t}\frac{m_{F_\chi}(w)}{s-w}\right|\le C\,\ell(t).
$$
This is `HkLocal.logDeriv_local`, exported as **rayClassLFunction_logDeriv_local_formula** (src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionLogDerivLocalFormula.lean:21–156 and src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionLogDerivLocalFormulaStatement.lean:8).

*Proof.* Put $\rho=7/10$ and $f(z)=F_\chi(z_t+\rho z)$. For $|z|\le1$ the point $w=z_t+\rho z$ has $\Re w\ge5/4-7/10=11/20>1/2$, so $f$ is analytic on a neighborhood of the closed unit disk by the continuation input, and the growth clause, valid for $\Re w\ge11/20$, gives $|F_\chi(w)|\le300B(|w|+1)^2$. Since $|w|+1\le5/4+|t|+7/10+1<|t|+3$, take $M=300B(|t|+3)^2$. At the center, $\Re z_t=5/4>1$, so the Euler input gives $F_\chi(z_t)=(z_t-1\text{ or }1)\cdot L(a_\chi,z_t)$ with $|L(a_\chi,z_t)|\ge((5/4-1)/(5/4))^2=1/25$ and $|z_t-1|\ge\Re(z_t-1)=1/4$. Hence $|f(0)|\ge1/100$, in particular $f(0)\ne0$.

The logarithmic budget is paid by $\ell(t)$ alone. Put $X=B(|t|+2)$, so $\ell(t)=\log X$ and $X\ge8$ because $B\ge4$. Then $\log X\ge1$. Also $(|t|+3)^2\le\tfrac94(|t|+2)^2$ and $X^2\ge4B(|t|+2)^2$, so $300B(|t|+3)^2\le675B(|t|+2)^2\le\tfrac{675}{4}X^2\le\tfrac{8^5}{100}X^2\le\tfrac1{100}X^7$, using $8^5\le X^5$. Dividing by $|f(0)|\ge1/100$ gives $M/|f(0)|\le X^7$ and
$$
1+L\le1+7\log X\le8\,\ell(t).
$$

Apply Theorem 1 with $r=5/7$, $R=6/7$. The orders are unchanged by the affine substitution, $m_f(z)=m_{F_\chi}(z_t+\rho z)$ (`analyticOrderNatAt_comp_affine`, `:11–19`), and $|z|\le6/7$ corresponds exactly to $|w-z_t|\le\rho\cdot6/7=3/5$. The map is injective, so the finite sum over $Z_{6/7}$ is the finite sum over $W_t$, and $\sum m\le C_0(1+L)\le8C_0\ell(t)\le C\ell(t)$. For $|s-z_t|\le1/2$ put $z=(s-z_t)/\rho$, so $|z|\le5/7$. The chain rule gives $f'(z)=\rho F_\chi'(s)$, and $m/(z-z_w)=\rho\,m/(s-w)$ for $w=z_t+\rho z_w$. Therefore
$$
\rho\left|\frac{F_\chi'(s)}{F_\chi(s)}-\sum_{w\in W_t}\frac{m_{F_\chi}(w)}{s-w}\right|\le8C_0\,\ell(t),
$$
and $8/\rho=80/7\le12$. $\square$

**Remarks.**

1. *The three radii.* The nesting is $1/2<3/5<7/10$, and the fourth radius is the analyticity margin: the growth disk of radius $7/10$ reaches $\Re w=11/20$, inside the continuation region $\Re w>1/2$ and exactly at the edge of the growth clause. In unit-disk coordinates these are $5/7<6/7<1$. Lemma 2 needs $R<1$ to make the count finite and to turn $\prod|w|^{m}\le R^N$ into a logarithm. Theorem 1 needs $1-R>0$ on the unit circle to bound $g$. Lemma 3 needs $R-r>0$ for the Cauchy circle. With $r=5/7$ and $R=6/7$, $c_1=\log(7/6)\approx0.154$, $c_2=\log7\approx1.946$, $A=8\cdot(6/7)\cdot49=336$, $C_0\approx4584$ and $C\approx5.5\times10^4$. The archive states $C$ existentially; the numerical value is our reading of the proof, not a declared constant.

2. *Multiplicity.* Orders enter at three places: in $P$, in $|f(0)|\le R^N|g(0)|$, and in $|g(u)|\le M/(1-R)^N$. A zero of order $k$ at $w$ costs $k$ factors $R$ in the count and $k$ factors $1/(1-R)$ in the remainder budget. Both are paid by the same $L$, since $N\le L/c_1$. The second calculation above shows that counting a double zero once leaves an unbounded error near the zero.

3. *Boundary zeros.* The zero set uses the closed disk $|w|\le R$, so a zero on the circle $|w|=R$ is in the finite sum. The remainder $g'/g$ is estimated on the open disk $|z|<R$, where $g$ has no zero, and evaluated on $|z|\le r<R$. A zero of $f$ with $R<|w|\le1$ stays inside $g$ and is paid by the remainder, as in the first calculation. The evaluation hypothesis $f(z)\ne0$ excludes only the points of the finite sum.

4. *Dependence on conductor and height.* The constant $C$ is absolute. The conductor $B$ and the height $t$ enter only through $M/|f(0)|\le X^7$, with $X=B(|t|+2)$, which is where $\ell(t)$ comes from. The lower bound $|f(0)|\ge1/100$ is uniform because the center has real part $5/4$, where the Euler input gives a product lower bound independent of $\chi$. For the principal character the removed pole contributes the factor $|z_t-1|\ge1/4$ rather than a singularity.

5. *Classical shape.* Montgomery and Vaughan, *Multiplicative Number Theory I*, Lemma 6.3 (p. 170), is the same statement with an unspecified constant depending on $r$ and $R$, proved from Jensen's inequality (Lemma 6.1, p. 168) and the Borel–Carathéodory lemma (Lemma 6.2, p. 169). The archive replaces Jensen by the reflected-factor maximum modulus argument of Lemma 2 and uses the Mathlib Borel–Carathéodory estimate. Their application to $\zeta$ uses $R=5/6$ and $r=2/3$, which are the radii the archive passes to the same `main` for its Riemann zeta and Dirichlet local zero sums. The disk theorem of Chapter 4, Lemma 4.11.1, is a different production for the `TailBox` component, with fixed ratios $r/3$ and $r/6$ and a Schwarz-lemma proof; it is not used here.

6. *Return to §§17.4.10–17.4.11.* Theorem 2 is the declaration consumed in Lemma 1 of §17.4.10 and in the subtracted logarithmic derivative of §17.4.11. With $C$ read as $12C_0$, the constant of `logDeriv_sub_exceptional_le` is $C_1+4C_1/c_0+10+K_1+3$ with $C_1=12C_0$, and the uniform constants $K_2$, $C_7$ of the endpoint formula follow as written there. Nothing in this subsection changes those derivations.

**Reading boundary.** Local R3 covers `LogDerivZeros.main` with `exists_factor`, `norm_logDeriv_le`, `norm_le_of_sphere` and `norm_one_sub_conj_mul`, the one-point stripping `exists_factor_order`, and the specialization `HkLocal.logDeriv_local` with `analyticOrderNatAt_comp_affine`. The two declaration-level inputs are **rayClassLFunctionFamily_continuation_growth** and **rayClassFamily_logDeriv_re_gt_one**; the continuation proof is read in [§17.4.13](#17413-mellin-continuation-and-uniform-growth-in-the-ray-class-family), and the Euler proof is read in [§17.4.14](#17414-euler-nonvanishing-and-the-center-of-the-local-disk). Mathlib's `Complex.borelCaratheodory_zero`, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, `AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected`, the codiscrete finiteness lemma, the exactness of differentiable functions on balls and the `logDeriv` algebra are used at declaration level. [Montgomery–Vaughan, Chapter 6](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/10.0_pp_168_198_The_Prime_Number_Theorem.pdf) · [Mathlib Borel–Carathéodory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/BorelCaratheodory.html) · [Archive source map](../sources/SOURCES.md#p13-ray-class-local-zero-formula)

### 17.4.13 Mellin continuation and uniform growth in the ray-class family

The disk in §17.4.12 extends to the left of absolute convergence. Its analytic input comes from counting ideals in each ray class. Every class has the same linear main term. Character summation cancels it in the nonprincipal branch and gives a simple pole in the principal branch. The error in the class counts controls the regularized function throughout the closed disk.

**Worked examples. [Expository]** Take the finite ray modulus $8$ over $\mathbb Q$. The ray group identifies opposite odd residues, giving class $0$ for $\{1,7\}$ and class $1$ for $\{3,5\}$, with addition modulo $2$. The class coefficients are the indicators of those residues. Take $\kappa=1/4$ and $B=4$ for both characters. For $x=8k+r$, $0\le r<8$, the count error in each class is the count in the first $r$ positions minus $r/4$, of modulus at most $2$.

1. *Principal character.* The count is $A_1(x)=\lfloor(x+1)/2\rfloor$, so $r_1=2\kappa=1/2$ and $|A_1(x)-x/2|\le1/2$. The series for $\Re s>1$ is $(1-2^{-s})\zeta(s)$ by removal of the even terms. In terms of the Mellin integral $J_1$ below, the regularization is $F_1(s)=s/2+(s-1)sJ_1(s)$. Thus $F_1(1)=1/2$ and $1/2$ is the original pole residue. Take $c=5/4+i$ and $s=c+(7/10)z$ with $|z|\le1$. At the left boundary $z=-1$ we have $s=11/20+i$. The bounded count error gives $|J_1(s)|\le(1/2)/(11/20)=10/11$ there and on the whole disk. The triangle inequality gives $|s|\le59/20$ and $|s-1|\le79/20$. Hence $|F_1(s)|\le59/40+(79/20)(59/20)(10/11)<13$. The family allowance is $300\cdot4\cdot(1+3)^2=19200$. At the center, the regularizing multiplier has modulus $|c-1|=\sqrt{17}/4\ge1/4$.
2. *Nonprincipal character.* Take $\chi(0)=1$ and $\chi(1)=-1$. The signs at $1,3,5,7$ are $1,-1,-1,1$, so $r_\chi=0$ and the successive running totals in each block are $0,1,0,-1,0$. Thus $|A_\chi|\le1$ and $F_\chi(s)=sJ_\chi(s)$. Partial summation at $1$ identifies $F_\chi(1)$ with the convergent signed reciprocal sum. Integrating each block of the geometric series on $[0,1]$ gives $F_\chi(1)=\int_0^1(1-u^2)/(1+u^4)\,du=\log(1+\sqrt2)/\sqrt2$. Each block contributes the integral of $u^{8k}(1-u^2)(1-u^4)\ge0$, and an antiderivative of the summed integrand is $\operatorname{artanh}(\sqrt2\,u/(1+u^2))/\sqrt2$. Now take $c=5/4-i$ with the same radius. The left boundary is $11/20-i$ and throughout the closed disk $|J_\chi(s)|\le20/11$. Hence $|F_\chi(s)|\le59/11<19200$. The center multiplier is $1$. Both examples have $X=B(|t|+2)=12$ and the same positive margin $11/20-1/2=1/20$ at the closed boundary. Invoking the same Euler center input as the consumer gives $|f(0)|\ge1/100$ in the principal case and $|f(0)|\ge1/25$ in the nonprincipal case. In both cases $100M=1920000<12^7=35831808$.

**Definitions.** In an `LFam`, let $G$ be the finite additive class group, $B\ge4$ the common size parameter with $|G|\le B$, and $1/B\le\kappa\le4$ the class density. Write $a_g(n)\ge0$ for the class coefficients. Its count field is $|A_g(x)-\kappa x|\le10\sqrt x$ for $x\ge1$, where $A_g(x)=\sum_{1\le n\le x}a_g(n)$. Set $a_\chi(n)=\sum_g\chi(g)a_g(n)$, $A_\chi(x)=\sum_{1\le n\le x}a_\chi(n)$ and $r_\chi=\kappa\sum_g\chi(g)$. Set $E_\chi(x)=A_\chi(x)-r_\chi x$ and $J_\chi(s)=\int_1^\infty E_\chi(x)x^{-s-1}\,dx$, with the real logarithm for positive $x$. These give the archive's twisted coefficients, residue and Mellin integral. Write $\ell(t)=\log(B(|t|+2))$. [Archive source map](../sources/SOURCES.md#p13-ray-class-mellin-continuation-and-growth)

**Lemma (Mellin transform of the count error). [Lean, read]** Under these hypotheses, $r_1=\kappa|G|$, $r_\chi=0$ for $\chi\ne1$, and $|r_\chi|\le4B$. The function $J_\chi$ is holomorphic for $\Re s>1/2$, with $|J_\chi(s)|\le10B/(\Re s-1/2)$. For $\Re s>1$ the absolutely convergent Dirichlet series is $L_\chi(s)=sJ_\chi(s)+sr_\chi/(s-1)$.

*Proof.* Translating the character sum by an element where $\chi$ differs from $1$ proves its vanishing in the nonprincipal case. For the principal character the sum is $|G|$. The residue bound follows from $\kappa\le4$ and $|G|\le B$. Now $E_\chi(x)=\sum_g\chi(g)(A_g(x)-\kappa x)$, so unit modulus gives $|E_\chi(x)|\le10|G|\sqrt x\le10B\sqrt x$. The count is a measurable step function. Taking absolute values in the integral reduces the bound to $10B\int_1^\infty x^{-\Re s-1/2}\,dx$.

Near a point with real part greater than $1/2$, choose a neighborhood with $\Re s\ge1/2+\eta$ for some $\eta>0$. The integrand and its complex derivative have the integrable majorants $10B x^{-1-\eta}$ and $10B x^{-1-\eta}\log x$, so one can differentiate under the integral. The formal proof uses the indicator of $(1,\infty)$, which vanishes near zero and has the square-root bound at infinity. It applies Mellin differentiability at $-s$ and composes with negation.

Positivity and the count give $\sum_{n\le x}|a_\chi(n)|\le\sum_g A_g(x)\le14|G|x$. For coefficients $b(n)$ with partial sum $S_b(x)$, finite partial summation writes $\sum_{n=1}^N b(n)n^{-s}=S_b(N)N^{-s}+s\int_1^N S_b(x)x^{-s-1}\,dx$. First use $b(n)=|a_\chi(n)|$ and the real exponent $\Re s>1$ to get absolute convergence. Then use $a_\chi$ and the complex exponent. The linear bound makes the endpoint term vanish as $N$ tends to infinity. Splitting the integral at the linear main term gives the asserted identity since $\int_1^\infty x^{-s}\,dx=1/(s-1)$. $\square$

**Theorem (regularized continuation and uniform disk bound). [Lean, read]** For an `LFam` with the count and size fields above, let $F_1(s)=r_1s+(s-1)sJ_1(s)$ and $F_\chi(s)=sJ_\chi(s)$ for $\chi\ne1$. These are holomorphic on $\Re s>1/2$. On $\Re s>1$ they agree with $(s-1)L_1(s)$ and $L_\chi(s)$ respectively. The principal continuation has a simple pole at $1$ with residue $r_1$, and the nonprincipal continuation is holomorphic there. For $\chi^2=1$ we have $F_\chi(\bar s)=\overline{F_\chi(s)}$ on the continuation domain. Uniformly in the family and the character, for $\Re s\ge11/20$ one has $|F_\chi(s)|\le300B(|s|+1)^2$. Consequently $f(z)=F_\chi(5/4+it+(7/10)z)$ is analytic on a neighborhood of $|z|\le1$ and satisfies $|f(z)|\le M=300B(|t|+3)^2$ there on the closed disk. With the separate Euler lower bound at the center as in §17.4.12, $1+\log(M/|f(0)|)\le8\ell(t)$.

*Proof.* The lemma supplies holomorphy and the agreement with the series. Since $F_1(1)=r_1=\kappa|G|>0$, dividing by $s-1$ recovers the stated pole. When $\chi^2=1$, the values of $\chi$ lie in $\{1,-1\}$, so $E_\chi$ and $r_\chi$ are real. Conjugation commutes with the integral and replaces $s$ by $\bar s$ in the kernel. The archive also states this identity for its totalized integral definition outside the continuation domain.

On the closed growth half-plane $\Re s-1/2\ge1/20$, so $|J_\chi(s)|\le200B$. Write $u=|s|$. The nonprincipal bound is $200Bu$. For the principal branch, $|s-1|\le u+1$ and $|r_1|\le4B$ give $200Bu(u+1)+4Bu$. Both bounds are at most $300B(u+1)^2$ for $u\ge0$. These are the two branches of `RayCont.continuation_growth`. [Archive source map](../sources/SOURCES.md#p13-ray-class-mellin-continuation-and-growth)

For the consumer `HkLocal.logDeriv_local`, write $c=5/4+it$ and $\rho=7/10$. On $|z|\le1$, $\Re(c+\rho z)\ge5/4-7/10=11/20>1/2$ and $|c+\rho z|+1\le5/4+|t|+7/10+1=|t|+59/20\le|t|+3$. This proves the neighborhood and growth requirements, including the closed left edge. At $z=0$ we are at $\Re c=5/4>1$, where the series agreement applies. The separate Euler input gives $|L_\chi(c)|\ge((5/4-1)/(5/4))^2=1/25$. The regularizing multiplier is at least $1/4$ in modulus in either branch, so $|f(0)|\ge1/100$.

With $X=B(|t|+2)\ge8$, the inequalities $(|t|+3)^2\le(9/4)(|t|+2)^2$ and $B\le B^2/4$ give $M/|f(0)|\le100M\le16875X^2\le X^7$. Now $\log X\ge1$ gives the desired logarithmic budget. The inherited disk result uses radii $5/7$ and $6/7$ in the $z$ coordinate, corresponding to $1/2$ and $3/5$ in the $s$ coordinate. Its error scales by $1/\rho$, so the inherited constant $C_0$ gives $(8/\rho)C_0=(80/7)C_0\le12C_0$. The zero count uses $8C_0$ before the common enlargement. $\square$

**Notes.**

1. *Verifying the example family.* Take $\lambda_g(n)=\Lambda(n)$ for odd $n$ in class $g$ and zero otherwise. The support checks the values at $0$ and $1$, nonnegativity, and $\sum_g\lambda_g(n)\le2\Lambda(n)$. At odd $n$, class addition and $\sum_{d\mid n}\Lambda(d)=\log n$ verify the class convolution. At even $n$ the odd-supported products vanish. For the square field, convolution of the principal sequence with a real twisted sequence at odd $n$ is $\prod_{p^e\parallel n}(1+\chi(p)+\cdots+\chi(p)^e)$. The factors are nonnegative for $\chi(p)=\pm1$ and at least $1$ at $n^2$. At positive even $n$ and at $0$, the support gives zero. This checks both square inequalities. For the exponential field, the two geometric series in each class sum to $\cosh(kv)/\sinh(4v)$ for $0<v\le1$, with $k=3$ and $1$ for the respective classes. Over the denominator $4v\sinh(4v)\ge16v^2$, the numerator of the difference from $1/(4v)$ has modulus at most $4v(9v^2/2)\cosh(4)+(4v)^3\cosh(4)/6$ by Taylor's theorem. Hence the difference is at most $((9/8)+(2/3))\cosh(4)\,v<4^{10}v$. Together with the count, $|G|=2\le B$ and $\kappa=1/B=1/4$, this checks the family fields.
2. *The modulus in the actual ray family.* For the imaginary quadratic construction, $d=|D_K|$ and the modulus is $m\mathcal O_K$, with $d$ prime, $d\equiv3\bmod4$, $d\ge100$ and $m\ge3$. The archive assigns $B=4dm^2$ and $\kappa=2\pi/(\sqrt d\,m^2)$. Each primitive inducing conductor divides the fixed modulus of norm $m^2$. Thus the proof budgets the discriminant and full modulus simultaneously, with the same $B$ for every character. The modulus variable in the construction is distinct from the disk allowance $M$. The small rational examples instantiate the abstract family. [Zaman, §2.1, p. 6](https://arxiv.org/pdf/1502.05679v4) · [Archive source map](../sources/SOURCES.md#p13-ray-class-mellin-continuation-and-growth)
3. *Uniformity and scope.* A pointwise estimate with its constant chosen after the character or family can contribute an uncontrolled $\log C_{\mathcal F,\chi}$ to the disk budget. An estimate only at the center leaves the closed circle uncontrolled. The supplied bound holds for the entire circle, with the same numerical constant before every choice of family, character, height and disk coordinate. The holomorphy assertion concerns $\Re s>1/2$. The classical fractional-part integral for $\zeta$ illustrates the summatory-error calculation. Zaman gives the classical primitive Hecke functional equation and a conductor-dependent convexity estimate. [NIST DLMF 25.2.8](https://dlmf.nist.gov/25.2.E8) · [Zaman, §2.1 and Lemma 2.1, pp. 6–7](https://arxiv.org/pdf/1502.05679v4)
4. *Reading boundary.* Local R3 covers the complete continuation and growth proof and its in-file helpers, the exporting wrapper and the direct consumer interface. The disk zero sum and its constants are inherited from §17.4.12. The Euler producer is read in [§17.4.14](#17414-euler-nonvanishing-and-the-center-of-the-local-disk). The concrete family's count and arithmetic suppliers retain their separate read boundaries. Imported Mathlib theorems are used through their statements. [Archive source map](../sources/SOURCES.md#p13-ray-class-mellin-continuation-and-growth)

### 17.4.14 Euler nonvanishing and the center of the local disk

The local zero formula needs a quantitative nonzero value at $c=5/4+it$. At this center the class convolution gives a differential equation for the twisted series. Normalizing its solution at the far right produces a logarithm. Comparison with the real zeta series bounds its real part from below, while differentiation gives the weighted series used in the endpoint formula.

**Worked examples. [Expository]** Use the finite ray modulus $8$ over $\mathbb Q$ with no real place in the modulus. Its classes are the two pairs of opposite odd residues $\{1,7\}$ and $\{3,5\}$. This is the family verified in §17.4.13, with $B=4$, $\kappa=1/4$, $a_g(n)$ the class indicator and $\lambda_g(n)=a_g(n)\Lambda(n)$. The principal conductor is $1$. The sign character has conductor $8$, since it takes opposite values at $1$ and $5$, which agree modulo $4$.

Write $x_p=p^{-5/4}$. For either character at $c=5/4+it$, each inverse factor has modulus at least $(1+x_p)^{-1}\ge1-x_p$. Absolute convergence allows passage from the finite inequalities to the full tail

$\displaystyle \left|\prod_{p>5}(1-\chi(p)p^{-c})^{-1}\right|\ge\prod_{p>5}(1-x_p)\ge\frac{1}{5(1-x_2)(1-x_3)(1-x_5)}.$

Here the tail product on the right equals $\zeta(5/4)^{-1}/[(1-x_2)(1-x_3)(1-x_5)]$ and the integral test gives $\zeta(5/4)\le5$.

1. *Principal character at height zero.* The prime $2$ is omitted, so its factor is $1$. At $3$ and $5$ the factors at $c=5/4$ are $(1-x_3)^{-1}$ and $(1-x_5)^{-1}$. Summing the powers of these primes gives the weighted contribution $(\log3)x_3/(1-x_3)+(\log5)x_5/(1-x_5)$. The full principal series is $(1-2^{-s})\zeta(s)$. The regularization at the center gives $f(0)=L_1(5/4)/4$ and the pole correction in the weighted identity is $1/(c-1)=4$. Multiplying the finite factors and the tail bound gives $|f(0)|\ge1/[20(1-x_2)]>1/20$. With the inherited $M=10800$ this yields $M/|f(0)|<216000<8^7$, with $\ell(0)=\log8$.
2. *Sign character at height one.* Take $c=5/4+i$ and $y_p=x_p e^{-i\log p}$. The prime $2$ is again omitted. Both $3$ and $5$ have sign $-1$, so their factors are $(1+y_3)^{-1}$ and $(1+y_5)^{-1}$. The squared modulus of each is $(1+2x_p\cos(\log p)+x_p^2)^{-1}$, hence its modulus is at least $(1+x_p)^{-1}$. The weighted contribution of each is $-(\log p)y_p/(1+y_p)$ by the geometric series. Here $f(0)=L_\chi(c)$. The two finite bounds and the tail give $|f(0)|\ge1/[5(1-x_2)(1-x_3^2)(1-x_5^2)]>1/5$. With $M=19200$ this gives $M/|f(0)|<96000<12^7$, with $\ell(1)=\log12$.

**Definitions.** Fix a single §17.4.13 family $\mathcal F$, with finite additive group $G$, common budget $B\ge4$, $|G|\le B$, and $1/B\le\kappa\le4$. Keep all the `LFam` fields, including the exponential estimate and the two real-character square inequalities. For the Euler calculation we use the class counts and $a_g(n)\ge0$, $a_g(0)=0$, $a_0(1)=1$, $a_g(1)=0$ for $g\ne0$, together with

$\displaystyle \lambda_g(n)\ge0,\qquad \sum_g\lambda_g(n)\le2\Lambda(n),\qquad a_g(n)\log n=\sum_{h\in G}\sum_{de=n}\lambda_h(d)a_{g-h}(e)\quad(n\ge1).$

Here $\Lambda(p^k)=\log p$ on positive powers of rational primes and is zero elsewhere. For any character $\chi$ of $G$, write $a_\chi(n)=\sum_g\chi(g)a_g(n)$ and $\lambda_\chi(n)=\sum_g\chi(g)\lambda_g(n)$. Put $L_\chi(s)=\sum_{n\ge1}a_\chi(n)n^{-s}$ and $D_\chi(s)=\sum_{n\ge1}\lambda_\chi(n)n^{-s}$, with the real logarithm for positive bases. Keep the same $F_\chi$ as in §17.4.13, with its series agreement on $\Re s>1$. [Archive source map](../sources/SOURCES.md#p13-ray-class-euler-nonvanishing-and-center-bound)

**Lemma (the exponential from convolution). [Lean, read]** Let $a(n)$ and $b(n)$ have absolutely convergent Dirichlet series $A(s)$ and $D(s)$ for $\Re s>1$. Assume $a(1)=1$, $b(1)=0$ and $a(n)\log n=\sum_{de=n}b(d)a(e)$. Then $H(s)=\sum_{n\ge2}b(n)n^{-s}/\log n$ converges absolutely there, $A=e^H$ and $-A'/A=D$.

*Proof.* Since $\log n\ge\log2$ for $n\ge2$, the series for $H$ converges absolutely. On any compact subset of the half-plane compare with absolute convergence at a real exponent $\sigma_0>1$ strictly less than the smallest real part on that subset. The same comparison gives uniform convergence of the derivative series because $(\log n)n^{-\delta}$ is bounded for every $\delta>0$, using the gap above $\sigma_0$. Termwise differentiation gives $H'=-D$ and $A'=-DA$, the latter by the absolutely convergent convolution product. Thus $(Ae^{-H})'=0$ on the connected half-plane. On the real axis as $s$ tends to $+\infty$, the tails are dominated by absolute convergence at $\sigma_0$, so $A(s)$ tends to $1$ and $H(s)$ tends to $0$. The constant is therefore $1$. This is the normalization in the archive's `eq_exp_of_conv`. $\square$

**Theorem (right-half-plane and disk-center supply). [Lean, read]** For every such family, character, and $s$ with $\sigma=\Re s>1$, both $L_\chi$ and $D_\chi$ converge absolutely and

$\displaystyle |L_\chi(s)|\ge\left(\frac{\sigma-1}{\sigma}\right)^2>0,\qquad F_\chi(s)\ne0,\qquad D_\chi(s)=-\frac{F_\chi'(s)}{F_\chi(s)}+\begin{cases}1/(s-1)&\chi=1,\\0&\chi\ne1.\end{cases}$

For the ray-coefficient realization at a fixed modulus $\mathfrak m$, $L_\chi$ is the absolutely convergent Euler product over prime ideals $\mathfrak p\nmid\mathfrak m$. For every real $t$, set $c=5/4+it$ and $f(z)=F_\chi(c+(7/10)z)$. Then $|f(0)|\ge1/100$, with the branch bounds $|c-1|/25$ and $1/25$ for the principal and nonprincipal cases respectively. With the inherited closed-disk allowance $M=300B(|t|+3)^2$,

$\displaystyle 1+\log\frac{M}{|f(0)|}\le8\ell(t),\qquad \ell(t)=\log(B(|t|+2)).$

*Proof.* The absolute convergence of $L_\chi$ is the right-half-plane clause of §17.4.13. The triangle inequality, unit character modulus and positivity of $\lambda_g$ give $|\lambda_\chi(n)|\le2\Lambda(n)$. This implies $\lambda_\chi(1)=0$ and absolute convergence of $D_\chi$, since $\Lambda(n)\le\log n$. Normalization gives $a_\chi(1)=1$. Multiply the class convolution by $\chi(g)$ and sum over $g$. For each $h$, translate to $u=g-h$ and use $\chi(g)=\chi(h)\chi(u)$. It follows that $a_\chi(n)\log n=\sum_{de=n}\lambda_\chi(d)a_\chi(e)$. The lemma gives $L_\chi=e^{H_\chi}$ and $-L_\chi'/L_\chi=D_\chi$, with $H_\chi(s)=\sum_{n\ge2}\lambda_\chi(n)n^{-s}/\log n$.

For the ray realization, $a_g$ counts nonzero integral ideals coprime to $\mathfrak m$ by class and norm. The weight $\lambda_g(n)$ sums $\log N\mathfrak p$ over prime powers $\mathfrak p^k$ of that class and norm. Class and norm multiply and $\log N(\mathfrak p^k)=k\log N\mathfrak p$, so

$\displaystyle H_\chi(s)=\sum_{\mathfrak p\nmid\mathfrak m}\sum_{k\ge1}\frac{\chi([\mathfrak p])^k}{k(N\mathfrak p)^{ks}}.$

The absolute sum before grouping is bounded by $\sum_{n\ge2}2\Lambda(n)n^{-\sigma}/\log n$ using the family weight field. The power series $\sum_{k\ge1}u^k/k$ exponentiates to $(1-u)^{-1}$ for $|u|<1$. Exponentiating the absolutely summable logarithms therefore gives the Euler product with factors $(1-\chi([\mathfrak p])(N\mathfrak p)^{-s})^{-1}$. The weighted series has terms $(\log N\mathfrak p)\chi([\mathfrak p])^k(N\mathfrak p)^{-ks}$ with absolute convergence by the weight bound before division by $\log n$. [Zaman, §2.1, p. 6](https://arxiv.org/pdf/1502.05679v4)

To bound $L_\chi$, put $R_\sigma=\sum_{n\ge2}\Lambda(n)n^{-\sigma}/\log n$. Since $\sum_{d\mid n}\Lambda(d)=\log n$ by prime factorization, the lemma with $a(n)=1$ and $b(n)=\Lambda(n)$ gives $e^{R_\sigma}=\zeta(\sigma)$. By the integral test $\zeta(\sigma)\le1+\int_1^\infty x^{-\sigma}\,dx=\sigma/(\sigma-1)$. The weight bound gives $|H_\chi(s)|\le2R_\sigma$, hence

$\displaystyle |L_\chi(s)|=e^{\Re H_\chi(s)}\ge e^{-2R_\sigma}=\zeta(\sigma)^{-2}\ge\left(\frac{\sigma-1}{\sigma}\right)^2.$

In the principal branch $F_1(s)=(s-1)L_1(s)$ on the open half-plane, and both factors are nonzero there. Differentiating gives $F_1'/F_1=1/(s-1)+L_1'/L_1$. In the other branch $F_\chi=L_\chi$ and $F_\chi'/F_\chi=L_\chi'/L_\chi$. This proves the weighted identity.

At $\sigma=5/4$ the bound for $L_\chi$ becomes $1/25$. The principal multiplier satisfies $|c-1|=\sqrt{1/16+t^2}\ge1/4$, and the other multiplier is $1$. Thus $|f(0)|\ge1/100$. In `HkLocal.logDeriv_local` the projection `.2.1` of `rayClassFamily_logDeriv_re_gt_one` supplies the bound for $L_\chi(c)$ before multiplication. The consumer uses the inherited series agreement to perform the multiplication and prove center nonvanishing. With $X=B(|t|+2)\ge8$,

$\displaystyle \frac{M}{|f(0)|}\le100M\le30000\cdot\frac94 B(|t|+2)^2\le16875X^2\le X^7.$

Here $(|t|+3)/(|t|+2)\le3/2$ and $B\ge4$. Taking logarithms and using $\log X\ge1$ gives the asserted budget. The consumer uses it in the disk theorem of §17.4.12 with the analyticity and growth of §17.4.13. Scaling the derivative remainder by $10/7$ gives $80/7\le12$ after inserting the budget factor $8$, and the unscaled multiplicity count fits the common factor $12$ as well. $\square$

**Notes.**

1. *The producing calls.* `Hk.LogDeriv.logDeriv_F` exports the weighted identity and the bound for $L_\chi$ together. Its `norm_ge_of_conv` uses `eq_exp_of_conv` and the real series comparison `LLower.norm_LSeries_le`. The weighted identity uses `hasDerivAt_of_conv` and the two branches of series agreement. The center bound for $F_\chi$ is proved in the local consumer. The separate `LLower.norm_LFunction_ge` concerns Dirichlet characters and is outside this call chain. The prime-ideal product is the interpretation of the exponential identity for ray coefficients. The formal argument uses the convolution fields of the abstract family. [Archive source map](../sources/SOURCES.md#p13-ray-class-euler-nonvanishing-and-center-bound)
2. *Full modulus and inducing conductor.* For the archive's imaginary quadratic family $\mathfrak m=m\mathcal O_K$ with $m\ge3$, $d=|D_K|\ge100$ prime and $d\equiv3\bmod4$. Its fields include $B=4dm^2$ and $\kappa=2\pi/(\sqrt d\,m^2)$. The uniform lower bound uses the $2\Lambda$ field. Growth and the logarithmic budget use the full $B$. If $\chi^\circ$ denotes the primitive inducing character of conductor $\mathfrak f_\chi\mid\mathfrak m$, passing from its $L$-function to the one at modulus $\mathfrak m$ multiplies by $\prod_{\mathfrak p\mid\mathfrak m,\ \mathfrak p\nmid\mathfrak f_\chi}(1-\chi^\circ(\mathfrak p)(N\mathfrak p)^{-s})$, by canceling the common factors. The principal example exhibits this correction at $2$. The rational examples instantiate the abstract family conditions. [Zaman, §2.1, p. 6 and Lemma 4.1, p. 12](https://arxiv.org/pdf/1502.05679v4)
3. *Domains and reading scope.* The weighted series identity is for $\Re s>1$. In the larger disk the local formula estimates the logarithmic derivative of the continued $F_\chi$ away from its zeros. The pole correction concerns $L_1$. The classical zeta product and differentiated series give the degree-one comparison, and the family square comes from the weight bound $2\Lambda$. Local R3 covers the direct Euler producer and real series comparison, its forwarding statement, and the consumer's center and budget. Continuation, growth and the generic disk theorem are inherited. The count producer `rayCountTheta` is read in [§17.4.15](#17415-ray-class-size-and-theta-counts-at-a-fixed-modulus). The producers `lamRay_props`, `aRay_mul_log` and `conv_real_char` are read in [§17.4.16](#17416-the-ideal-level-weight-lamray-its-convolution-and-the-real-character-square); the imported Mathlib theorems retain their declaration-level boundaries here. [NIST DLMF (25`.2.1`1)](https://dlmf.nist.gov/25.2.E11) · [NIST DLMF (25.2.6)](https://dlmf.nist.gov/25.2.E6) · [Archive source map](../sources/SOURCES.md#p13-ray-class-euler-nonvanishing-and-center-bound)

### 17.4.15 Ray-class size and theta counts at a fixed modulus

The input to §17.4.13 is a count **in each ray class**. A finite quotient bounds the number of classes. A different calculation counts the ideals of each norm inside a class. In the imaginary quadratic construction the latter is a count of points in a translated planar lattice. The covolume changes with the chosen ideal representative, and the conversion from generator norm to ideal norm cancels that change. This yields one density for the entire family.

**Examples. [Expository]** All norm fibres in the following examples are given by the formulas below, including empty fibres.

1. *Finite modulus $8$ over $\mathbb Q$.* The ordinary class group is trivial. The four unit residues $1,3,5,7$ split into the unit orbits $\{1,7\}$ and $\{3,5\}$. The image of $\{1,-1\}$ has order two, and the subgroup congruent to $1$ is trivial. For each $n\ge1$, the only ideal of norm $n$ is $(n)$. Its class is determined by the orbit of $n$ for odd $n$. Both fibres are empty at even $n$ and at $n=0$. With inverse-class representatives $(1)$ and $(3)$, the generators are $1+8k$ and $9+24k$ for $k\in\mathbb Z$. Their ideal norms are $|1+8k|$ and $|3+8k|$, respectively. For example, the norm-$7$ generator is $-7$ in the first class and the norm-$5$ generator is $-15$ in the second. Each generator fibre is a singleton whenever its ideal exists. Including the real place instead requires a positive generator. In the residue-sign group the orbits are $\{(r,+),(-r,-)\}$ for each odd $r$, and one obtains four classes with a single positive residue per class.

   For the finite modulus, the densities are $\kappa=2/8=1/4$ and the abstract budget is $B=4$, with $|G|=2$ and $1/B=\kappa$. For $y=8j+r$, $0\le r<8$, the exact counts are $2j+\mathbf1_{r\ge1}+\mathbf1_{r\ge7}$ and $2j+\mathbf1_{r\ge3}+\mathbf1_{r\ge5}$. Their deviations from $y/4$ are at most $2$. The two theta sums are $(e^{-t}+e^{-7t})/(1-e^{-8t})$ and $(e^{-3t}+e^{-5t})/(1-e^{-8t})$, or $\cosh(3t)/\sinh(4t)$ and $\cosh(t)/\sinh(4t)$. For $0<t\le1$ and $k=1,3$, subtract $1/(4t)$ over the denominator $4t\sinh(4t)\ge16t^2$. Taylor's theorem bounds $|4t\cosh(kt)-\sinh(4t)|$ by $(2k^2+64/6)\cosh(4)t^3$. This gives an error bounded by $(9/8+2/3)\cosh(4)t<4^{10}t$. With the real place included, each density is $1/8$, and the theta sum for residue $r$ is $e^{-rt}/(1-e^{-8t})$.

2. *Modulus $3\mathcal O$ over $K=\mathbb Q(\sqrt{-103})$.* Here $d=103$ is prime, $d\equiv3\pmod4$, and $\omega=(1+\sqrt{-103})/2$ has minimal polynomial $X^2-X+26$. It is irreducible modulo $3$, so $\mathcal O/3\mathcal O$ is the field of nine elements. The integer norm of $u+v\omega$ is $(u+v/2)^2+103v^2/4$. It follows that $\mathcal O^\times=\{1,-1\}$, both with distinct images modulo $3$. The congruence subgroup is trivial, and each nonzero residue has trivial stabilizer under the two units. The four residue orbits have representatives $1,\omega,1+\omega,1+2\omega$.

   The ordinary class number is $5$. Indeed the imaginary quadratic Minkowski bound $2\sqrt{103}/\pi<7$ gives an integral ideal of norm at most $6$ in every class. The polynomial has distinct roots $0,1$ modulo $2$, while modulo $3$ and $5$ it is irreducible. With $P=(2,\omega)$ and $\bar P=(2,\omega-1)$, the representatives are therefore $\mathcal O,P,\bar P,P^2,\bar P^2$, since $P\bar P=(2)$. If two of these classes agree, then $P^j$ is principal for some $1\le j\le4$. A generator would have norm $2^j\le16$, hence would be rational by the norm formula. A rational generator has equal valuations at $P$ and $\bar P$, which is impossible. This proves distinctness. The five ideals have bases $(a,\omega-r)$ where $(a,r)=(1,0),(2,0),(2,1),(4,2),(4,3)$, respectively. The last two roots modulo $4$ lift the roots $0,1$ modulo $2$. The ideals they define have index $4$, and containment in the corresponding prime above $2$ and coprimality to its conjugate identify them as the two squares. [Milne, Algebraic Number Theory, §4, Theorem 4.3 and Proposition 4.27](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

   These five ideals $J$ and four residues give all $20$ ray classes. For residue $\rho=u+v\omega$ on the list, the class is $[(\rho)][J]^{-1}$. Let $C_0=v$ and let $A_0$ be the unique integer in $\{0,1,2\}$ congruent to $a^{-1}(u+rv)$ modulo $3$. The complete fibre at norm $n$ is obtained from
   $A=A_0+3m$, $C=C_0+3k$, $m,k\in\mathbb Z$, by imposing
   $n=((aA+(1/2-r)C)^2+103C^2/4)/a$.
   The corresponding ideal is $(aA+(\omega-r)C)J^{-1}$. For instance, $(a,r,\rho)=(1,0,1)$ gives the unit ideal at $n=1$. The choice $(2,0,1)$ gives $A_0=2,C_0=0$ and $A=-1,C=0$ at $n=2$, yielding $(2)P^{-1}=\bar P$. Every ideal in a given fibre occurs once. Its generators with residue in the orbit of $\rho$ occur in opposite pairs, and the residue $\rho$ selects exactly one.

   The theta sum in each class is the sum of $e^{-tn}$ over these $(m,k)$, using the displayed polynomial for $n$. To read its constants set $\ell=(1/2-r)/a$, $\theta_1=(A_0+\ell C_0)/3$ and $\theta_2=C_0/3$. The two quadratic coefficients are $\alpha=9a$ and $\gamma=927/(4a)$, with product $8343/4$. Thus the count and theta densities are $\kappa=2\pi/(9\sqrt{103})$ for all twenty classes. The exact size is $5(9-1)/2=20$, the intermediate bound is $5\cdot9=45$, and the archive takes $B=4\cdot103\cdot9=3708$, with $B\kappa=8\pi\sqrt{103}$. The coefficient of the linear principal-character count is $20\kappa=40\pi/(9\sqrt{103})$. The estimates below give $10\sqrt y$ and $3708^{10}t$ for the two class errors.

**Definitions.** Write $\mathcal O=\mathcal O_K$, let $\mathfrak m$ be a nonzero proper integral ideal, and let $S$ be the set of real places included in the modulus. The ideal group $I^{\mathfrak m}$ consists of fractional ideals with valuation zero at every prime dividing $\mathfrak m$. Divide by the principal ideals generated by elements locally congruent to $1$ at the prime powers in $\mathfrak m$ and positive at every place of $S$. Denote this ray group by $G_{\mathfrak m,S}$ and put $U_{\mathfrak m,S}=\{u\in\mathcal O^\times:u\equiv1\pmod{\mathfrak m},\ \sigma(u)>0\text{ for }\sigma\in S\}$. Congruence for a fractional element is taken in the local rings at the modulus primes. Use $N$ for absolute ideal norm. The coefficient $a_g(n)$ counts nonzero integral ideals $I$ coprime to $\mathfrak m$ with $[I]=g$ and $NI=n$. Put $A_g(y)=\sum_{1\le n\le y}a_g(n)$ and $\Theta_g(t)=\sum_{n\ge0}a_g(n)e^{-tn}$. The archive's finite modulus has $S=\varnothing$ and $\mathfrak m=M\mathcal O$. [Milne, Class Field Theory, Chapter V, §1](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

**Lemma (the two fibres).** The fibre of $G_{\mathfrak m,S}\to\mathrm{Cl}(K)$ over any ordinary class is a torsor for
$((\mathcal O/\mathfrak m)^\times\times\{\pm1\}^{S})/\operatorname{im}(\mathcal O^\times)$,
where units act by their residues and real signs. Consequently
$|G_{\mathfrak m,S}|=h_K\,2^{|S|}N\mathfrak m\prod_{\mathfrak p\mid\mathfrak m}(1-1/N\mathfrak p)/[\mathcal O^\times:U_{\mathfrak m,S}]$.
For a ray class $g$, choose a nonzero integral ideal $J$ coprime to $\mathfrak m$ with ray class $g^{-1}$. Then the generators in
$X_J=\{z\in J:z\equiv1\pmod{\mathfrak m},\ \sigma(z)>0\text{ for }\sigma\in S\}$
map onto the ideals of ray class $g$ by $z\mapsto(z)J^{-1}$. The fibre over an ideal is a free orbit of $U_{\mathfrak m,S}$. Its norm parameter is $|N_{K/\mathbb Q}z|/NJ$.

*Proof.* Every ordinary ideal class has an integral representative prime to the specified primes. For example, take an integral ideal in its inverse class and choose an element with exactly the ideal's valuations at the modulus primes, by approximation, then divide its principal ideal by that ideal. Approximation also realizes every combination of residue units and real signs by an element of $K^\times$ that is a local unit at the modulus primes. Map its residue and sign tuple to the ray class of its principal ideal. The tuple determines that class, because the ratio of two lifts has residue $1$ and positive signs. The image consists of the ordinary principal classes. A tuple maps to the ray identity exactly when the lift differs from a ray-principal generator by a global unit. This identifies the kernel as the unit image and proves the first assertion by translation in the ray group. The cardinality follows from the Chinese remainder theorem, since the nonunits modulo $\mathfrak p^e$ are the $N\mathfrak p^{e-1}$ multiples of $\mathfrak p$.

An integral representative of any ray class can be obtained by clearing a fractional ideal's denominators with an integral element congruent to $1$ at the modulus primes and positive at $S$. The congruences are compatible by the Chinese remainder theorem, and adding a sufficiently large positive rational integer divisible by all the congruence ideals ensures positivity. With $J$ fixed, $IJ$ is ray principal precisely when $[I]=g$. Its generator is integral and belongs to $J$ since $IJ\subseteq J$. Conversely, $z\in X_J$ is nonzero, and $(z)\subseteq J$ makes $(z)J^{-1}$ integral. It is coprime to $\mathfrak m$ by the local residue of $z$, and its class is $g$. Two such generators give the same ideal exactly when their ratio is a unit of residue $1$ and positive signs. A unit fixing a nonzero element is the identity. Norm multiplicativity gives the asserted parameter. For $S=\varnothing$, choose $z_0\in J$ congruent to $1$, using $J+\mathfrak m=\mathcal O$. Then $X_J=z_0+\mathfrak m J$ by $J\cap\mathfrak m=\mathfrak m J$. For nonempty $S$ take the part of this coset in the required real sign region. $\square$ [Milne, Class Field Theory, Chapter V, Proposition 1.6 and Theorem 1.7](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

**Theorem (the count fields of the concrete family). [Lean, read]** Let $d\ge100$ be prime with $d\equiv3\pmod4$, let $[K:\mathbb Q]=2$ with $x^2=-d$ for some $x\in K$, and fix an integer $M\ge3$. Use the coefficients of a single `RayData K M` at the finite modulus $M\mathcal O$. Put $B=4dM^2$ and $\kappa=2\pi/(\sqrt d M^2)$. Then $|G|\le B$, $B\ge4$, and $1/B\le\kappa\le4$. For each $g$, the norm fibres are finite, the theta sum is absolutely convergent for $t>0$, and

$\displaystyle |A_g(y)-\kappa y|\le10\sqrt y\quad(y\ge1),\qquad |\Theta_g(t)-\kappa/t|\le B^{10}t\quad(0<t\le1).$

*Proof.* The field is imaginary quadratic of discriminant $-d$. The archive identifies $D.G$ with the finite ray quotient by taking an integral representative for each label and using `D.cls_eq` to compare labels. In the fractional group, the inverse of a coprime integral ideal $I$ can be represented by $(b)I^{-1}$ with $b\in I$, $b\equiv1\pmod{M\mathcal O}$, so the identification reaches the whole quotient. The finite ray relation can equally be expressed by cross multiplication with two integral generators congruent to $1$, after clearing local-unit denominators. The lemma gives the size bound $h_KN(M\mathcal O)=h_K M^2$ before the unit and residue savings. The archive instead proves this bound by an injection. It chooses one ideal in each ordinary-class fibre of the ray quotient. A representative $I$ in that fibre is related to the chosen $J$ by $(x)I=(y)J$. Pick $j\in J$ congruent to $1$. Then $yj\in(x)$, so $b=yj/x$ is integral, $(j)I=(b)J$, and $b$ is a unit at the modulus primes. The ordinary class and residue of $b$ distinguish ray classes, because equal residues yield ray-equivalent principal ideals. This is the injection used by `rayNo_bounds`. For degree two the archive's class-number comparison bounds $h_K$ by $s(1+\log s)\le s^2$, where $s=\sqrt{|D_K|}\ge1$ and $\log s\le s-1$. The weaker $h_K\le4|D_K|$ is the bound actually fed to `card_ray_le`. Here $N(M\mathcal O)=M^2$ by the norm of the rational scalar $M$.

For the norm count choose the inverse ray representative $J$ separately for each $g$. In the complex embedding every unit has absolute value $1$. If $u=1+Mw$ with $w\ne0$, then $|u-1|=M|w|\ge M$ by $|w|^2=N_{K/\mathbb Q}w\in\mathbb Z_{\ge1}$, whereas $|u-1|\le2$. Thus $U_{M\mathcal O,\varnothing}=\{1\}$. The ideal-generator map is a bijection, and the affine lattice in the lemma now counts ideals without a multiplicity divisor.

Use a complex embedding and put $L=MJ$, viewed as a lattice in $\mathbb C$. An integral basis of $\mathcal O$ is $1,(1+x)/2$ and has area $\sqrt d/2$. Passing to $L$ multiplies area by the index $M^2NJ$, giving area $V=M^2NJ\sqrt d/2$. The archive supplies a basis $f_1,f_2$ of $L$ with $|f_1|^2\le2V$. One can obtain this inequality by choosing a shortest nonzero vector, which is primitive, completing it to a basis, and changing the second vector by an integer multiple of the first so that its parallel component has length at most $|f_1|/2$. Since the resulting second vector has length at least $|f_1|$, its perpendicular length is at least $\sqrt3|f_1|/2$. This gives the claimed inequality. The change of lattice basis reindexes the whole coset by $\mathbb Z^2$.

Projecting parallel and perpendicular to $f_1$ writes $|z_0+mf_1+kf_2|^2/NJ$ as

$\displaystyle Q(m,k)=\alpha(m+\theta_1+\ell k)^2+\gamma(k+\theta_2)^2,\qquad \alpha=|f_1|^2/NJ,\quad \gamma=V^2/(|f_1|^2 NJ).$

In fact, $\ell$ is the parallel coefficient of $f_2$ along $f_1$, $\theta_1$ the corresponding coefficient of $z_0$, and $\theta_2$ the ratio of the perpendicular components of $z_0$ and $f_2$. The ideal $(f_1)$ is contained in $MJ$, so $|f_1|^2\ge M^2NJ$. The short basis gives $\gamma\ge V/(2NJ)=M^2\sqrt d/4\ge1$. Hence both coefficients are at least $1$ and $\sqrt{\alpha\gamma}=V/NJ=M^2\sqrt d/2$. The norm identity in the lemma shows that $Q$ takes positive integer values and $a_g(n)=\#\{(m,k):Q(m,k)=n\}$. The disk of squared radius $yNJ$ in the generator plane has area $\pi yNJ$. Dividing by $V$ gives exactly $\kappa y$.

To bound the discrete count, set $R=\sqrt{y/\gamma}$. Only rows with $|k+\theta_2|\le R$ contribute, and each row is a bounded interval in the first coordinate. Its integer count differs by at most $1$ from its length $w(k+\theta_2)$, where $w(u)=2\sqrt{\max(0,y-\gamma u^2)/\alpha}$. There are at most $2R+1$ such rows. Compare the shifted sum of $w$ with its integral on consecutive unit intervals whose left endpoints are the sample points. The error lies between the negative of the total increase of $w$ and its total decrease. Indeed on each interval the integral minus the sampled value lies between the negative downward variation and the upward variation there. The function increases to $w(0)$ and then decreases to zero, so either bound has magnitude at most $w(0)$. The integral is $\pi y/\sqrt{\alpha\gamma}$ by rescaling the semicircle. The total error is at most $2R+1+2\sqrt{y/\alpha}\le5\sqrt y$, which implies the archive allowance $10\sqrt y$. This argument also proves finiteness of the positive integer norm fibres. Grouping the points below $y$ by their value of $Q$ gives the finite sum up to $\lfloor y\rfloor$.

For the theta count, Poisson summation for the translated Gaussian gives

$\displaystyle \sum_{m\in\mathbb Z}e^{-s(m+\theta)^2}=\sqrt{\pi/s}\sum_{j\in\mathbb Z}e^{-\pi^2 j^2/s}e^{2\pi i j\theta}\qquad(s>0).$

The relative error from the nonzero frequencies is at most $s^2$. Indeed $e^{-v}\le2/v^2$ for $v>0$, so after using $1/j^4\le1/j^2$ the error is bounded by $(2s^2/\pi^4)\sum_{j\ne0}1/j^2=2s^2/(3\pi^2)$. Apply this first with $s=\alpha t$ and shift $\theta_1+\ell k$. The zero-frequency term is independent of the row. Multiply its uniform error by the nonnegative row weights $e^{-\gamma t(k+\theta_2)^2}$, and sum. These weights are summable by the same Gaussian identity with $s=\gamma t$. The row bounds prove convergence of the two-dimensional sum. Writing $a=(\alpha t)^2$ and $c=(\gamma t)^2$, the product error is bounded by $\kappa(a+c+ac)/t$: the outer weight sum is at most $\sqrt{\pi/(\gamma t)}(1+c)$, and its own relative error in the constant row term is at most $c$. Regroup by the positive integer norm using absolute convergence. This is the infinite fibre transfer, which uses the Gaussian estimate directly and is independent of the sharp-cutoff error. [NIST DLMF §1.8(iv), (1.8.14)](https://dlmf.nist.gov/1.8.E14)

Finally $\alpha,\gamma\ge1$ imply $\kappa\le\pi$ and $\alpha,\gamma\le\alpha\gamma$. For $t\le1$ the error is at most $3\pi(\alpha\gamma)^2t=(3\pi/16)d^2M^8t\le B^{10}t$. The fixed parameter bounds give $B\ge4$, $B\kappa=8\pi\sqrt d\ge1$, and $\kappa\le4$. The unique ideal of norm $1$ is $\mathcal O$, in the identity class, and there are no ideals of norm zero. Counting gives nonnegativity. In `ExistsLFamRay.lean:97–123`, passing from $D.G$ to its additive form transfers `card_le`, the two bounds on $\kappa$, and the two projections of `rayCountTheta` to `count` and `theta`. The same $a_g$ appears in both fields. $\square$ [Archive source map](../sources/SOURCES.md#p13-ray-class-size-and-theta-counts)

**Notes.**

1. *Order of choices.* Fix $d,M$ and the ray group before any class, norm, theta parameter or character. The representative $J$, the congruence lift $z_0$ and the basis may depend on the class. Choose them in that order before taking norm fibres or summing. The area divided by $NJ$ and all the stated bounds are independent of those choices. The class-number injection uses a separate choice over the **ordinary** class group.
2. *Infinite places and a failed hypothesis.* The sign factor and the unit image enter together. For $\mathbb Q$ at $8$, adding the real place doubles the class count and halves the class density. In the imaginary quadratic theorem there are no real places to add. Dropping the triviality of the congruence unit subgroup invalidates the undivided lattice count. For $K=\mathbb Q(\sqrt{-103})$ and $M=2$, both units are congruent to $1$. In the identity class with $J=\mathcal O$, the norm-$1$ ideal has two generators $1,-1$ in $1+2\mathcal O$, and the lattice theta sum has twice the ideal theta sum. Its ideal density is $\pi/(4\sqrt{103})$, after dividing the lattice density by two. Also, a finite ray relation concerns the full modulus and its exponents. Using $(2)$ in place of $(8)$ over $\mathbb Q$ leaves the same primes excluded but makes all odd residues a single class.
3. *Nonprimitive modulus.* A character is chosen after fixing the family. Its primitive inducing conductor divides the full modulus, including the applicable real-place conditions. Passing from the primitive series to the full-modulus series removes the prime-ideal factors for $\mathfrak p\mid\mathfrak m$ with $\mathfrak p\nmid\mathfrak f_\chi$. The multiplier is $\prod_{\mathfrak p\mid\mathfrak m,\ \mathfrak p\nmid\mathfrak f_\chi}(1-\chi^\circ(\mathfrak p)(N\mathfrak p)^{-s})$. Primes already omitted at the conductor cause no additional factor, and real signs affect the inducing character with no finite Euler factor of their own. A principal pole residue is multiplied by the value of this finite product at $1$. In the rational example the principal conductor is $1$, and the multiplier is $1-2^{-s}$. The other character takes different values on $1$ and $5$, so it does not descend modulo $4$ and has conductor $8$. In the quadratic example the principal conductor omits the inert prime $(3)$ of norm $9$, giving multiplier $1-9^{-s}$. Its value $8/9$ converts the total density at the trivial modulus, $5\pi/\sqrt{103}$, into $20\kappa$. Here the trivial-modulus density follows by the same area computation with $J$ an ordinary-class representative, omitting the zero generator and dividing by the two units. The family coefficients, $B$ and $\kappa$ remain tied to $M\mathcal O$. [Zaman, §2.1 and Lemma 4.1](https://arxiv.org/pdf/1502.05679v4)
4. *Reading boundary.* This subsection reads the finite ray-size injection, the direct ideal-to-lattice count, the row and Gaussian estimates and their two fibre transfers. The deeper class-number lattice estimate, the archive's plane-basis reduction and its integral-basis construction remain named inputs. The productions `lamRay_props`, `aRay_mul_log` and `conv_real_char`, supplying the remaining weight, convolution and real-character square fields, are read in [§17.4.16](#17416-the-ideal-level-weight-lamray-its-convolution-and-the-real-character-square). §§17.4.12–17.4.14 supply the downstream local formula, continuation, growth, Euler nonvanishing, weighted derivative and disk budget. [Archive source map](../sources/SOURCES.md#p13-ray-class-size-and-theta-counts)

### 17.4.16 The ideal-level weight: `lamRay`, its convolution, and the real-character square

Section 17.4.14 used three fields of `LFam` at declaration level: `lam_nonneg`, `lam_le` and `conv`
(the weighted convolution identity), together with the real-character square clause `sq`. For the
concrete ray-coefficient family of §17.4.15 these are supplied by three named but previously unread
productions: `lamRay_props` (file relocated below; the archive's own import graph puts the proof in
`ExistsLFamRay.lean`, not in `SumLamIdealLe.lean`, which instead supplies an auxiliary bound used
inside it), `aRay_mul_log`, and `conv_real_char`. This subsection reads all three bodies and explains
why the ideal weight $\lambda(g,n)$ cannot be the integer von Mangoldt function $\Lambda(n)$ reindexed
by class: a rational prime that splits produces **two** ideals of the same norm, each independently
weighted, so the per-class and total weights at that norm can exceed $\Lambda(n)$ even though every
individual contribution is a $\log$ of a rational prime.

**Why ideal weight is not integer weight. [Expository]** Over $K=\mathbb Q(\sqrt{-103})$ the rational
prime $2$ splits as $\mathfrak p\bar{\mathfrak p}$ with $N\mathfrak p=N\bar{\mathfrak p}=2$ (both are
established as the class representatives of $a=2,r=0$ and $a=2,r=1$ in §17.4.15). Each of
$\mathfrak p,\bar{\mathfrak p}$ is a prime ideal power with $k=1$, so each has ideal weight $\log 2$.
Summing over classes at $n=2$ gives $\sum_g\lambda(g,2)=2\log2$, matching the family bound
$\sum_g\lambda(g,n)\le2\Lambda(n)$ of $\mathrm{LFam}$ **with equality**. There is no single rational
integer of norm $2$ carrying weight $2\log2$; the identity $\Lambda(2)=\log2$ is a statement about the
integer $2$, while $\lambda(g,2)$ is a statement about one ideal of norm $2$ in one class. Reindexing
$\Lambda$ directly by class and norm would silently merge two distinct geometric objects (and would
be wrong by a factor of $2$ exactly at split primes), which is why the archive routes the weight
through `lamIdeal`, defined ideal by ideal, and proves the $2\Lambda$ bound as a genuine inequality
rather than an identity.

**Definitions (restated from the archive). [Lean]** Fix a number field $K$ of degree $2$, a modulus
$M\ge1$ and a `RayData K M` record $D$ with group $D.G$. For $g\in D.G$ and $n\in\mathbb N$,
$$
\mathrm{idealsIn}(g,n)=\{I\subseteq\mathcal O_K:I\neq0,\ I\ \text{coprime to}\ M\mathcal O_K,\ NI=n,\ D.\mathrm{cls}(I)=g\},
$$
$$
\mathrm{lamIdeal}(I)=\begin{cases}\log(N\,\mathrm{rad}(I))&\text{if }I=P^k\text{ for some prime ideal }P\neq0\text{ and some }k\ge1,\\0&\text{otherwise,}\end{cases}
$$
$$
a_g(n)=\#\mathrm{idealsIn}(g,n),\qquad \lambda_g(n)=\sum_{I\in\mathrm{idealsIn}(g,n)}\mathrm{lamIdeal}(I).
$$
(`idealsIn`, `lamIdeal`, `aRay`, `lamRay`, `LamIdealOfNotPrimePow.lean:94–104`.) Since $\mathrm{rad}(P^k)=P$,
$\mathrm{lamIdeal}(P^k)=\log NP$ for every $k\ge1$: the weight depends on the underlying prime, not on
the exponent. Both sets are finite because `Ideal.finite_setOf_absNorm_eq` bounds the ideals of a
fixed norm.

**Lemma (support and the $2\Lambda$ bound: `lamRay_props`). [Lean, read]** For $K=\mathbb Q(\sqrt{-d})$
with $d\ge100$ prime, $d\equiv3\pmod4$, a square root $x\in K$ of $-d$, $[K:\mathbb Q]=2$, $M\ge3$, and
any `RayData K M` instance $D$: (i) $\lambda_g(n)\ge0$ for all $g,n$; (ii) $\sum_g\lambda_g(n)\le2\Lambda(n)$
for all $n\ge1$; (iii) if $p$ is a rational prime and $\lambda_1(p)\neq0$ (weight at the identity class
and norm exactly $p$), then $p$ satisfies the quadratic form condition `NormOne d M p`: there exist
integers $A,B$ with $A^2+dB^2=4p$, $M\mid B$ and $2M\mid A-2-B$.
(`lamRay_props`, relocated to `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLFamRay.lean:135–170`;
the file named in the predecessor's source map, `SumLamIdealLe.lean`, instead holds the auxiliary bound
`sum_lamIdeal_le` used inside clause (ii), at line 38–80 of that file.)

*Proof.* (i) is immediate since every `lamIdeal` value is a nonnegative real logarithm or zero. For (ii), fix
$n$ and let $T$ be the (finite) set of ideals of norm $n$ across all classes that are prime-ideal powers.
Every prime $P$ dividing such an ideal also divides $(\,\mathrm{minFac}(n)\,)$, because a degree-$2$ field
has $N P\mid p^2$ for the rational prime $p$ below $P$ (`pow_prime_norm`, using that
$\mathrm{absNorm}(\mathrm{span}\{p\})=p^{[K:\mathbb Q]}=p^2$ and that $NP\mid p^2$ with $NP>1$ forces
$NP=p$ or $p^2$), and $n$ being a prime-ideal-power norm forces $n$ itself to be a prime power $p^k$ with
$p=\mathrm{minFac}(n)$. The radicals of the (at most two, by coprimality of distinct maximal ideals above
the same prime) members of $T$ are pairwise coprime divisors of the single prime ideal above $p$ raised
to the first power; their product of norms therefore divides $p^2$, giving
$\prod_{I\in T}N\,\mathrm{rad}(I)\le p^2$ and hence, after taking logarithms,
$\sum_{I\in T}\log N\,\mathrm{rad}(I)\le2\log p=2\Lambda(n)$. Summing the class-disjoint union
$\bigsqcup_g\mathrm{idealsIn}(g,n)=T$ (ideals in distinct classes are automatically distinct, so the union
is disjoint and covers exactly the prime-power ideals of norm $n$) gives (ii). For (iii), $\lambda_1(p)\neq0$
forces $\mathrm{idealsIn}(1,p)$ nonempty; take $I$ in it. The identity-class membership `cls_eq_one_iff`
supplies $a,b\in\mathcal O_K$ nonzero with $a-1,b-1\in M\mathcal O_K$ and $(a)I=(b)$. Writing $b=a\pi$ for
some $\pi\in I$ (using $(b)\subseteq(a)$) and using $a-1\in M\mathcal O_K$ shows $\pi-1\in M\mathcal O_K$
after a short computation ($\pi-1=(a\pi-1)-\pi(a-1)$). The explicit integral basis of $\mathcal O_K$
(`exists_gen`: every $z\in\mathcal O_K$ is $u+v\omega$ with $4N(u+v\omega)=(2u+v)^2+dv^2$) applied to $\pi$
turns $\pi\equiv1\pmod M$ and $N(\pi)=\pm p$ (so $N(\pi)=p$, since the right side is a sum of squares) into
exactly the two congruences of `NormOne d M p` with $A=2u+v$, $B=v$. $\square$

**Lemma (ideal convolution: `aRay_mul_log`). [Lean, read]** For $K$ of degree $2$, $M\ge2$, a `RayData`
instance $D$, $g\in D.G$ and $n\in\mathbb N$,
$$
a_g(n)\log n=\sum_{h\in D.G}\sum_{\substack{d,e\ge1\\de=n}}\lambda_h(d)\,a_{g/h}(e).
$$
(`aRay_mul_log`, `FiniteIdealsIn.lean:82–134`.)

*Proof.* Both sides are finite sums indexed by ideals. On the left, every ideal $I$ in the class-$g$,
norm-$n$ fibre satisfies $a_g(n)\log n=\sum_{J\mid I}\mathrm{lamIdeal}(J)$ by `sum_lamIdeal`
(an induction on the unique factorization of $I$: at a prime factor $P^{k+1}\|I$, splitting the divisors
of $I$ into those dividing $I/P$ and those of the form $P\cdot(\text{divisor of }I/P)$ reduces the claim
to $\log N(I)=\log N(P)+\log N(I/P)$, with the single extra term $\mathrm{lamIdeal}(P^{k+1})=\log NP$
coming from the top power of $P$). Summing this identity over the finite class-$g$, norm-$n$ fibre and
reorganizing by the pair $(J,I/J)$ gives the right side termwise: a bijection sends the triple
$(J$ dividing $I$, $I$ in the fibre$)$ to $(J,I/J)$, landing $J$ in $\mathrm{idealsIn}(h,d)$ and $I/J$ in
$\mathrm{idealsIn}(g/h,e)$ for $h=D.\mathrm{cls}(J)$, $d=NJ$, $e=N(I/J)$, because
$D.\mathrm{cls}$ is multiplicative on coprime-to-$M$ ideals and $N$ is multiplicative; the inverse sends
$(J,K)$ with $NJ=d$, $NK=e$, $de=n$ to $I=JK$. This bijection is exactly `Finset.sum_bij` applied in the
file, matching divisor pairs on each side. $\square$

**Lemma (real-character square: `conv_real_char`). [Lean, read]** For $K$ of degree $2$, $M\ge2$, a
`RayData` instance $D$ and a group homomorphism $\varepsilon:D.G\to\{\pm1\}$ with $\varepsilon(1)=1$,
for every $n\ge1$,
$$
0\le\sum_{\substack{d,e\ge1\\de=n}}\Big(\sum_g a_g(d)\Big)\Big(\sum_g\varepsilon(g)a_g(e)\Big),\qquad
\sum_g a_g(n)\le\sum_{\substack{d,e\ge1\\de=n^2}}\Big(\sum_g a_g(d)\Big)\Big(\sum_g\varepsilon(g)a_g(e)\Big).
$$
(`conv_real_char`, `ConvRealChar.lean:361–416`.)

*Proof sketch.* Write $\chi(I)=\varepsilon(D.\mathrm{cls}\,I)$ for $I$ coprime to $M$ and $0$ otherwise;
$\chi$ is completely multiplicative on ideals ($\chi(IJ)=\chi(I)\chi(J)$, by multiplicativity of
$D.\mathrm{cls}$ and of $\varepsilon$) and takes only the values $0,\pm1$. For a multiplicative,
$\{0,\pm1\}$-valued function $f$ with $f(1)=1$, write $r_f(C)=\sum_{J\mid C}f(J)$. A direct induction on
the prime factorization of $C$ (`r_pow`, `r_bounds`) shows $r_f(C)=\prod_{P^k\|C}\big(\sum_{i=0}^kf(P)^i\big)$
is always $\ge0$ (each geometric factor is $0$, $k+1$, or alternates $\ge0$, by `geom_bounds`), and
$r_f(C^2)\ge1$ (each squared factor is a sum over an *odd* number $2k+1$ of terms of a value in $\{0,\pm1\}^i$
raised to even power $\ge1$, hence $\ge1$ by `geom_bounds`'s second clause). Taking $f=\chi$, the left sum of
the theorem is $\sum_{I\ \mathrm{coprime}}\chi_1(I)\,r_\chi(I)$ over ideals of norm $n$ (nonnegative
termwise since $\chi_1(I)\in\{0,1\}$ and $r_\chi(I)\ge0$); the right inequality compares the same quantity
at $n$ against its value at $n^2$ using $r_\chi(I^2)\ge1$ and the injectivity of $I\mapsto I^2$. The
rewriting from ideal sums to the stated double sums over integer divisors uses the same `conv_eq` bijection
as `aRay_mul_log` (grouping ideals by norm). $\square$

**Worked computation 1 (modulus $8$ over $\mathbb Q$). [Expository, computed]** Here $\mathcal O_K=\mathbb Z$
is a PID, so every ideal is $(n)$ for a unique $n\ge0$, and $P$ ranges over $(p)$, $p$ prime. A nonzero
ideal $(n)$ is a prime-ideal power exactly when $n$ is a prime power integer $p^k$ ($k\ge1$), in which case
$\mathrm{lamIdeal}((n))=\log p=\Lambda(n)$ in the classical sense; otherwise both sides are $0$. So for
$K=\mathbb Q$, $\lambda$ restricted to the trivial class ($G=\{\pm1\}$ orbits mod $8$, as in §17.4.13) is
literally the classical von Mangoldt function, split by residue. This is consistent with `OddFam.fam` in
`LamIdealOfNotPrimePow.lean:212–265`, which takes $\mathrm{lam}\,g\,n=a_0(n)\Lambda(n)$ directly, bypassing
`lamRay` because $\mathbb Z$ has no norm collisions: no rational integer is simultaneously a prime power
in two different ways, so clause (ii) of `lamRay_props` holds here with $\sum_g\lambda_g(n)=\Lambda(n)\le2\Lambda(n)$,
never at equality for $n>1$. Two explicit values: $\lambda_1(9)=\mathrm{lamIdeal}((9))=\log3$ (since
$(9)=(3)^2$, radical $(3)$, norm $3$; target class: $9\equiv1\pmod8$, so the identity class), and
$\lambda_1(12)=0$ (since $(12)=(2)^2(3)$ is not a prime-ideal power — $12$ is divisible by two distinct
primes — matching $\Lambda(12)=0$ exactly).

**Worked computation 2 ($K=\mathbb Q(\sqrt{-103})$, modulus $3\mathcal O$). [Expository, computed]**
Continue the setup of §17.4.15 Example 2: $\omega=(1+\sqrt{-103})/2$, $N(u+v\omega)=u^2+uv+26v^2$, class
number $5$ with representatives $\mathcal O,\mathfrak p,\bar{\mathfrak p},\mathfrak p^2,\bar{\mathfrak p}^2$
at $(a,r)=(1,0),(2,0),(2,1),(4,2),(4,3)$, and residue orbits $\{1\},\{\omega\},\{1+\omega\},\{1+2\omega\}$ of
$(\mathcal O/3\mathcal O)^\times\cong\mathbb F_9^\times$ modulo $\{\pm1\}$ (the units of $\mathcal O$ are
exactly $\{\pm1\}$, as computed in §17.4.15, and $3$ is coprime to $M=3$... no: $3$ is the modulus prime
itself and is excluded below). Units are trivial at $M=3$: if $u=1+3w$ were a nontrivial unit,
$|u-1|=3|w|\ge3$ while every unit has complex absolute value $1$, so $|u-1|\le2$; hence $U_{3\mathcal O,\varnothing}=\{1\}$,
and every principal ideal coprime to $3$ has a *unique* generator congruent to $1\bmod3\mathcal O$ up to sign.

Legendre symbols $\left(\dfrac{-103}{p}\right)$ for $p=2,3,5,103$ (checked directly: $X^2-X+26\bmod2$ has
roots $0,1$; $(-103/3)=-1$; $(-103/5)=-1$; $103$ is the ramified prime):

| $p$ | splitting | ideal(s) above $p$ | ordinary class | $N$ | weight contributed |
|---|---|---|---|---|---|
| $2$ | split | $\mathfrak p=(2,\omega)$, $\bar{\mathfrak p}=(2,\omega-1)$ | $(a,r)=(2,0)$ and $(2,1)$ | $2,2$ | $\log2$ each, at $n=2$ |
| $3$ | inert | $(3)$ | — | $9$ | **excluded**: $3\mid M$, not coprime to the modulus |
| $5$ | inert | $(5)$ | $(1,0)$, principal | $25$ | $\log5$, at $n=25$ |
| $103$ | ramified | $\mathfrak q=(\sqrt{-103})$ | $(1,0)$, principal | $103$ | $\log103$, at $n=103$ (and again at $n=103^2$ from $\mathfrak q^2=(103)$, same weight $\log103$, not $2\log103$) |

Target ray classes, using that $U_{3\mathcal O,\varnothing}=\{1\}$ makes the fibre lemma's generator unique:

- *$p=2$.* $\mathfrak p\cdot\bar{\mathfrak p}=(2)$ is principal with generator $2$. Reducing $2$ modulo
  $3\mathcal O$ gives the residue class of $-1\cdot1$ (since $2\equiv-1\pmod3$), i.e. the $\rho=1$ orbit.
  By the fibre lemma of §17.4.15 (choosing $J=\bar{\mathfrak p}$ for $\mathfrak p$ and $J=\mathfrak p$ for
  $\bar{\mathfrak p}$, each the representative of the inverse class, so that $\mathfrak p\cdot J=\bar{\mathfrak p}\cdot J=(2)$
  is the natural principal ideal), the norm parameter is $|N(2)|/NJ=4/2=2$, matching $N\mathfrak p=2$ exactly.
  So $\mathfrak p$ lands in ray class $(a,r,\rho)=(2,0,1)$ and $\bar{\mathfrak p}$ in $(2,1,1)$, each
  carrying weight $\log2$ at $n=2$. The ray-class sum at $n=2$ is $\lambda_{(2,0,1)}(2)+\lambda_{(2,1,1)}(2)=2\log2=2\Lambda(2)$,
  the equality case of clause (ii) above.
- *$p=5$.* $(5)$ is principal; $-5\equiv1\pmod3$ (since $-5+6=1$), so the generator $-5$ already lies in the
  required congruence class, putting $(5)$ in ray class $(1,0,1)$ — the **ray-identity class** — at $n=25$,
  weight $\log5$.
- *$p=103$.* Write $\sqrt{-103}=2\omega-1$, i.e. $\sqrt{-103}=-1+2\omega$ in the $(u,v)$ basis. Modulo $3$,
  $-1\equiv2$ and $2\equiv2$, so $\sqrt{-103}\equiv2+2\omega\equiv-(1+\omega)\pmod3$: a unit ($-1$) times the
  representative $1+\omega$. So $\mathfrak q=(\sqrt{-103})$ lands in ray class $(1,0,1+\omega)$ at $n=103$;
  the same computation for $\mathfrak q^2=(103)$ (generator $103\equiv1\pmod3$, since $103=34\cdot3+1$) lands
  in class $(1,0,1)$ at $n=103^2=10609$, **not** the class of $\mathfrak q$ itself — the squared ideal is a
  different, principal, unramified-looking object at a different norm, even though it comes from the same
  prime of $K$.

**Failure example: dropping the coprimality-to-$M$ condition. [Expository]** Suppose `idealsIn` were
redefined to drop "$I$ coprime to $M\mathcal O_K$," keeping only $I\neq0$, $NI=n$, $D.\mathrm{cls}(I)=g$ (with
$D.\mathrm{cls}$ still only *defined* and multiplicative on coprime ideals — the `RayData` structure's
`cls_mul`/`cls_eq` hypotheses are stated with explicit coprimality witnesses and give no information about
$D.\mathrm{cls}$ on ideals dividing $M\mathcal O_K$). At $M=3$, $K=\mathbb Q(\sqrt{-103})$, take $J=(3)$ itself
(prime, since $3$ is inert). The fibre lemma of §17.4.15 computes ray classes of ideals $I$ via a generator
$z\in J^{-1}\cdot(\text{inverse-class representative})$ with $z\equiv1\pmod{3\mathcal O}$; but every element
of $(3)$ is itself $\equiv0\pmod{3\mathcal O}$, so no such $z$ exists when the "class representative" is taken
to be $(3)$ — the set $X_J$ in the lemma is forced empty. Concretely, if one tried to assign $(3)$ some ray
class $g_0$ anyway and extend $a_{g_0}(9)$ by $+1$, the convolution identity of `aRay_mul_log` would fail at
$n=9$: the right side sums $\lambda_h(d)a_{g/h}(e)$ only over **coprime** ideals (since $\lambda_h$ is defined
through `idealsIn`, unchanged), so it would still compute $a_g(9)\log9$ using only the coprime-to-$3$ ideals of
norm $9$ — there are none, since $9=3^2$ and the only ideal of norm $9$ is $(3)$ itself, not coprime to the
modulus — giving $0$ on the right, while the left side would now read $1\cdot\log9\neq0$ after the
illegitimate inclusion. The identity breaks precisely because `lamIdeal`, the fibre lemma, and the
convolution all presuppose the same coprimality clause; dropping it on one side (membership) without the
others produces an immediate, checkable contradiction rather than a silently wrong density.

**Reading boundary.** Local R3 now additionally covers `lamRay_props` (`ExistsLFamRay.lean:135–170`, using
`sum_lamIdeal_le` from `SumLamIdealLe.lean:38–80`, `pow_prime_norm`, `exists_gen` and `normOne_span`),
`aRay_mul_log` (`FiniteIdealsIn.lean:82–134`, using `sum_lamIdeal` and `lamIdeal_pow` from the same file) and
`conv_real_char` (`ConvRealChar.lean:339–416`, using `conv_aRay`, `r_bounds`, `r_pow`, `geom_bounds` and
`conv_eq` from the same file). The deeper geometric inputs of §17.4.15 (the class-number lattice estimate, the
archive's plane-basis reduction, its integral-basis construction) remain named and unread, as do the
imported Mathlib factorization lemmas used at interface (`UniqueFactorizationMonoid.induction_on_prime`,
`WfDvdMonoid.max_power_factor`). [Archive source map](../sources/SOURCES.md#p13-ideal-weight-convolution-and-real-character-square)

### 17.4.25 Radial Haar measure and the Gamma factor in Minkowski volume

The weighted Minkowski body uses the sum of the real moduli and twice the complex moduli. Its volume computation uses the equality of open and closed unit ball volumes and recovers that volume from an exponential integral. The real dimension determines the radial power, and the choice of Haar measure fixes the unit ball constant. [Source and consumer map](../sources/SOURCES.md#chapter-17-radial-haar-measure-and-the-gamma-factor)

**Example A (a cubic exponential on a line).** Give $\mathbb R$ the norm $\rho(x)=2|x|$ and the measure $3\,dx$. For $r>0$, the radius-$r$ ball is $(-r/2,r/2)$, of measure $3r$. The radial density is $3\,dr$ on $(0,\infty)$. With $p=3$ and $b=8$ the original integral is $6\int_0^\infty e^{-64x^3}\,dx$. Put $t=64x^3$, so $dx=t^{-2/3}\,dt/12$. Then

$$
6\int_0^\infty e^{-64x^3}\,dx
=\frac12\Gamma(1/3)
=\frac32\Gamma(4/3)
=3\cdot8^{-1/3}\Gamma(1+1/3).
$$

Reflection gives the factor $2$, the norm scale divides the unit ball length by $2$, and the measure multiplier is $3$. On the ordinary Lebesgue half-line at $b=1$, the substitution $t=x^3$ gives $\Gamma(1/3)/3=\Gamma(4/3)$, the value used by the real Mathlib declaration.

**Example B (one complex coordinate).** Give $\mathbb C$ the modulus and Haar measure $du\,dv$ for $z=u+iv$. Its real dimension is $2$. Slicing its unit disk gives $2\int_{-1}^1\sqrt{1-u^2}\,du=\pi$ by the substitution $u=\sin\theta$. A disk of radius $r$ has area $\pi r^2$, with radial density $2\pi r\,dr$. At $p=1$ and $b=2$, set $t=2r$ to obtain

$$
\int_{\mathbb C}e^{-2|z|}\,du\,dv
=2\pi\int_0^\infty r e^{-2r}\,dr
=\frac{2\pi}{4}\Gamma(2)
=\pi\,2^{-2}\Gamma(3)
=\frac{\pi}{2}.
$$

Here $\Gamma(2)=1$ and $\Gamma(3)=2$. The weighted radius $s=2r$ has density $(\pi/2)s\,ds$, and $2|z|\le B$ has area $\pi B^2/4$ for $B\ge0$. For comparison, at $p=1/2$ and $b=2$ the substitution $t=2\sqrt r$ gives $r\,dr=t^3\,dt/8$. The same Haar measure then gives $(\pi/4)\Gamma(4)=3\pi/2$, equal to $\pi\,2^{-4}\Gamma(5)$ since $\Gamma(4)=6$ and $\Gamma(5)=24$.

**Definition (the radius measure).** Let $E$ be a finite-dimensional real normed space, with $\rho(x)=\|x\|$, $d=\dim_{\mathbb R}E$, and nonzero additive Haar measure $\mu$ on its Borel sets. Put $c=\mu\{\rho<1\}$. Haar measure is positive on nonempty open sets and finite on compact sets, and the closed unit ball is compact. Thus $0<c<\infty$. Define the pushforward $\nu=\rho_*\mu$ on $[0,\infty)$ by $\nu(A)=\mu(\rho^{-1}(A))$ for Borel $A$.

**Lemma (balls and spheres).** If $d>0$, for every center $a\in E$ and $r\ge0$ the open and closed balls both have measure $cr^d$, and the sphere has measure zero. At negative radii all three sets are empty. The measure $\nu$ has density $dc\,r^{d-1}$ on $(0,\infty)$ and zero mass at the origin.

*Proof.* For $r>0$, dilation by $r$ carries each unit ball to its radius-$r$ version. It multiplies Haar volume by $|\det(r\,\mathrm{id}_E)|=r^d$, by transporting the measure to a linear real coordinate chart, using Haar uniqueness there, and applying the Lebesgue change of variables. For $0<s<1$ the closed ball of radius $s$ lies in the open unit ball. Writing $C$ for the closed unit ball measure gives $s^d C\le c\le C$. Taking $s\uparrow1$ proves $c=C$. At radius zero the open ball is empty, and the singleton in the closed ball has measure at most $cr^d$ for every $r>0$, tending to zero because $d>0$. Translation invariance supplies all centers. The sphere is the difference of the closed and open balls, whose common volume is finite.

For $t\ge0$ we have $\nu([0,t])=ct^d$. The claimed density has the same cumulative measure by integration. The two measures restrict to finite measures on each $[0,m]$, with $m$ a positive integer, and agree on the intersection-stable generating family of intervals $[0,t]$ there. Uniqueness of finite measures gives equality on each $[0,m]$, and exhaustion gives equality on $[0,\infty)$. Hence for every nonnegative Borel $F$,

$$
\int_E F(\rho(x))\,d\mu(x)=dc\int_0^\infty F(r)r^{d-1}\,dr
$$

as an equality of nonnegative integrals. [Pinned ball and sphere proofs](../sources/SOURCES.md#chapter-17-radial-haar-measure-and-the-gamma-factor)

**Lemma (the exponential moment).** Under these assumptions, for every $p>0$ and $b>0$,

$$
\int_E e^{-b\rho(x)^p}\,d\mu(x)=c\,b^{-d/p}\Gamma(1+d/p).
$$

*Proof.* Write $e^{-b\rho(x)^p}=\int_0^\infty \mathbf 1_{\{b\rho(x)^p\le t\}}e^{-t}\,dt$. The integrand is measurable and nonnegative, and the measures are sigma finite since the balls of integral radius have finite measure and exhaust $E$. Tonelli and the closed ball volume now give $c\,b^{-d/p}\int_0^\infty e^{-t}t^{d/p}\,dt$. The inverse radius $(t/b)^{1/p}$ uses both positive parameters. Euler's integral is finite because $1+d/p>0$, proving integrability as well. Alternatively, substituting $t=br^p$ in the radial formula gives $r^{d-1}\,dr=b^{-d/p}t^{d/p-1}\,dt/p$. The resulting factor $(d/p)\Gamma(d/p)$ equals $\Gamma(1+d/p)$ by recurrence at $d/p>0$. [Euler's integral](https://dlmf.nist.gov/5.2.E1) · [Gamma recurrence](https://dlmf.nist.gov/5.5.E1)

**The mixed-coordinate volume.** For a number field $K$ of signature $(r_1,r_2)$ use all real places and one complex coordinate per conjugate pair. On $E=\mathbb R^{r_1}\times\mathbb C^{r_2}$ take the original product measure, with $du\,dv$ on each complex coordinate. Set $g(x,z)=\sum_i |x_i|+2\sum_j |z_j|$ and $S_B=\{g\le B\}$. This is a norm sublevel set in real dimension $n=r_1+2r_2=[K:\mathbb Q]>0$. The moment identity at $p=b=1$ gives $\int_E e^{-g}=n!\operatorname{vol}(S_1)$ by the boundary equality and $\Gamma(n+1)=n!$.

The pushforward by $g$ is the convolution of the coordinate radius measures, with an empty family contributing the unit mass at zero. Coordinate pushforward first gives the product of the radius measures, and the sum map gives their convolution. Its mass on bounded intervals is finite because every radius is nonnegative, so bounding the sum also bounds each radius. The real density for $|x|$ is $2\,ds$ and the complex density for $2|z|$ is $(\pi/2)s\,ds$. Tonelli factors the moment at $e^{-\sum s}$ into $2\Gamma(1)=2$ per real place and $(\pi/2)\Gamma(2)=\pi/2$ per complex place. Consequently for $B\ge0$,

$$
\operatorname{vol}(S_B)=\frac{2^{r_1}(\pi/2)^{r_2}}{n!}B^n.
$$

For $B<0$ the set is empty. For example, one real and one complex factor give $\int_0^B 2\cdot\pi(B-s)^2/4\,ds=\pi B^3/6$. The complex weight scales planar area by $2^{-2}$. The inherited $2^{-r_2}$ in the ideal covolume comes from converting conjugate rows to real coordinates. Both formulas use the same $du\,dv$. [Milne, Lemmas 4.22–4.23 and Proposition 4.26](https://www.jmilne.org/math/CourseNotes/ANT.pdf) · [Pinned mixed-body consumer](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/ConvexBody.lean#L377-L426)

**Notes on endpoints and formal scope.** In dimension zero, $E=\{0\}$ with $\mu=m\delta_0$ and $0<m<\infty$. At positive radii both balls have measure $m$. At radius zero the open ball is empty and the closed ball and sphere have measure $m$. The radius measure is $m\delta_0$ and the positive-$p$, positive-$b$ exponential has integral $m$, consistent with $\Gamma(1)=1$. In positive dimension, deleting $b>0$ permits $b=0$, giving integral $\mu(E)=\infty$ since $cr^d\to\infty$. If $b<0$ the integrand is at least $1$, with the same divergence. Deleting $p>0$ permits $p=0$, giving the constant $e^{-b}$ off the null singleton zero and again an infinite integral.

In the pin, `measure_le_eq_lt` puts the supplied gauge on a copy of the space as a norm, pushes Haar measure through the identity continuous linear equivalence between the two topologies, and pulls both balls back using `Measure.map_apply`. The equality theorem compares the two ball formulas. The sphere lemma takes their difference at positive radius and uses singleton nullity at zero. The real `integral_exp_neg_rpow` is on $(0,\infty)$ for $p>0$ and uses the weighted half-line integral at weight exponent zero. `Complex.integral_exp_neg_mul_rpow` assumes $1\le p$ and $0<b$. Its weighted supplier uses polar coordinates on the slit plane, the radial Jacobian and the angular length $2\pi$ before applying the real weighted formula. The recurrence gives $\Gamma(1+2/p)$. In `convexBodySum_volume` both coordinate calls use $p=1$, with $b=2$ in the complex call. The Haar proof above covers $0<p<1$ as in Example B. The scope of this reading is the integral supply to the previously established ordinary-class and ray-cardinality applications. [Declaration and evidence ledger](../sources/SOURCES.md#chapter-17-radial-haar-measure-and-the-gamma-factor)

### 17.4.26 Angular measure and the Haar product in polar coordinates

A radius measure tells us the volume of a shell. To integrate a function that varies over the shell, we also need the volume assigned to each set of directions. The unit ball supplies that information. A patch of the unit sphere is assigned a multiple of the volume of its cone inside the ball. Dilation then determines the mass of that patch in every shell. [Source and consumer map](../sources/SOURCES.md#chapter-17-angular-measure-and-the-haar-product)

**Example A (a nonradial integral on the plane).** Use Euclidean length and ordinary area on $\mathbb R^2$. An arc of angular length $\theta$ cuts out a unit sector of area $\theta/2$. Indeed, rotations divide the unit disk of area $\pi$ into equal sectors at rational fractions of a turn. The boundary rays have area zero, and squeezing the angle between rational fractions gives the formula for every angle. Twice the cone area gives the usual angle measure $d\theta$, by agreement of the two finite measures on a generating family of half-open arcs in a fixed angular parametrization. The circle has angular mass $2\pi$, and its first quadrant has mass $\pi/2$.

Take $F(x,y)=x\,\mathbf 1_D(x,y)$ for the open first-quadrant unit sector $D=\{x>0,\ y>0,\ x^2+y^2<1\}$. At the same radius it takes different values at different angles. The radial factor is $r\,dr$, and $F$ supplies another $r$.

$$
\int F(x,y)\,dx\,dy
=\int_0^1 r^2\,dr\int_0^{\pi/2}\cos\theta\,d\theta
=\frac13.
$$

Cartesian slices give $\int_0^1 x\sqrt{1-x^2}\,dx=1/3$, using $t=1-x^2$. With the indicator of $D$ alone the product gives $(\pi/2)(1/2)=\pi/4$. Over all angles the same radial integral gives $\pi$.

**Example B (two three-dimensional sectors in different shells).** Use $\|(x,y,z)\|_\infty=\max(|x|,|y|,|z|)$ and ordinary volume. The unit cube has volume $8$. On its boundary choose the disjoint face patches

$$
A=\{(u,v,1): 0<u<1,\ -1<v<1/2\},\qquad
B=\{(-1,u,v): -1/2<u<1/2,\ 0<v<1/2\}.
$$

At radius $r$ the first cone has the slice $z=r$, with $0<x<r$ and $-r<y<r/2$. Its Cartesian slice area is $3r^2/2$. The second cone has the slice $x=-r$, with $-r/2<y<r/2$ and $0<z<r/2$. Its slice area is $r^2/2$, and $|dx|=dr$. Integrating those areas from zero to one gives unit cone volumes $1/2$ and $1/6$. Multiplying by the dimension $3$ gives angular masses $3/2$ and $1/2$. For the first patch in $1<r<2$ and the second in $0<r<3$ the volumes are

$$
\frac32\frac{2^3-1^3}{3}=\frac72,\qquad
\frac12\frac{3^3}{3}=\frac92.
$$

Their disjoint union has volume $8$, in agreement with integrating the Cartesian slice areas over those intervals. Each full open face has angular mass $4$, by the same slice calculation with both transverse intervals equal to $(-r,r)$. The cones over the edges lie in the planes $x_i=\pm x_j$ for distinct coordinates and have volume zero. Thus the angular mass is $24$, giving cube volume $24\int_0^R r^2\,dr=8R^3$ for every $R>0$. This calculation uses the radial factor on a sphere with corners.

**Definition (direction, radius and angular measure).** Let $E$ have finite real dimension $d>0$, with a norm, its Borel sets, and nonzero additive Haar measure $\mu$. Write $E^\times=E\setminus\{0\}$, $S=\{u:\|u\|=1\}$, and $P=(0,\infty)$. Set

$$
\Phi(x)=(\|x\|^{-1}x,\|x\|),\qquad
\Psi(u,r)=ru.
$$

Write $\mu^\times$ for the restriction of $\mu$ viewed as a measure on $E^\times$. For Borel $A\subseteq S$ write $C_t(A)=\{ru:u\in A,\ 0<r<t\}$ and set

$$
\sigma(A)=d\,\mu(C_1(A)),\qquad \eta_d(dr)=r^{d-1}\,dr\quad(r>0).
$$

With $c=\mu\{\|x\|<1\}$, the angular mass is $dc$. The probability version $\sigma/(dc)$ describes the direction of a point chosen uniformly by volume in the unit ball.

**Lemma (the angular and radial product).** [Lean, read] The maps $\Phi$ and $\Psi$ are inverse Borel isomorphisms, and $\Phi_*\mu^\times=\sigma\otimes\eta_d$. Consequently, for any nonnegative Borel $F$ on $E$,

$$
\int_E F(x)\,d\mu(x)
=\int_S\int_0^\infty F(ru)\,r^{d-1}\,dr\,d\sigma(u)
$$

in the extended nonnegative reals. For real or complex $F$ in $L^1(\mu)$ it holds as an ordinary integral, and the two orders of integration agree.

*Proof.* The norm of $\|x\|^{-1}x$ is one and $\|ru\|=r$ for $r>0$. These identities give the inverses. The two maps are continuous on their displayed domains, since inversion of the radius is continuous on $P$. The subspace Borel structures agree with the subtype measurable structures. The Borel sets of the product agree with the product sigma algebra since both factors are second countable. Thus $C_t(A)=\Phi^{-1}(A\times(0,t))$ is Borel. Restrict $\Phi_*\mu^\times$ to $S\times(0,1)$ and project to $S$. Multiplying this finite measure by $d$ gives $\sigma$. Its total mass is $dc$ by the nullity of the origin and finiteness of the unit ball volume from §17.4.25.

For each Borel $A$ and $t>0$, $C_t(A)=tC_1(A)$, so the Haar dilation law gives

$$
(\Phi_*\mu^\times)(A\times(0,t))
=t^d\mu(C_1(A))
=\sigma(A)\frac{t^d}{d}
=(\sigma\otimes\eta_d)(A\times(0,t)).
$$

This is scaling the *image* of the unit cone. The pushforward of Haar measure on $E$ by $x\mapsto tx$ has factor $t^{-d}$, since evaluating it on a fixed set takes the inverse image. The division by $d$ comes from integrating $r^{d-1}$ on $(0,t)$.

The tested rectangles form a pi-system. Intervals $(0,t)$ generate the Borel sets of $P$, and the angular side ranges over all Borel sets. The rectangles generate the product sigma algebra, since $A\times P$ is the increasing union of $A\times(0,m)$. On each strip $S\times(0,m)$ the two measures are finite and agree on the intersected rectangles, including the entire strip. Finite-measure uniqueness on each strip and increasing exhaustion prove the product identity. Evaluating it on $A\times(0,1)$ also proves uniqueness of $\sigma$ with this radial factor. Pushforward integration transports indicators, then nonnegative functions by monotone convergence. The null singleton permits integration over $E$. Tonelli gives the iterated integral. Applying the same identity to $|F|$ gives absolute integrability on the product when $F\in L^1(\mu)$, and Fubini gives both ordinary iterated integrals. [Pinned product proof](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean#L139-L158)

**How the marginal enters Minkowski volume.** In the pin, `toSphere` uses the comap along the inverse polar map followed by the inclusion of the punctured subtype into $E$. On Borel sets this gives the same measure as pushing $\mu^\times$ forward by $\Phi$. The definition then restricts to the unit strip and takes the first marginal. `volumeIoiPow n` is Lebesgue measure on the positive-ray subtype with density $r^n$. The product theorem uses $n=d-1$. Its proof uses positive dimension to simplify $(d-1)+1=d$ in the interval mass. The proof compares the measures on rectangles via `prod_eq_generateFrom`, using the finite sphere factor and the spanning intervals $(0,k+1)$. [Pinned construction and proof](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean#L48-L158)

For a radial test $F(x)=h(\|x\|)$ the function on the product depends only on the second projection. `integral_fun_norm_addHaar` first replaces the ambient integral by the subtype integral using the null singleton. It transports the integral along the measure-preserving homeomorphism, applies `integral_fun_snd` to extract the sphere mass, and moves the density into the positive-ray integral. In real notation the result is $dc\int_0^\infty h(r)r^{d-1}\,dr$. The companion `integrable_fun_norm_addHaar` uses the sphere's finite, strictly positive mass to give the integrability equivalence with the weighted radial function. Mathlib states its radial equality with the totalized Bochner integral. The ordinary signed and complex formulas above require actual integrability. [Pinned marginal](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean#L250-L314)

`measure_unitBall_eq_integral_div_gamma` calls this marginal in the nontrivial branch with $h(r)=\exp(-r^p)$ and $p>0$. Its subsingleton branch integrates over the singleton. The gauge wrapper `measure_lt_one_eq_integral_div_gamma` transfers the existing weighted sum gauge and Haar measure to a normed copy, and `convexBodySum_volume` calls the wrapper with $p=1$. The real half-line and complex coordinate Gamma calls in the same mixed-volume proof have their own paths. The complex call uses the slit-plane chart from §17.4.25. The sphere product supplies the generic ball-to-integral step, before the coordinate integrals evaluate the mixed exponential moment. [Generic ball consumer](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean#L50-L111) · [Mixed-body consumer](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/ConvexBody.lean#L377-L426)

**Notes.**

- In dimension one write $\|x\|=a|x|$ and $\mu=k\,dx$, with $a,k>0$. The sphere is $\{-1/a,1/a\}$. Each unit cone has length $1/a$, so each atom has mass $k/a$. The radial factor is $dr$. The product formula reads $(k/a)\int_0^\infty (F(r/a)+F(-r/a))\,dr$, exactly the two half-line substitutions. In dimension zero the coordinate homeomorphism still identifies two empty spaces. The punctured measure and the product are zero, but the original measure is $m\delta_0$ with $m>0$. The constant function $1$ is integrable and has integral $m$, whereas its punctured integral is zero. Positive dimension lets us discard the origin from the full-space integral and divide by $d$. The pinned measure-preservation statement handles the trivial case through the empty spaces, with natural subtraction truncated at zero.
- Without Haar homogeneity, the same radial marginal can hide different angular behavior. On the real line with the ordinary norm, give $dx$ density $1+\tfrac12\operatorname{sgn}(x)\mathbf 1_{\{1<|x|<2\}}$. The densities at $r$ and $-r$ sum to $2$ for all $r>0$. The unit cones have mass one each. The positive half of the shell $1<|x|<2$ has actual mass $3/2$, while the product of the unit-cone angular measure and the radial factor assigns it mass one.
- Angular measure depends on the norm and the Haar normalization. In the norm $\max(|x|/2,|y|)$ the unit rectangle has vertical sides of length two and horizontal sides of length four. Each full side cuts out a triangle of area two, so all four sides have angular mass four. Euclidean boundary length gives different proportions even after normalization to a probability. The radial factor here comes from homogeneous dilation. The general nonlinear Jacobian theorem and the compact-dual density of Chapter 9 have their own hypotheses and sources.
- Naor and Romik give the integrable formula and its product-measure form for Lebesgue volume with the Minkowski functional of a convex body. For the closed unit ball of a norm, their normalized cone measure is $\sigma/(dc)$. Linear coordinates and the Haar normalization give the version above. Folland gives the Euclidean special case with the factors in the opposite order. [Naor–Romik, p. 244, Proposition 1 and Note 1](https://www.numdam.org/article/AIHPB_2003__39_2_241_0.pdf#page=4) · [Folland, Theorem 2.49](https://buchholzmd.github.io/paying-in-attention/Assets/Folland---Real-Analysis--Modern-Techniques-and-Their-Applications.pdf)

## 17.5 Remarks, formalization notes, and Masullo's counterpart

### 17.5.1 Mathlib's `C = 4` for 3-APs versus the archive's `C_T = 64` for `NoRel`

It is instructive to compare Mathlib's standalone Behrend theorem `[Behrend1946]` with the archive's
generalization (`ThickExists.lean` and `ThickFrame2Large.lean`) [Lean, read]:

- In `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean`, Mathlib defines `rothNumberNat N` (the
  maximum size of a $3$-AP-free subset of $\{0, \dots, N-1\}$), encodes $\mathrm{sphere}(n, d, k)$ in
  base **$2d - 1$** (`threeAPFree_image_sphere`, `:186`, since $x + z = 2y$ only has coefficients
  $1, -2, 1$ with $\lvert x_m + z_m - 2 y_m \rvert < 2d - 1$!), and proves `Behrend.roth_lower_bound`
  (`:481`): $N \exp(-4\sqrt{\log N}) \le \mathrm{rothNumberNat}(N)$ for all $N \in \mathbb N$!
- The archive does **not** use `roth_lower_bound` or `threeAPFree_image_sphere`, because `HostThickOrbit`
  needs to rule out **all** relations $j(s_2 - s_1) = i(s_3 - s_1)$ up to window width $L_w \asymp \log x$
  and keep $4 L_w s < n_0$ for modular wrap-around! Instead, `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:302` imports **only**
  the clean pigeonhole sphere lemma `Behrend.exists_large_sphere S d` (`Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:245`), widens the
  radix from $2d - 1$ to **$B = 4 L_w d$**, proves general sphere relation-freeness `sphere_rel` in
  37 lines of `ring` / `linear_combination` (`:36–72`), gets $C = 32$, and doubles $32 \to 64$ when
  erasing $0$ and balancing $\sqrt{\log n_0 \cdot \log L_w}$ against $x^\varepsilon$!

### 17.5.2 Masullo's counterpart

Masullo's *The Music of the Primes* has **no counterpart** to Behrend spheres, progression-free sets
in finite Galois groups, or a three-way top/thick/thin partition of CM places [Expository]:

- **Where Masullo avoids orbit collisions (`Theorem 7.1.3.2`, p. 324, and `Appendix A.4`, pp. 562–565):**
  In Masullo's $\mathrm{GL}_1(\mathbb A_F)/F^\times$ framework, there is no auxiliary host tower;
  periodic Euler-pole orbits $\frac{2\pi i}{\log N(\mathfrak p)}\mathbb Z$ along $\mathbb R_{>0}$ avoid
  infinite collisions across distinct rational primes $p_1 \neq p_2$ by the **$\mathbb Q$-linear
  independence of $\{\log p\}$** (unique prime factorization in $\mathbb Z$, `p. 324`), while lattice
  point counting in $\mathbb R^d$ enters only in Appendix A's classical proof of Dirichlet's $S$-unit
  theorem (`pp. 562–565`) [Paper; Masullo pp. 324, 562–565].
- **Where Alpöge needs Behrend's sphere:** Because Alpöge's Frobenius elements act inside a **finite
  abelian $2$-group** $A_0 \cong \mathbb Z/n_0\mathbb Z$ (where every element has finite order dividing
  $2^e$ and logarithms of primes play no role!), preventing multi-hit collisions along length-$L_w$
  orbit windows requires genuine **additive combinatorics in $\mathbb Z$** lifted via strict Euclidean
  convexity of spheres in $\mathbb Z^S$!

---

## 17.6 Lean counterpart for this chapter

| Declaration | File:line | Mathematical content / role in Sections 17.3–17.4 | Tag |
|---|---|---|---|
| `Behrend.box`, `Behrend.sphere`, `Behrend.map`, `threeAPFree_image_sphere`, `exists_large_sphere_aux`, `Behrend.exists_large_sphere`, `Behrend.roth_lower_bound` | `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:97,110,133,186,237,245,481` | Definition 17.1 & Theorem 17.2(3): Mathlib's discrete box $\{0,\dots,d-1\}^S$, sphere $\sum v_m^2 = k$, base-$B$ homomorphism, and pigeonhole existence of a sphere of size $\ge d^S / (S d^2)$. | [Lean, read] |
| `Bl.general_b_fact_second_last.goal1` | `src/Lemmata/GeneralBFactSecondLast/Imports.lean:5` | Lemma 17.1(1): carry-free signed base-$B$ uniqueness ($\lvert c_m \rvert < B,\ \sum c_m B^m = 0 \implies c_m = 0$; archive import cone 0). | [Lean, read] |
| `NoRel`, `InTranslate`, `HostThickOrbit`, `HostThickExists`, `HostTops`, `HostOrdinary`, `HostConductor`, `HostEta` | `src/Formalism/FrobeniusOrbits/HostThickExists.lean:13,18,22,30,40,61,82,92` | Definition 17.2(1–3): bounded-ratio relation-freeness $j(s_2-s_1) \neq i(s_3-s_1)$, $\le 2$ orbit-window hit contract, and subexponential `NoRel` existence (cone 5). | [Lean, read] |
| `coeff_zero`, `map_lt`, `sphere_rel`, `cast_map`, `noRel_image`, `card_image`, `hostThickExists` | `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:11,15,36,74,85,146,181` | Lemma 17.1(2) & Theorem 17.2: proves strict sphere convexity `sphere_rel`, base-$4Ld$ `noRel_image`, and `HostThickExists` with explicit constant $C = 32$ (cone 7). | [Lean, read] |
| `bound_aux`, `int_mul_lt_of_le_four_mul`, `ThickOrbit.key`, `part_one`, `part_two`, `hostThickOrbit` | `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickOrbit.lean:9,15,21,71,96,132` | Proposition 17.3(1): proves $\le 2$ hits per length-$L$ window when $\operatorname{ord}(h) > 4L$ and $\le 1$ hit on the entire coset when $\operatorname{ord}(h) \le 4L$ (cone 6). | [Lean, read] |
| `Frame`, `Frame.A`, `a0`, `n0`, `o`, `dig`, `GG`, `Psi`, `placeOf`, `tau1`, `tau2`, `natCard_GG`; `Frame.thick_key`, `Frame.hostThickOrbit` | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:15,29,61,68,70,72,89,112,118,120,122,137`; `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean:714,821` | Definition 17.2(4) & Proposition 17.3(1): host abelian frame `Frame`, cyclic subgroup `A0 = ⟨a0⟩` of order `n0`, two CM sheets `tau1`/`tau2`, and lift of `hostThickOrbit` to `Frame.A` (cones 3 and 32). | [Lean, read] |
| `Ranks`; `PrimeClass`, `Host`, `topPlaces`, `thickPlaces`, `IsThin`, `secondSet_card_lower_bound`, `FactTopsThick` | `src/Formalism/LocalRingCardinality/Params.lean:6`; `src/Formalism/LocalRingCardinality/DataHost.lean:24,39,129,133,136,165,193` | Definition 17.3(1–2): chain rank tuple `Ranks` and concrete `Host R` partitioning `R.Psi` into `topPlaces`, `thickPlaces` (built from `T2`), and `IsThin` (cones 5 and 33). | [Lean, read] |
| `hE`, `KE`, `dE`; `thickFrame2_card`, `thickFrame2_large`, `thickFrame2`; `topsChoiceH` | `src/Development/AutomorphicArithmetic/ThickFrames/MarkedLow.lean:23,25,29`; `src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean:7,18,29`; `src/Development/AutomorphicArithmetic/ThickFrames/topsChoiceH.lean:30` | Theorem 17.4(1–2): weighted AM–GM with $\delta = \varepsilon/(3C)$ yielding $C_T = 64$, $x^{-\varepsilon}\,\varphi.\mathrm{ord} \le \lvert T_2 \rvert$, $4 L_w \lvert T_2 \rvert \le n_0$, and Bernoulli top-place selection (cones 5, 41, 385). | [Lean, read] |
| `ThinOK`, `thinScales_iff_hostBound`, `HostGood`, `HostExW`; `FieldRows`, `Choices`, `HostNF`, `exists_host`; `hof_Lwv_le`, `hof_thick`, `hostOfFieldOf`; `hostOfField`, `supplyOfAdm` | `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:61,65,101,120`; `src/Development/AutomorphicArithmetic/CoprimeRanks/SecondSetNoRelation.lean:13,23,55,100`; `src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:58,71,159`; `src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8,17` | Definition 17.3(3) & Theorem 17.4(2): assembles `T2`, `TT`, `ccK`, and `levelPrimes` into a scale-admissible `Host R` (`HostGood`) feeding `supplyChi` (`HostOfField` cone 1,314; `shortNorm`/`topsBase` `R2` `[Lean]`). | [Lean, read] |
| `PrimesRel`, `primesRel_holds`, `primesInProgressions_relativeError` | `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ZerosDisc.lean:35`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimesInProgressionsRelativeError.lean:22`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimesInProgressionsRelativeErrorStatement.lean:8` | Relative prime count and assembly from quantitative inputs. | [Lean, read] |
| `primesAPInterval_of_primesRel`, `shortIntervalLowerBound`, `shortIntervalImpliesProgressions_statement` | `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimesAPIntervalOfPrimesRel.lean:12`; `src/Formalism/GL3MeanSquares/HookFormulaTorsion/GlobalBoundRefinements.lean:222,366` | Relative error yields an interval count at polynomial scales. | [Lean, read] |
| `SmallOne`, `smallOne_of`, `smallOne`, `exists_three_primes_one_mod_le_rpow`, `mod_small`, `levelData` | `src/Development/AutomorphicArithmetic/ShortNorms/ShortNorm.lean:13`; `src/Development/AutomorphicArithmetic/ShortNorms/SmallOneOf.lean:8`; `src/Development/AutomorphicArithmetic/ShortNorms/Primes.lean:7`; `src/Development/AutomorphicArithmetic/ShortNorms/ExistsThreePrimesOneModLeRpow.lean:10`; `src/Development/AutomorphicArithmetic/ShortNorms/levelData.lean:10,36` | One witness becomes three, with a common scale bound. | [Lean, read] |
| `split_of_one_mod` | `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NcardPrimesOverOfStabilizer.lean:73` | Congruence pays the splitting clauses in the host. | [Lean, read] |
| `exceptionalDirichletZero_unique_zeroFreeRegion`, `chebyshevPsiProgression_relative_error`, `primeCount_relative_error_of_psi_relative_error` | `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExceptionalDirichletZeroUniqueZeroFreeRegionStatement.lean:8`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChebyshevPsiProgressionRelativeErrorStatement.lean:8`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeErrorStatement.lean:8` | Analytic inputs to `PrimesRel`. | [Lean], deeper proofs [Open] |
| **psi_exceptional**, **contour**, **exists_line**, **shift** | src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyPsiWithExceptionalZero.lean:14,160,181,438 | §17.4.11, ray-class Perron contour and uniform endpoints | [Lean, read], local R3 |
| **LogDerivZeros.main**, `exists_factor`, `norm_logDeriv_le`, `norm_le_of_sphere`, `norm_one_sub_conj_mul`; `exists_factor_order`; **HkLocal.logDeriv_local**, `analyticOrderNatAt_comp_affine` | src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormOneSubConjMul.lean:19,49,108,117,125; src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsFactorOrder.lean:7; src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionLogDerivLocalFormula.lean:11,21 | §17.4.12, unit-disk zero count and Borel–Carathéodory remainder with $C(r,R)=1/c_1+A(1+c_2/c_1)$, then the affine specialization $r=5/7$, $R=6/7$, $\rho=7/10$ giving `rayClassLFunction_logDeriv_local_formula` with $C=12C_0$ | [Lean, read], local R3; continuation in §17.4.13 and Euler supply in §17.4.14 |
| **RayCont.continuation_growth** and **rayClassLFunctionFamily_continuation_growth** | src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean:206–249 and src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowthStatement.lean:8–9 | §17.4.13, class-count Mellin continuation and closed disk growth | [Lean, read], local R3 |
| **Hk.LogDeriv.logDeriv_F** and **rayClassFamily_logDeriv_re_gt_one** | src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOne.lean:13–294; src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOneStatement.lean:8–9; src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TsumOneDivRpowLe.lean:6–60 | §17.4.14, half-plane lower bound and weighted series, with the center and log budget in the local consumer | [Lean, read], local R3 |
| **`card_ray_le`**, **`rayCountTheta`**, **`aRay_eq_ncard_qForm`** | `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLFamRay.lean:50–63,97–123`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayCountThetaFibreCount.lean:11–121`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassIdealCountEqNcardShiftedBinaryForm.lean:183–343` | [Lean, read] Fixed modulus, size, norm fibres and theta estimates for the concrete family. |
| **`lamRay_props`**, **`aRay_mul_log`**, **`conv_real_char`** | `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLFamRay.lean:135–170`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean:38–80`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteIdealsIn.lean:82–134`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean:339–416` | §17.4.16, ideal-weight support and the $2\Lambda$ bound, the divisor convolution identity, and the real-character square | [Lean, read], local R3 |
| `log_conductor_mul_height_le_of_pageN` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/LogConductorMulHeightLeOfPageN.lean:6` | Theorem 17.4(3): proves $\log(N \cdot t) \le 2 x^{\varepsilon/4}$ from $N \le 2^{e+2} m q d$, `PageN eps x e`, $t \le x^{C_t}$, and $\log(qd) \le x^{\varepsilon/4}$ (cone 21, called in `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean:49`). | [Lean, read] |
| `no_three`, `no_three_consecutive_thick_places`; `LongWindow.main`; `thick_density_le`; `FinalE.trivStab` | `src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/NoThreeConsecutiveThickPlaces.lean:28,222`; `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/AtMostTwoThickInWindowLongOrbit.lean:27`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickSetDensityLeInvFourLw.lean:7`; `src/Formalism/BehrendSets/FinalE.lean:12` | Proposition 17.3(2) & Section 17.1.2: downstream $\le 2$-hit window and $\le 1/(4L_w)$ density consumers of `Host.T2`, contrasted with the misfiled torsion-freeness export `BehrendSets.FinalE.trivStab` (cones 333, 480, 191, 12). | [Lean, read] |

**Summary of the chapter.** To prevent local Frobenius orbits along the unitary chain from clustering
while keeping coset-averaging losses subexponential, every CM host `H : Host R` (`src/Formalism/LocalRingCardinality/DataHost.lean:39`)
equips its $-1$ CM sheet $\tau_2(R.A)$ with a translated subset `thickPlaces` built from a finite set
$T_2 \subset \mathbb N$ satisfying `NoRel T2 Lw` ($j(s_2 - s_1) \neq i(s_3 - s_1)$ for
$0 < \lvert i \rvert, \lvert j \rvert \le L_w, i \neq j$) and $4 L_w s < n_0$ [Lean, read]. In
`ThickExists.lean` (Theorem 17.2), the archive imports Mathlib's pigeonhole sphere lemma
`Behrend.exists_large_sphere` `[Behrend1946]`, proves by strict Euclidean convexity (`sphere_rel`)
and signed carry-free base-$4 L_w d$ uniqueness (`src/Lemmata/GeneralBFactSecondLast/Imports.lean:5`, Lemma 17.1) that sphere encodings
satisfy `NoRel`, and achieves cardinality $\ge \frac{n_0}{L_w}\exp(-32\sqrt{\log n_0 \cdot \log L_w})$.
`ThickOrbit.lean` and `FrameFacts.lean` (Proposition 17.3) turn `NoRel` and $4 L_w s < n_0$ into the
hard cap of **at most $2$ thick places** in any length-$L_w$ long-orbit window (and **at most $1$**
in any short-orbit coset), while `ThickFrame2Large.lean` and `hostOfFieldOf.lean` (Theorem 17.4) apply
weighted AM–GM ($\delta = \varepsilon/96 \implies C_T = 64$) to guarantee $\lvert T_2 \rvert \ge x^{-\varepsilon}\,\varphi.\mathrm{ord}$
at $L_w = \mathrm{Lwv}(s) \asymp \log x$ and assemble `HostOfField` on the main spine of `src/Main.lean`!
