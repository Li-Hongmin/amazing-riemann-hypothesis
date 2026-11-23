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
> imported Bernoulli-sampling and norm-one sub-lemmas (`topsBase`, `shortNorm`, `smallOne`, `R2`);
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
by `letter_snd`, using `placeOf_snd`, `:16,20`), while `no_three` (`src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/NoThreeConsecutiveThickPlaces.lean:28–115`) handles
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
   norm-one witnesses from `ShortNorm`, and level primes `smallOne` constructs a complete `Host R`
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
`hostOfFieldOf` (`:159–254`) assembles five distinct level primes
$g_0,g_1,p_{\mathrm{de}},p'_{\mathrm{de}},q_0$ (`:104,194`).
Writing $M=Q_Sqd$, the two distinguished primes satisfy $1$ modulo $\operatorname{lcm}(15,M)$
(`:200–203`), and $g_0,g_1,q_0$ satisfy $1$ modulo $M$ (`:208,215`).
The ideal $\mathfrak c_K$ is the unit ideal (`:104,109`). The witnesses from `ShortNorm`
are bounded-height norm-one elements for $g_0,g_1$ (`:167,209`). The proof takes
$T_2$ from `hof_thick` and the top set from `topsChoiceH`, then verifies `HostGood`
(`:225–254`). Specializing in `src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8,17`
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

---

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
| `ThinOK`, `thinScales_iff_hostBound`, `HostGood`, `HostExW`; `FieldRows`, `Choices`, `HostNF`, `exists_host`; `hof_Lwv_le`, `hof_thick`, `hostOfFieldOf`; `hostOfField`, `supplyOfAdm` | `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:61,65,101,120`; `src/Development/AutomorphicArithmetic/CoprimeRanks/SecondSetNoRelation.lean:13,23,55,100`; `src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:58,71,159`; `src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8,17` | Definition 17.3(3) & Theorem 17.4(2): assembles `T2`, `TT`, `ccK`, and `levelPrimes` into a scale-admissible `Host R` (`HostGood`) feeding `supplyChi` (`HostOfField` cone 1,314; `shortNorm`/`smallOne`/`topsBase` `R2` `[Lean]`). | [Lean, read] |
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
