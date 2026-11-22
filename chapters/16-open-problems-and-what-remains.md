# Chapter 16. Open problems and what remains to be checked

> **Status tags used in this chapter:** `[Lean, read]` for archive statements, static-audit facts, and
> proofs verified line by line by us (`R3`); `[Lean]` for compiled archive declarations inspected at
> statement level (`R1`/`R2`); `[Paper; remark p. …]` and `[Paper; Masullo p. …]` for primary
> documents; `[Community]` for public machine-check logs, repository audits, and community reports
> checked online through `2026-11-22 03:30 UTC`; `[Expository]` for classical number-theoretic proofs
> and worked examples on scope boundaries; `[Open]` for pending kernel replays, unaudited statement
> matches, unread deep proof cones, and unresolved gaps in Masullo's draft.

We have reached the closing chapter of *Amazing Riemann Hypothesis*. Across Chapters 1 through 15, our
governing rule (`README.md`) has been to keep four questions strictly separate whenever someone asks
*"Has the Riemann Hypothesis been proved?"*:

1. **Kernel soundness (`[Community]` / `[Open]`):** Does the exported 61.57 GB proof term of Alpöge's
   `src/Main.lean` follow from Lean's three standard logical axioms (`propext`, `Classical.choice`,
   `Quot.sound`) according to multiple independent proof kernels, generated from unmodified source in a
   network-isolated sandbox?
2. **Statement fidelity (`[Lean, read]` / `[Community]` / `[Open]`):** Do the five headline theorems in
   `src/Main.lean` (`:4, 6, 8, 10, 12`) say **literally** what mathematicians mean by RH and Dirichlet
   GRH — and, separately, do the 257 internal `*_of_literature` / `*_of_open` theorems in
   `UpperTheory.LiteratureTheorems.*` match the classical theorems after which they are named?
3. **Human mathematical understanding (`[Lean, read]` vs `[Open]`):** Which parts of the 175,187-file
   archive have human mathematicians actually read, understood, and extracted into clean mathematical
   arguments — and which deep import cones remain opaque formal proof terms?
4. **Status of Masullo's route and mathematical consequences beyond Dirichlet GRH (`[Open]`):** Which
   gaps in *The Music of the Primes* remain open, and **which famous conditional theorems in number
   theory would become unconditional if `EveryCharacter` stands — versus which ones DO NOT follow from
   Dirichlet GRH at all**?

This chapter answers all four questions in consolidated, citation-pinned ledgers as of
`2026-11-22 03:30 UTC`, preceded by two concrete worked examples — one in algebraic number theory and
one in Lean build mechanics — that clear up the two most widespread misconceptions in public discussion
of the announcements, and followed by an actionable checklist for readers who want to contribute to the
next stage of verification and digestion.

---

## 16.1 Motivation: why kernel acceptance ends one stage and starts two others

As the official joint statement of the Lean and Mathlib communities (`2026-11-21 13:55 UTC`) and Martin
Bridson's statement for the Clay Mathematics Institute emphasized (`CONTRIBUTIONS.md`, `[Community]`),
a machine-checked proof of a 167-year-old problem changes the nature of peer review rather than
abolishing it [Expository]:

- **What independent proof kernels settle:** Once the five target statements in `src/Statements.lean`
  and Mathlib's `RiemannHypothesis` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`) have been
  audited line by line against their textbook definitions (Chapter 1, `[Lean, read]`), and once
  multiple independently implemented kernels (`leanchecker`, `nanoda`, `con-leche --compare`,
  `con-ron --compare`, `lean4lean`) accept a sandbox-reproduced export depending only on the three
  standard axioms, **the risk of a subtle hidden gap, unstated assumption, sign slip, or missing boundary
  case in proving `Main.lean` drops essentially to zero** (modulo simultaneous soundness bugs across
  independent kernels in Lean, Rust, and C++, or a definition bug in Mathlib's eight `LSeries` files).
- **What kernels do NOT supply on their own:**
  1. A kernel checks that `UpperTheory.FinalTheorems.everyCharacter` has type `EveryCharacter`, **not**
     whether an internal helper `Prop` named `GlobalTheory.Published.GlobalArtinReciprocity` or
     `KawamataViehwegVanishing` is the textbook theorem or a specialized avatar (so nobody should reuse
     an unaudited internal module as a black-box library theorem without reading its `def`! Chapter 13).
  2. A kernel gives zero mathematical insight into **why** the proof works or how to simplify 17.37
     million lines into a human-checkable monograph and reusable Mathlib theorems.
  3. Above all, a kernel proves **only the exact `Prop`s in `Main.lean`** — namely `EveryCharacter`
     (Dirichlet $L$-functions over $\mathbb Q$). In the press and on social media, dozens of commentators
     have conflated "GRH for Dirichlet $L$-functions" with the **Extended Riemann Hypothesis (ERH)** for
     Dedekind zeta functions $\zeta_K(s)$ of **arbitrary** number fields $K$ and Artin $L$-functions
     `[Artin1924]`! Let us see by an explicit hand calculation why that conflation is mathematically
     false.

---

## 16.2 Worked examples of scope boundaries and verification subtleties

### 16.2.1 Non-abelian Dedekind and Artin $L$-functions: $K = \mathbb Q(\sqrt[3]{2})$, $S_3$, and negative Brauer exponents

In `Main.lean:8`, `EveryCharacter` rules out zeros of Dirichlet $L$-functions over $\mathbb Q$ to the right of the critical line, with the stated exception at the pole. To see its scope for a number field $K$, start with the Dedekind series $\zeta_K(s)=\sum_{0\ne\mathfrak a\subseteq\mathcal O_K}(N\mathfrak a)^{-s}$ for $\Re(s)>1$. The sum runs over nonzero integral ideals and uses their absolute norms. `[Artin1924]` `[Brauer1947]` [Expository].

**Step 1. Abelian extensions.** Suppose $K/\mathbb Q$ is Galois with finite abelian group $G$. Examples include $\mathbb Q(\zeta_8)$ and $\mathbb Q(\sqrt{5})$. By the Kronecker–Weber theorem there is an integer $N\ge1$ such that $K\subseteq\mathbb Q(\zeta_N)$. Each character of $G$ lifts through the quotient map from $(\mathbb Z/N\mathbb Z)^\times$ to $G$ and determines a primitive Dirichlet character $\chi^\ast$ of conductor dividing $N$. Artin factorisation gives

$$
\zeta_K(s)=\prod_{\chi\in\widehat{G}}L(s,\chi^\ast).
$$

The Dirichlet statement `EveryCharacter` therefore gives RH for the Dedekind zeta function of each such field.

**Step 2. Cubic splitting.** The cubic field $K=\mathbb Q(\sqrt[3]{2})$ is not Galois over $\mathbb Q$. Its Galois closure $L=\mathbb Q(\zeta_3,\sqrt[3]{2})$ has group $S_3$. The subgroup fixing $K$ has order two, and the quadratic resolvent is $F=\mathbb Q(\zeta_3)=\mathbb Q(\sqrt{-3})$.

The permutation character of $S_3$ on the roots of $X^3-2$ splits into the trivial character and the irreducible character $\rho_2$ of degree two. The trace of $\rho_2$ is the number of fixed roots minus one. It takes the values $2,0,-1$ on the identity, the transpositions and the three-cycles respectively. With $\chi_{-3}$ the quadratic character of $F$, Artin factorisation gives `[Artin1924]`

$$
\zeta_K(s)=\zeta(s)L(s,\rho_2),
\qquad
\zeta_L(s)=\zeta(s)L(s,\chi_{-3})L(s,\rho_2)^2.
$$

The Euler factors at unramified primes $p\nmid6$ follow from the factorisation of the cubic modulo $p$.

- If $p\equiv2\pmod3$, cubing permutes the nonzero elements of the residue field. The polynomial has one linear factor and an irreducible quadratic factor, as at $p=5,11,17,23,29$. Frobenius is a transposition, and $L_p(s,\rho_2)^{-1}=1-p^{-2s}$.
- If $p\equiv1\pmod3$ and 2 is a cube modulo $p$, the polynomial has three linear factors, as at $p=31,43$. Frobenius is the identity, and $L_p(s,\rho_2)^{-1}=(1-p^{-s})^2$.
- If $p\equiv1\pmod3$ and 2 is a noncube modulo $p$, the polynomial is irreducible, as at $p=7,13,19$. Frobenius is a three-cycle, and $L_p(s,\rho_2)^{-1}=1+p^{-s}+p^{-2s}$.

The representation $\rho_2$ is induced from a nontrivial character of the cyclic subgroup of order three in $S_3$. Class field theory gives a cubic Hecke character $\psi_3$ over $F$ with $L(s,\rho_2)=L_F(s,\psi_3)$. A product of two Dirichlet functions over $\mathbb Q$ would have a Frobenius trace periodic in the prime modulo a fixed conductor, away from its prime divisors.

The primes $31$ and $367$ are congruent modulo $48$. The cubic polynomial has roots $4,7,20$ modulo $31$ and no root modulo $367$, since $2^{122}\equiv283\pmod{367}$. Its two-dimensional traces are therefore $2$ and $-1$. In Crossley’s 547/727 example the eight Dirichlet characters give traces $-8$ and $8$ at the same primes. Three finite prime-race scores recover each of those traces unconditionally. This abelian trace is periodic modulo $16\cdot547\cdot727$. [Three-score theorem](https://doi.org/10.5281/zenodo.24413208)

For each $M\ge1$, both cubic traces occur among primes $p\equiv1\pmod M$. The intersection $L\cap\mathbb Q(\zeta_M)$ is abelian over $\mathbb Q$. Every $3$-cycle belongs to the commutator subgroup $A_3$ of $S_3$, so it fixes the intersection. The identity and a $3$-cycle therefore each extend to the compositum while fixing $\mathbb Q(\zeta_M)$. Chebotarev gives primes of each type. Rosen, Takeyama, Tasaka and Yamamoto discuss this classical cubic example in their introduction. [Splitting of primes, section 1.1](https://arxiv.org/html/2208.11381v4#S1.SS1)

**Step 3. Brauer induction.** Let $L/\mathbb Q$ be any finite Galois extension with group $G$. Brauer’s theorem expresses each irreducible character $\rho$ as an integral sum of characters induced from linear characters $\psi_i$ of elementary subgroups $H_i$. The characters on the right give Hecke functions over the corresponding fixed fields `[Brauer1947]`.

$$
\rho=\sum_{i=1}^r n_i \mathrm{Ind}_{H_i}^G(\psi_i),
\qquad
L(s,\rho)=\prod_{i=1}^r L_{L^{H_i}}(s,\psi_i)^{n_i},
\qquad n_i\in\mathbb Z.
$$

The action of $A_5$ on five letters gives its irreducible character of degree four as $\rho_4=\mathrm{Ind}_{A_4}^{A_5}\mathbf{1}-\mathbf{1}$. A proper subgroup of index $d\le4$ would give a nontrivial action of the simple group $A_5$ on $d$ cosets. Simplicity makes the action faithful, which would embed the group of order 60 in a group of order at most 24. Thus a character induced from a proper subgroup has degree at least five. The only linear character of $A_5$ itself is trivial. Any expression for $\rho_4$ as an integral sum of characters induced from linear characters therefore needs a negative coefficient. [Character table and subgroup indices](https://www.math.rwth-aachen.de/homes/sam/ctbllib/ctbltoc/data/A5.html)

Assume GRH for the finite-order Hecke characters $\psi_i$ over their respective fields $L^{H_i}$. On $\Re(s)>1/2$ with $s\ne1$, all factors in the Brauer product are holomorphic and nonzero. At $s=1$ each trivial $\psi_i$ gives a simple pole, and each nontrivial $\psi_i$ has a finite nonzero value. Frobenius reciprocity gives $\sum_{i:\psi_i=\mathbf{1}}n_i=\langle\rho,\mathbf{1}\rangle_G$. Thus $L(s,\rho)$ is regular and nonzero at $1$ for a nontrivial irreducible $\rho$, while the trivial representation gives the simple pole of $\zeta(s)$. These Hecke hypotheses imply RH for $\zeta_L$ by Artin factorisation. On the critical line, holomorphy of the quotient still requires control of the multiplicities of denominator zeros.

The statement `EveryCharacter` concerns Dirichlet characters over $\mathbb Q$. The cubic example requires a Hecke character over $\mathbb Q(\zeta_3)$. Hooley’s conditional proof of Artin’s primitive root conjecture uses the Dedekind zeta functions of $\mathbb Q(\zeta_m,a^{1/m})$ for squarefree positive integers $m$ `[Hooley1967]`.

### 16.2.2 Build determinism versus kernel soundness: Sutherland's 175,186 / 175,187 `.olean` experiment

A second point of frequent confusion concerns compiled `.olean` file hashes versus exported kernel
declarations (`sources/SOURCES.md` §5 and `fetches/sutherland_grh.html`, updated `2026-11-22 03:10 UTC`)
`[Community]` [Expository]:

1. **Why `.olean` hashes usually differ across machines:** In Lean `v4.33.1`, `.olean` files serialize
   linter messages containing the absolute filesystem path of the `.lean` source file; in Alpöge's
   archive, `98,219` of `175,187` modules emit linter messages (storing `/home/ubuntu/grh/src/lean/src/…`),
   while `76,968` modules — **including `Main.olean` (`sha256 9146dfb4…`) and `Statements.olean`** — emit
   none and match across LUMI, Dixit, and Sutherland `[Community]`.
2. **The sole 38-byte parallel-elaboration race (`LocModel.olean`):** On 21 November, Sutherland ran a
   fresh **bubblewrap-sandboxed `lake build Main`** (no network, read-only source) at the **exact same
   path** `/home/ubuntu/grh/src/lean`: **175,186 of 175,187 `.olean` files were byte-for-byte identical**,
   and the single exception —
   `Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LocModel.olean` —
   differed in just **38 bytes**: the user-facing name of a bound variable inside an auto-generated
   equation lemma `BBtop.eq_1` requested concurrently by two parallel-elaborated theorems (Lean issue
   `#15498`, fixed in `v4.36.0` by PR `#15499`, and 100% deterministic under single-threaded `lean -j1`)!
3. **Why the kernel export is 100% immune:** Bound-variable display names are ignored by de Bruijn
   indices in `lean4export`: **the 61,570,595,788-byte proof export generated inside that isolated
   sandbox has sha256 `5ea74b91…244e`, byte-for-byte identical to the published export** `[Community]`!
   That closes one of the main items listed as pending in Chapter 1!

### 16.2.3 Worked specimen of auditing a `GlobalTheory.Published.*` theorem (`FerreroWashington` vs `GlobalArtinReciprocity`)

Finally, let us illustrate in four concrete steps what it means to audit one of the 257 internal
"literature" declarations (`P18`, Chapter 13) [Lean, read] [Expository]:

1. **Locate both the `Prop` declaration, its proof wrapper, and its consumer:** Compare
   `GlobalTheory.Published.FerreroWashington`
   (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:10`)
   against `PositivityTheory.Stage1.PM.globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity`
   (`src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8`)
   [Lean, read].
2. **Check quantifiers against the published theorem:** In `FerreroWashington.lean:10`, the `Prop`
   asserts that for every prime $p$, every number field $K$ abelian over $\mathbb Q$, and the
   cyclotomic $\mathbb Z_p$-extension $K_\infty / K$, the Iwasawa $\mu$-invariant vanishes — matching
   the full unconditional statement of `[FerreroWashington1979]` (*Faithful* `[Lean, read]`)! By
   contrast, for `GlobalTheory.Published.GlobalArtinReciprocity` (`GlobalArtinReciprocity.lean:8`,
   consumed at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:45`
   in Chapter 10), one checks whether the `Prop` bundles the full idelic Artin reciprocity package
   (`rayClassFieldSt` at `:11`, `heckeLAdicCharacter` at `:14`) or a domain-restricted avatar
   supplying the unramified Hilbert-class-field bound invoked by `UnramHom.length_le_classNumber`!
3. **Verify non-vacuity of hypotheses:** Check that no hypothesis in the `Prop` is unsatisfiable or
   circularly strong (for example, in `KatoTwoW`, Ishaan Dixit asked on Zulip `#642435200` whether a
   missing $L(1, f) \neq 0$ hypothesis made the statement stronger than `[Kato2004]`; David Loeffler
   showed at `#642442900` that in the archive's analytic normalization $s = 1$ lies right of the
   critical center $s = \frac{1}{2}$, where $L(1, f) \neq 0$ holds automatically `[Community]`!).
4. **Assign two separate tags:** Even when an internal `Prop` turns out to be a domain-restricted
   special case (as LUMI `docs/07-named-theorems.md` found for 29 of 105 audited items `[Community]`),
   the implication inside `Main.lean` remains 100% kernel-valid (`[Lean]`), while only *Faithful*
   statements qualify for standalone reuse as Mathlib theorems under their classical names!

---

## 16.3 Consolidated verification ledgers (`2026-11-22 03:30 UTC`)

We now assemble four master ledgers recording exactly what has been verified and what remains `[Open]`.

### 16.3.1 Ledger 1: Machine compilation, sandbox isolation, and independent proof kernels (Alpöge archive)

| Verification item | Tool / runner | Status (`2026-11-22 03:30 UTC`) | Exact scope & evidence |
|---|---|---|---|
| Archive byte integrity | Sutherland, LUMI, `leanprover-community`, this book | **Passed** `[Lean, read]` / `[Community]` | 14 parts join to `239,275,554` bytes, sha256 `9631b4f0…49c7fc`; 175,187 `.lean` files, `17,374,215` lines. |
| Statement & Mathlib pin | `Statements.lean`, `Challenge.lean`, Chapter 1 | **Passed** `[Lean, read]` / `[Community]` | All 5 theorems in `Main.lean` use unmodified Mathlib `v4.33.1` (`0df444a3`); PR #34 proved machine equivalence with `formal-conjectures` Dirichlet GRH. |
| Axiom & static metaprogramming audit | `#print axioms`, `NOTES.md`, LUMI, our `rhaudit` (`186,200` `.olean` stream) | **Passed** `[Lean, read]` / `[Community]` | Only `propext`, `Classical.choice`, `Quot.sound`; zero `sorryAx`, zero `Lean.ofReduceBool`/`native_decide`, zero CShorcuts; 4 custom tactics elaborate to standard kernel terms. |
| No-network sandboxed `lake build` + export match | LUMI (8 nodes), Sonoda (RIKYU), Sutherland (bubblewrap) | **Passed** `[Community]` | Sutherland's sandboxed `lake build Main` (`18:07 UTC` 21 Nov) produced a **byte-identical** `61,570,595,788`-byte export (`5ea74b91…244e`, `19:32 UTC` 21 Nov; also matched by Dixit). |
| Module-by-module native & Lean-in-Lean replay | `leanchecker` (`v4.33.1`) & `lean4lean` (`67f63b0c`) | **Passed** `[Community]` | `175,187 / 175,187` `.olean` modules accepted (`lean4lean` passed 175,182 at default fuel + 5 `decide +kernel` modules with raised fuel). |
| Independent Rust kernel on full export | `nanoda_bin` | **Passed** `[Community]` | `exit 0` in 27m42s on 80 threads (`Sutherland`), plus independent runs by `Infatoshi` and `nasqret`. |
| Verified statement-and-kernel comparators | `con-leche --compare` (`5dc36dc1`) & Rust port `con-ron --compare` (`3f22699b`) | **Passed** `[Community]` | Both accepted all `1,468,418` solution + `51,692` challenge declarations in `--verified` mode and confirmed all 5 theorems (`con-ron` `exit 0` at `23:02 UTC` 21 Nov in 7m06s on 64 threads), plus both `Robin1984` divisor-sum inequalities! |
| Additional community export checkers | `con-agua`, `Pestka`, `Gruszka`, `nanoclo`, `tenet` | **Passed (reported)** `[Community]` | Reported accepting `solution.ndjson` by Teżewski on Lean Zulip. |
| Import-tree dead-file pruning | `leanprover-community/riemann-hypothesis` (PRs `#8, #45, #57, #60, #64`) | **In progress** `[Community]` | `10,724` unused `.lean` files pruned from `Main`'s import tree so far (`164,464` remaining; Shore/LUMI measured `146,287`–`146,437` used). |
| Single-threaded Lean default & `--paranoid` kernels on 61.57 GB export | `leanchecker` / `lake comparator` (`v4.36.0` & `v4.33.0`) | **Still running** `[Open]` | Statement and axiom stages of `lake comparator` passed; single-threaded C++ kernel replay of the 61.57 GB text export still running on Sutherland's, Sonoda's, and Brasca's machines as of `2026-11-22 03:10 UTC`. |

### 16.3.2 Ledger 2: Human reading depth (`R3` vs `[Open]`) across nodes `P0`–`P18`

Across Chapters 1–13, we read in full (`R3` / `[Lean, read]`) every top-level deduction of the analytic
endgame (`P0`, `P1`, `P3`–`P6`), the complete Arakelov Harder–Narasimhan / Bost slope library (`P9`),
the formal chain-algebra / kernel-convergence / divisibility-deduction / GMA-congruence / Iwasawa-squeeze
spines of `P7`–`P12`, and the top-level Galois / local Langlands / Green / literature-assembly interfaces
of `P14`–`P18`. Below is the exact ledger of **what remains unread (`R1`/`R2` $\implies$ `[Open]` for
human mathematical digestion)** ordered by leaf-inclusive import-cone size (`notes/proof-map.md`):

| Node | Block (`chapters/`) | What we verified at `R3` (`[Lean, read]`) | Deepest unread sub-cone (`[Open]` for human reading) | Cone size |
|---|---|---|---|---|
| `P0`–`P1`, `P3` | Statements & reductions (Chs. 1–2) | **100% read (`R3`)**: `Main.lean`, `Statements.lean`, `ClaimStrip.lean`, `RhOfRight.lean`, `CritLine.lean`, `Imprimitive.lean`. | **None** (`0`–`10` modules; unused `EveryCharacter` import in `CritLine` bypassed). | `0`–`10` |
| `P4`–`P6` | Landau windows & `core_gm` (Chs. 3, 5) | **100% of analytic/chain algebra read (`R3`)**: `LandauTheorems/`, `PrimitiveCosets/`, `LipschitzWeightAndMinimum.lean`, `TopWin.lean`, `ZeroFreeAllOfTopG.lean`. | Upstream proof of `TopG` / `ChainTied` (accounted for in `P7`–`P17` below). | `9`–`753` |
| `P9` | Arakelov slopes & heights (Ch. 9) | **Core library read in full (`R3`)**: `LatticeSlopes/`, `HarderNarasimhan/` (`SlopeIneq`, `ShiftInvariance`), `DivisionHeightBoundStatement`, `GlobalBoundRefinements`. | Minor helper lemmas in `HermitianLatticesTheory` within the `763`-module cone. | `1`–`763` |
| `P13` | Auxiliary prime pairs (Ch. 4) | `PairGood`, `pairEx`, `StagePow`, `twistK`, `meanSqK`, `BadShare`, `WinPairs`, `SupplyChi`, `IsChiField` (`R3`). | Internal proofs of classical `zero_density_box`, `pnt_progressions_relative_weak_holds`, Siegel `excBound` (`[Lean]`, `[Open]`). | `260`–`1,329` |
| `P11` | Congruences $\to \mathrm{Ш}^1$ (Ch. 10) | `IdempotentChoiceDepthZero`, `CutDetOrd.main`, `CutCoreUnit.main`, `IntegralHeckeForms`, `twist_kills_selmer`, `LinkFam.main`, `divinN_of_hypV` (`R3`). | Internal proofs of `BlockDetPoly.main`, `Peel.main`, `length_cyclotomic_block_cocycles_le_sha`, and `TwistingCharacterExistence` (`[Open]`). | `207`–`3,287` |
| `P8` | Inert-prime divisibility (Ch. 8) | `WeilJacquetShalikaLaw` (all 633 lines), `DataDIVDefs`, `DataParams₂`, `JointServices`, `GServT`, `DIVRecBridgeSel` (`R3`). | Upstream proof of `Conclusion1` / `DivisionKernelData` via `FormalGroupSystem` & `trueColumns_row_sharp_bounds` (`[Open]`). | `321` / `4,699` |
| `P10` | Period gains & Gram decay (Ch. 9) | `StatementFrame` (`FrameHerm`), `GlobalTheoremInputs`, `TieGlobal`, and top wrappers `LinkG`, `LinkAltAltBis`, `LinkGl`, `Link` (`R3`). | Deep Chowla–Selberg / Siegel-mass / Rallis / Gram-matrix proof bodies inside `LinkG` (`12,612`) and `LinkAltAltBis` (`15,578`) (`[Open]`). | `306`–`15,578` |
| `P16` | Green's $\mathrm{GL}_d(\mathbb F_g)$ characters (Ch. 13) | `LabelDatum`, `GreenRegularCharacters` header, `SumRangeEqRoots` (`green_of_regular`), `TopShape` (`R3`). | Internal induction proving `GreenRegularCharacters` (`200` modules) and shape transport in `TopShape` (`16,990`) (`[Open]`). | `200` / `16,990` |
| `P15` | Partial local Langlands (Ch. 12) | `IsRecTOfIsRec` (`LawsT`, `RecTExists`) and `LocalCentralUnits/RecTExists` (`R3`). | Supercuspidal / Zelevinsky multisegment construction inside `26,672`-module cone (`[Open]`). | `1,063` / `26,672` |
| `P14` | CM Galois representations (Ch. 12) | `WeightsConjBis` (`Row0b`, `PropsB`), `RecT`, `WeakOfAtt`, `RowSrc`, `GaloisRepresentationsOfThetaLift`, `WeightOneGeometricRealization`, `TLiftK` (`R3`). | Unitary Shimura cohomology, $p$-adic Hodge / Caraiani–Shin compatibility, and congruence limit inside `66,167`-module cone (`[Open]`). | `3,150`–`66,167` |
| `P17` | Theta-lift chain families (Ch. 7) | `Hyps`, `SiegelEisensteinSecondTermHypotheses`, `WeilTensorModels`, `LiftLambdaBound`, kernel Fubini/chain-rule files, `TopPlug` (`R3`). | Deep regularized Siegel–Weil second-term & Howe-duality proof cones (`112,384`–`151k` modules) (`[Open]`). | `14,732`–`112,384` |
| `P2`, `P18` | Literature layer & assembly (Ch. 13) | `MainConclusion`, `OpenLiteratureStatements`, `GlobalArtinReciprocity`, `OpenImageCondition`, `every_character_of_literature_of_vWin` (`R3`). | Proof bodies of the 257 literature theorems + statement fidelity of ~77–83 unaudited `GlobalTheory.Published.*` constants (`[Open]`). | `151,285` |
| `P12` | Window bound `VWin` (Ch. 11) | `ExistsPageN`, `IsChiField`, `LengthEqAddEigen` (`vvle_of_parts`), `CMFieldExponentialBounds/`, `HeightAndVanishing/`, Sinnott/Ferrero–Washington spine, `KatoUse`, `TaylorWilesObstructionBound`, `TopMainZj`, `VwinOfRow` (`R3`). | Deepest single cone in the archive (**90% of all files!**): internal Euler-system / Coleman-map, $U(3)$ Picard modular surface cohomology, and patching modules (`[Open]`). | **`157,603`** |

### 16.3.3 Ledger 3: Statement fidelity of the 257 `LiteratureTheorems` (`P18`, Chapter 13)

Recall from Chapter 13 (`Section 13.5`) why `GlobalTheory.Published.*` requires careful book-keeping:
100% of these `Prop`s are **proved without axioms inside the archive** (`[Lean]`), so a specialized or
weakened `Prop` **cannot invalidate `Main.lean`** (because both its producer and its consumer sit
inside the kernel-checked graph!), **but** it *does* determine whether an internal file actually
formalizes the named classical theorem!

- **Exact declaration inventory (`rheval-lean-fidelity` & Chapter 13 `[Lean, read]`):** `257` theorems
  under `UpperTheory.LiteratureTheorems.*` (`176` `*_of_literature` + `60` `*_of_open` + `20` intermediate
  bundles + `1` master theorem `openLiteratureStatements` in `EveryCharacterOfLiteratureOfVWin.lean`),
  referencing **~182–188 distinct statement constants** in `GlobalTheory.Published.*` (plus `72` dead
  `UnusedSlot72` declarations never referenced by `Main.lean`).
- **Audited statements.** LUMI `docs/07-named-theorems.md` reports 105 AI-assisted comparisons, including 65 faithful statements, 29 special cases with a restricted domain (such as the rank-two `MorelSuh` and the curve and surface cases of `KawamataViehweg`), seven weakenings and four undetermined cases `[Community]`. Chapters 11–13 record the separate `R3` readings of `FerreroWashington`, `GlobalArtinReciprocity`, `OpenImageCondition`, `DiscreteSpectrumResidualClassification` and `KatoTwoW`. Loeffler clarified the last statement on Zulip (`#642442900`).
- **Remaining `[Open]`:** Roughly **77 to 83 `GlobalTheory.Published.*` constants** have not yet been
  compared side-by-side against the published mathematical literature by a human domain specialist `[Open]`.

### 16.3.4 Ledger 4: Open problems in Masullo's *The Music of the Primes* (Chapter 14)

| Item | Location in Masullo's PDF | Current status (`2026-11-22`) |
|---|---|---|
| **M1. Positive-width strip spectral nuclearity ($I = [-\alpha, \alpha]$, $\alpha > 0$)** | `Terminology 10.2.1.2(2)` (`p. 444`), `(10.3.1.18)` (`p. 451`), `(10.4.2.24)` (`p. 463`, fn. 8 `p. 464`) | **Open.** Close zeros contradict the individual biorthogonal bound. Pei (`doi:10.5281/zenodo.24409811`) treats the singleton $I=\lbrace 0\rbrace$ `[Community]`. Crossley’s strip proposal in `#1169` still needs comparison with `§12.5` `[Open]`. |
| **M2. Topology of adelic $\theta$-spaces (Structure Theorem I)** | `Theorem 5.2.1.1` (`p. 229`) | **Printed proof broken `[Community]` / `[Open]`** (`mccorvie/riemann-masullo` Wave 2 reports the printed proof does not work; truth of the statement is currently being tested in Lean). |
| **M3. Shell discontinuities and the local terms at $S$** | `Theorem 11.3.2.1` (`pp. 495–496`, issue `#1358`) and **empty `§12.3` (`p. 514`, fn. 1 *"Include section"*)** | **Incomplete.** Section 12.3 is needed to decompose the global geometric kernel into its local terms at $S$ and account for the vanishing unramified shells. `[Open]` |
| **M4. Explicit-formula measure factor & strip-invariance of `Theorem 12.5.1.1`** | `§B.4` (`pp. 606–625`) and `Theorem 12.5.1.1` (`pp. 519–520`, issue `#587`) | **Disputed.** The Wave 2 group in `mccorvie/riemann-masullo` is checking the local normalisations in §B.4. Issue `#587` reports a discrepancy in $\mu_1(C_F^1)$ for $\mathbb Q(i)$ and $\mathbb Q(\sqrt{-3})$. `[Open]` |
| **M5. Unwritten Chapter 13 (deducing GRH and central-zero behavior)** | `Chapter 13` (`pp. 521–522`, `Thm. 13.3.1.2` fn. 2 *"Insert statement"*) | **Unwritten in manuscript `[Paper]` / `[Open]`** (Loeffler formalized RH $\Leftarrow$ `Thm. 12.5.1.1` `[Community]`, so all substantive weight sits in M1–M4!). |

---

## 16.4 Conditional consequences: what DOES and DOES NOT follow if `EveryCharacter` stands

**Proposition 16.1.** Assume `UpperTheory.EveryCharacter` (`src/Main.lean:8`). For each positive modulus $N$ and each Dirichlet character $\chi$ modulo $N$, its $L$-function has no zero in $\Re(s)>1/2$. The principal character has a pole at $s=1$.

1. **Consequences under this hypothesis** `[Expository]` `[Community]`
   - **Classical RH.** The statements at `Main.lean:4, 6` imply $\psi(x)=x+O(x^{1/2}(\log x)^2)$ and $\pi(x)=\mathrm{li}(x)+O(x^{1/2}\log x)$ `[Davenport2000]`. For every $\varepsilon>0$ the Mertens function satisfies $M(x)=\sum_{n\le x}\mu(n)=O_\varepsilon(x^{1/2+\varepsilon})$. Robin’s and Lagarias’s divisor-sum inequalities also follow `[Lagarias2002]`. The two arithmetic statements in `ArithSolution.lean` combine the formalisation in `kimihiro64/Robin1984` with Alpöge’s theorem `[Community]`.
   - **Primes in arithmetic progressions (`[Davenport2000]`, Ch. 20):** For every modulus $q \ge 1$ and
     $\gcd(a, q) = 1$, $\psi(x; q, a) = \frac{x}{\varphi(q)} + O\bigl(x^{1/2}(\log(qx))^2\bigr)$,
     eliminating **Siegel zeros** (`[Siegel1935]`) for all Dirichlet characters over $\mathbb Q$ and
     improving Linnik's least-prime bound to $p_{\min}(q, a) \ll (\varphi(q)\log q)^2$!
   - **Ternary Goldbach and primality testing.** Deshouillers, Effinger, te Riele and Zinoviev proved under GRH in 1997 that every odd integer greater than five is a sum of three primes. Helfgott later proved this unconditionally. Miller’s 1976 deterministic primality test takes $O((\log n)^4)$ steps under its Dirichlet hypothesis. Agrawal, Kayal and Saxena subsequently gave an unconditional polynomial-time primality test. [Conditional three-prime theorem](https://doi.org/10.1090/S1079-6762-97-00031-0) [Helfgott](https://arxiv.org/abs/1312.7748) [Miller](https://www.cs.cmu.edu/~glmiller/Publications/Papers/Mi76.pdf) [Agrawal, Kayal and Saxena](https://doi.org/10.4007/annals.2004.160.781)
   - **Abelian extensions.** Suppose $K/\mathbb Q$ is a finite Galois extension with abelian Galois group. Its Dedekind zeta function satisfies RH by the Dirichlet factorisation in section 16.2.1. For comparison, the field generated by the real cube root of two has only the identity automorphism, since it contains only one root of $X^3-2$. Its Galois closure has group $S_3$.

2. **Results requiring further hypotheses** `[Expository]`

   - **Other number fields.** Section 16.2.1 exhibits the extra Hecke factor for $K=\mathbb Q(\sqrt[3]{2})$. For a number field with nonabelian Galois closure, such as a nonsolvable quintic field, the permutation action on its embeddings is faithful. A direct sum of linear characters has abelian image, so it cannot give this permutation action. Bach’s conditional bound $O((\log\lvert\Delta_K\rvert)^2)$ for the norms of prime ideals generating the ideal class group uses hypotheses over the number field.
   - **Unitary Hecke $L$-functions $L_F(s, \chi)$ over number fields $[F : \mathbb Q] > 1$** (`[Hecke1920]`),
     including CM Grossencharacters over imaginary quadratic fields.
   - **Artin functions and primitive roots.** Brauer induction for nonabelian Artin functions involves Hecke characters over number fields `[Artin1924]` `[Brauer1947]`. In Hooley’s proof, a nonsquare integer $a\ne-1$ is a primitive root modulo infinitely many primes under RH for the Dedekind zeta functions of $K_m=\mathbb Q(\zeta_m,a^{1/m})$ for squarefree positive integers $m$. For $a=2$, the field $K_2=\mathbb Q(\sqrt2)$ is quadratic and $K_3$ has nonabelian group $S_3$, as in section 16.2.1. At the squarefree index six, $K_6$ is the compositum of those two fields. [Hooley](https://doi.org/10.1515/crll.1967.225.209) [Squarefree indices](https://www.cs.uleth.ca/~akbary/2211.13913.pdf)
   - **Automorphic / elliptic-curve / modular-form GRH ($\mathrm{GL}_2$ and $\mathrm{GL}_n$, $n \ge 2$):**
     GRH for Ramanujan's $\Delta$-function $L(s, \Delta)$, holomorphic newforms $L(s, f)$, Maass forms,
     and elliptic curves $L(E, s)$ over $\mathbb Q$ (nor the Birch and Swinnerton-Dyer conjecture!).
   - **Simplicity of zeros, Montgomery's Pair Correlation Conjecture, and the Grand Simplicity Hypothesis (GSH):**
     None of the five theorems in `Main.lean` says anything about the **multiplicity** $N(\rho)$ of
     critical-line zeros or linear independence of $\gamma > 0$ over $\mathbb Q$! Whether $\zeta(s)$ has
     only simple zeros (`N(\rho) = 1`) remains **completely `[Open]`**!

---

## 16.5 Actionable checklist for readers who want to contribute

One of the best features of an open formal archive and an open textbook is that **every reader can check
something concrete without trusting anyone's summary**. Depending on your background, here are four
high-leverage ways to help advance the verification and human digestion of both works:

1. **For Lean 4 and Mathlib contributors (`leanprover-community/riemann-hypothesis` & `mccorvie/riemann-masullo`):**
   - *Dead-code & wrapper pruning on Alpöge's archive:* Clone `leanprover-community/riemann-hypothesis`,
     run `lake exe cache get`, and help collapse redundant transport wrappers or isolate standalone
     sub-libraries — starting with **Chapter 9's 68-module Arakelov Harder–Narasimhan / Bost slope
     library** (`src/Formalism/LatticeSlopes/` and `src/Formalism/HarderNarasimhan/`), which imports
     only Mathlib and is ready for clean upstreaming!
   - *Wave 2 testing on Masullo's draft:* In `mccorvie/riemann-masullo`, help test whether a repaired
     statement of `Theorem 5.2.1.1` (`p. 229`) holds in Lean `v4.36.0` and help recompute the exact
     measure normalizations of `Theorem B.4.4.7` (`p. 623`, issue `#587`).
2. **For algebraic number theorists, Iwasawa theorists, and arithmetic geometers:**
   - *Audit the ~80 remaining `GlobalTheory.Published.*` declarations (`P18`, Chapter 13):* Pick one
     unaudited file under `src/Development/AbelianVarietyTheory/PublishedTheorems/` or
     `src/Formalism/.../StandardTheoremStatements/`, read its Lean `def` (typically 20–60 lines!), and
     compare every hypothesis against the published paper (`[HarrisTaylor2001]`, `[Shin2011]`,
     `[Kato2004]`, `[Thorne2015]`, `[KudlaRallis1994]`), classifying it as *Faithful*, *Domain-restricted
     special case*, or *Weakened*.
   - *Excavate the deep cones of `P12` (`VwinOfRow`, 157,603 modules) and `P8` (`DIVRecBridgeSel`, 4,699 modules):*
     Trace how `FormalGroupSystem.Conclusion1`/`Conclusion2` (`FormalGroupSystem.lean:633, 649`) proves
     single-step Lubin–Tate theta-kernel divisibility at inert primes, and how `U3` Picard modular
     surface congruences feed `PropGK` (`KatoUse.lean:36`, Chapter 11).
3. **For automorphic representation theorists and harmonic analysts:**
   - *Read the `12,612`–`15,578`-module cones of `LinkG` and `LinkAltAltBis` (`P10`, Chapter 9) and the
     `26,672`-module cone of `RecTExists` (`P15`, Chapter 12):* Extract a clean 20-page human proof of
     how the archive establishes stretched-exponential Gram-matrix decay $\exp(-x^{\varepsilon/8})$
     across amplified theta-lift words without full Arthur endoscopic classification, and how `LawsT`
     suffices in place of full Henniart–Harris–Taylor local $\varepsilon$-factor matching!
4. **For functional analysts and spectral theorists:**
   - For M1 and M4, consider Masullo’s spaces $W_{[-\alpha,\alpha]}^{s,2}\mathcal H_F$. One question is whether, for a Beurling model with zeros off the line, residues of zeros outside the strip change the geometric kernel trace as $\alpha$ varies. Another is whether a nuclear trace formula on $I=[-\alpha,\alpha]$ of positive width can be matched to section 12.5 without assuming zero-freeness outside $\frac{1}{2}+I$ first.
5. **For readers of this book (`Li-Hongmin/amazing-riemann-hypothesis`):**
   - Every `src/…:line` citation, status tag, and mathematical proof in Chapters 0–16 is maintained in
     the public repository. If you read a deeper sub-cone at level `R3`, spot an imprecision, or resolve
     an `[Open]` item in Ledgers 1–4 above, open an issue or pull request with the exact `file:line` or
     page number so the public record stays sharp, honest, and reproducible.

---

**Summary.** As of 03:30 UTC on 22 November 2026, a sandboxed build of Alpöge’s archive had reproduced the 61,570,595,788-byte export. Its SHA-256 digest begins with `5ea74b91` and ends with `244e`. Leanchecker and lean4lean checked the compiled modules. Nanoda and con-leche accepted the export. Con-leche and con-ron also matched all five challenge statements. The checks identified three standard Lean axioms. The full export-level comparator runs were in progress at that update `[Community]` `[Open]`. [Verification logs](https://math.mit.edu/~drew/grh/)

Chapters 1–13 describe the proof’s structure from `P0` to `P18`. We read the statements, the analytic endgame, the Arakelov slope library, the chain-bracket calculations, the inert-prime valuation algebra, the GMA congruence reductions leading to $\mathrm{Ш}^1$, and the Langlands, Galois and Green interfaces `[Lean, read]`. The deeper proof dependencies include about 146,000 modules, and about 80 named statements in `GlobalTheory.Published.*` remain to be compared with the literature `[Open]`.

Chapters 14–15 examine Masullo’s 940-page *The Music of the Primes*. The positive-width Hardy–Sobolev argument includes a failed biorthogonal bound on pages 444, 451 and 463, an omitted section 12.3 on page 514, and an unwritten chapter 13 beginning on page 521 `[Paper]` `[Open]`. The Artin and Brauer examples in section 16.2.1 explain the scope of Dirichlet GRH. The extended hypothesis for general number fields, Artin’s primitive root conjecture, automorphic GRH for $\mathrm{GL}_2$ and simplicity of zeta zeros each require further arguments.
