# Chapter 16. Open problems and what remains to be checked

> **Status tags used in this chapter:** `[Lean, read]` for archive statements, static-audit facts, and
> proofs verified line by line by us (`R3`); `[Lean]` for compiled archive declarations inspected at
> statement level (`R1`/`R2`); `[Paper; remark p. …]` and `[Paper; Masullo p. …]` for primary
> documents; `[Community]` for public machine-check logs, repository audits, and community reports
> checked online through `2026-11-22 04:35 UTC`; `[Expository]` for classical number-theoretic proofs
> and worked examples on scope boundaries; `[Open]` for pending kernel replays, unaudited statement
> matches, unread deep proof cones, and unresolved gaps in Masullo's draft.

Across Chapters 1 through 15 (alongside **Chapter 17** on host-field Behrend geometry and **Chapter 18**
on `GlobalTheory.Published.*` statement-fidelity case studies), our
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
`2026-11-22 04:35 UTC`, preceded by two concrete worked examples — one in algebraic number theory and
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
  case in proving `src/Main.lean` drops essentially to zero** (modulo simultaneous soundness bugs across
  independent kernels in Lean, Rust, and C++, or a definition bug in Mathlib's eight `LSeries` files).
- **What kernels do NOT supply on their own:**
  1. A kernel checks that `UpperTheory.FinalTheorems.everyCharacter` has type `EveryCharacter`, **not**
     whether an internal helper `Prop` named `GlobalTheory.Published.GlobalArtinReciprocity` or
     `KawamataViehwegVanishing` is the textbook theorem or a specialized avatar (so nobody should reuse
     an unaudited internal module as a black-box library theorem without reading its `def`! Chapter 13).
  2. A kernel gives zero mathematical insight into **why** the proof works or how to simplify 17.37
     million lines into a human-checkable monograph and reusable Mathlib theorems.
  3. Above all, a kernel proves **only the exact `Prop`s in `src/Main.lean`** — namely `EveryCharacter`
     (Dirichlet $L$-functions over $\mathbb Q$). In the press and on social media, dozens of commentators
     have conflated "GRH for Dirichlet $L$-functions" with the **Extended Riemann Hypothesis (ERH)** for
     Dedekind zeta functions $\zeta_K(s)$ of **arbitrary** number fields $K$ and Artin $L$-functions
     `[Artin1924]`! Let us see by an explicit hand calculation why that conflation is mathematically
     false.

---

## 16.2 Worked examples of scope boundaries and verification subtleties

### 16.2.1 Non-abelian Dedekind and Artin $L$-functions: $K = \mathbb Q(\sqrt[3]{2})$, $S_3$, and negative Brauer exponents

Let us test what `EveryCharacter` (`∀ N χ s, 1/2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → L(s, χ) ≠ 0`,
`src/Main.lean:8`) [Lean, read] tells us — and **fails** to tell us! — about Dedekind zeta functions
$\zeta_K(s) = \sum_{\mathfrak a \subseteq \mathcal O_K} (N_{K/\mathbb Q}\mathfrak a)^{-s}$ of number
fields $K$ `[Artin1924]`, `[Brauer1947]` [Expository].

**Step 1: Abelian $K / \mathbb Q$ IS covered (e.g. $K = \mathbb Q(\zeta_8)$ or $\mathbb Q(\sqrt{5})$).**
If $K / \mathbb Q$ is Galois with **abelian** Galois group $G = \operatorname{Gal}(K/\mathbb Q)$, then
by the **Kronecker–Weber theorem** $K \subseteq \mathbb Q(\zeta_N)$ for some integer $N \ge 1$. Every
irreducible character of the finite abelian group $G$ is $1$-dimensional and factors through
$(\mathbb Z / N\mathbb Z)^\times \twoheadrightarrow G$, defining a primitive Dirichlet character
$\chi^\ast$ of conductor $f_\chi \mid N$ such that
$$\zeta_K(s) \;=\; \prod_{\chi \in \widehat{G}} L(s, \chi^\ast)!$$
Since every factor $L(s, \chi^\ast)$ is literally a `DirichletCharacter.LFunction` over $\mathbb Q$,
**`EveryCharacter` immediately proves RH for $\zeta_K(s)$ for every abelian extension $K / \mathbb Q$!**

**Step 2: Non-abelian cubic $K = \mathbb Q(\sqrt[3]{2})$ already exits `EveryCharacter`!**
Now take the simplest non-abelian number field in algebraic number theory:
$$K := \mathbb Q(\sqrt[3]{2}) \qquad ([K : \mathbb Q] = 3),$$
whose Galois closure over $\mathbb Q$ is $L = \mathbb Q(\zeta_3, \sqrt[3]{2})$ with non-abelian Galois
group $G = \operatorname{Gal}(L/\mathbb Q) \cong S_3$ of order $6$ (`\operatorname{Gal}(L/K) \cong C_2`,
quadratic resolvent $F = \mathbb Q(\zeta_3) = \mathbb Q(\sqrt{-3})$)!

Factor the permutation representation $\operatorname{Ind}_{C_2}^{S_3}(\mathbf{1})$ of $S_3$ on the three
roots of $X^3 - 2$: it splits into the trivial character $\mathbf{1}$ plus the unique **$2$-dimensional
irreducible character $\rho_2$** of $S_3$ ($\chi_{\rho_2}(1) = 2$, $\chi_{\rho_2}((12)) = 0$,
$\chi_{\rho_2}((123)) = -1$). By Artin's formalism `[Artin1924]`,
$$\zeta_{\mathbb Q(\sqrt[3]{2})}(s) \;=\; \zeta(s)\,L(s, \rho_2),
\qquad
\zeta_{\mathbb Q(\zeta_3, \sqrt[3]{2})}(s) \;=\; \zeta(s)\,L(s, \chi_{-3})\,L(s, \rho_2)^2!$$
Check the Euler factors of $L(s, \rho_2)$ at unramified primes $p \nmid 6$ by hand from the splitting
of $X^3 - 2 \pmod p$:

- **Primes $p \equiv 2 \pmod 3$ ($p = 5, 11, 17, 23, 29, \dots$):** Raising to the $3$-rd power is a
  bijection on $\mathbb F_p^\times$ ($\gcd(3, p-1) = 1$), so $X^3 - 2 \equiv (X - a)(X^2 + aX + a^2) \pmod p$
  always has **one linear and one quadratic factor**! Frobenius is a transposition $(12) \in S_3$, so
  $\det(I - p^{-s}\rho_2(\mathrm{Frob}_p)) = 1 - p^{-2s}$, matching
  $(1 - p^{-s})(1 - p^{-2s}) = (1 - p^{-s})\cdot L_p(s, \rho_2)^{-1}$!
- **Primes $p \equiv 1 \pmod 3$ where $2$ IS a cube mod $p$ ($p = 31, 43, \dots$; indeed $4^3 = 64 \equiv 2 \pmod{31}$!):**
  $X^3 - 2$ splits into **three linear factors**, Frobenius is $1 \in S_3$, and
  $L_p(s, \rho_2)^{-1} = (1 - p^{-s})^2$.
- **Primes $p \equiv 1 \pmod 3$ where $2$ is NOT a cube mod $p$ ($p = 7, 13, 19, \dots$):** $X^3 - 2$
  is **irreducible mod $p$**, Frobenius is a $3$-cycle $(123) \in S_3$, and
  $L_p(s, \rho_2)^{-1} = 1 + p^{-s} + p^{-2s}$.

Can $L(s, \rho_2)$ be written as a product of Dirichlet $L$-functions over $\mathbb Q$? **No!** A
product $L(s, \psi_1) L(s, \psi_2)$ of two Dirichlet characters over $\mathbb Q$ would have trace
$\psi_1(p) + \psi_2(p)$ periodic in $p$ modulo some integer $M$, whereas whether $2$ is a cube mod $p$
for $p \equiv 1 \pmod 3$ is governed by cubic reciprocity in $\mathbb Z[\zeta_3]$ ($p = a^2 + 27b^2$,
a weight-$1$ CM modular form $\sum q^{a^2+27b^2} - \dots$!), **not** by any congruence on $p \pmod M$!
Indeed, $\rho_2 = \operatorname{Ind}_{C_3}^{S_3}(\psi_3)$ is induced from a cubic **Hecke character
$\psi_3$ of the imaginary quadratic field $F = \mathbb Q(\zeta_3)$** (so $L(s, \rho_2) = L_F(s, \psi_3)$
lies in Masullo's target class, **not** in `EveryCharacter`!).

**Step 3: Why Brauer's induction theorem (`[Brauer1947]`) CANNOT propagate zero-freeness to general non-abelian $\zeta_K(s)$!**
Now ask what happens if we pass to general finite Galois groups $G = \operatorname{Gal}(L/\mathbb Q)$, such as
an **icosahedral $A_5$ extension** ($G \cong A_5$, order $60$)? By **Brauer's induction theorem**
`[Brauer1947]`, every irreducible character $\rho$ of $G$ is a **virtual $\mathbb Z$-linear combination**
of $1$-dimensional characters $\psi_i$ induced from elementary subgroups $H_i \le G$:
$$\rho \;=\; \sum_{i = 1}^r n_i \operatorname{Ind}_{H_i}^G(\psi_i) \qquad (n_i \in \mathbb Z),
\qquad\text{so}\qquad
L(s, \rho) \;=\; \prod_{i = 1}^r L_{L^{H_i}}(s, \psi_i)^{n_i}!$$
Look closely at the signs of the integers $n_i \in \mathbb Z$! For non-monomial groups like $A_5$
(for instance, the $4$-dimensional irreducible character $\rho_4$ of $A_5$: although $4 \mid 60$,
inducing a degree-$4$ character from a $1$-dimensional character requires a subgroup of **index $4$,
order $15$**, and the simple group $A_5$ has **no subgroup of index $4$** — its maximal proper subgroups
$A_4$, $D_{10}$, and $S_3$ have orders $12, 10, 6$, i.e. indices $5, 6, 10$!), **at least one integer $n_i$ MUST
be strictly negative ($n_i < 0$)!**

Now watch what happens even if someone proved GRH for **every** abelian character $\psi_i$ of **every**
intermediate subfield $L^{H_i}$ (i.e. **all of Masullo's unitary Hecke GRH**!):
- Because $L_{L^{H_i}}(s, \psi_i) \neq 0$ on $\Re s > \frac{1}{2}$ for every $i$, **neither the
  numerator factors ($n_i > 0$) nor the denominator factors ($n_i < 0$) vanish on $\Re s > \frac{1}{2}$**,
  so **Masullo's full Hecke GRH across all number fields WOULD imply ERH for $\zeta_L(s)$ and nonvanishing
  of $L(s, \rho)$ on $\Re s > \frac{1}{2}$** (though **not** holomorphy — Artin's conjecture — at a
  critical-line point $\frac{1}{2} + i\gamma$ if a denominator zero had higher multiplicity than the
  numerator!).
- By contrast, **Alpöge's `EveryCharacter` proves GRH ONLY over the base field $\mathbb Q$** ($H_i = G$),
  knowing **nothing at all** about $L_{L^{H_i}}(s, \psi_i)$ when $[L^{H_i} : \mathbb Q] > 1$! Thus
  `EveryCharacter` **does not** prove RH for $\zeta_{\mathbb Q(\sqrt[3]{2})}(s)$, **does not** prove RH
  for general Dedekind $\zeta_K(s)$ (ERH), and **does not** unconditionalize theorems such as Hooley's
  proof of Artin's primitive root conjecture `[Hooley1967]`, which explicitly require ERH for non-abelian
  Kummer towers $\mathbb Q(\zeta_q, a^{1/q})$!

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

1. **Locate the `Prop` declaration itself (not merely its proof wrapper!) and its consumer:** Compare
   `UpperTheory.V.Published.FerreroWashington`
   (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:7`)
   against `GlobalTheory.Published.GlobalArtinReciprocity`
   (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70–72`),
   carefully distinguishing that `Prop` definition (`∃ art : Idele E →* GalAb E Ω, IsGlobalArtin E Ω art`,
   `:25–40`) from the 17-line proof-term wrapper file
   `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8–15`
   (`globalArtinReciprocity`, `rayClassFieldSt`, `heckeLAdicCharacter`) [Lean, read]!
2. **Check quantifiers against the published theorem:** In `PublishedTheorems/FerreroWashington.lean:7`,
   the `Prop` quantifies over every abelian number field $K / \mathbb Q$ and prime $\ell$, adding the
   harmless base-layer root-of-unity hypothesis `∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l)`
   and finite $J$-localization (`IsLocalizedAt 𝔮 c`, bounding $\ell$-torsion of $\mathrm{Cl}_J(K_n)[\ell^\infty]$
   by $\ell^C$, equivalent to `[FerreroWashington1979]` via finite base change $K(\mu_{2\ell})/K$!).
   Meanwhile, in `ExistsUniqueHcharOfFiniteOrder.lean:70–72` (consumed at
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:45`
   in Chapter 10), `IsGlobalArtin` states the full idèlic Artin reciprocity theorem over **every**
   number field $E$ (*Faithful* `[Lean, read]`), while `RayClassFieldSt` and `HeckeLAdicCharacter` are
   separate companion `Prop`s (`NonemptyAlgHomOfIsRayOfDvd.lean:17` and `ExistsUniqueHcharOfFiniteOrder.lean:74`;
   all three audited in full in **Chapter 18**, Section 18.2)!
3. **Verify non-vacuity and off-center guards:** Check that no hypothesis in the `Prop` is unsatisfiable or
   silently omits a required condition (for example, in `UpperTheory.V.Published.Kato`,
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/QuotRepMk.lean:65`,
   Ishaan Dixit asked on Zulip `#642435200` whether omitting $L(f, \chi, r) \neq 0$ made the statement
   stronger than `[Kato2004]`; David Loeffler pointed out at `#642442900` `[Community]`, and we verify
   line by line in **Chapter 18**, Lemma 18.2(1) `[Lean, read]`, that the guard `2 * r ≠ k` keeps every
   integer $1 \le r \le k - 1$ at distance $\ge \frac{1}{2}$ from $\frac{k}{2}$, where Euler-product
   non-vanishing and the functional equation force $L(f, \chi, r) \neq 0$ automatically!).
4. **Assign two separate tags:** Even when an internal `Prop` turns out to be a domain-restricted
   special case (as LUMI `docs/07-named-theorems.md` found for 29 of 105 audited items `[Community]`,
   and as Chapter 18 verifies for `BaseChangeDefiniteUnitary`, `PoitouTateNormalised`, and `ClozelPurity`
   `[Lean, read]`),
   the implication inside `src/Main.lean` remains 100% kernel-valid (`[Lean]`), while only *Faithful*
   statements qualify for standalone reuse as Mathlib theorems under their classical names!

---

## 16.3 Consolidated verification ledgers (`2026-11-22 04:35 UTC`)

We now assemble four master ledgers recording exactly what has been verified and what remains `[Open]`.

### 16.3.1 Ledger 1: Machine compilation, sandbox isolation, and independent proof kernels (Alpöge archive)

| Verification item | Tool / runner | Status (`2026-11-22 03:30 UTC`) | Exact scope & evidence |
|---|---|---|---|
| Archive byte integrity | Sutherland, LUMI, `leanprover-community`, this book | **Passed** `[Lean, read]` / `[Community]` | 14 parts join to `239,275,554` bytes, sha256 `9631b4f0…49c7fc`; 175,187 `.lean` files, `17,374,215` lines. |
| Statement & Mathlib pin | `src/Statements.lean`, `Challenge.lean`, Chapter 1 | **Passed** `[Lean, read]` / `[Community]` | All 5 theorems in `src/Main.lean` use unmodified Mathlib `v4.33.1` (`0df444a3`); PR #34 proved machine equivalence with `formal-conjectures` Dirichlet GRH. |
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
| `P0`–`P1`, `P3` | Statements & reductions (Chs. 1–2) | **100% read (`R3`)**: `src/Main.lean`, `src/Statements.lean`, `ClaimStrip.lean`, `RhOfRight.lean`, `CritLine.lean`, `Imprimitive.lean`. | **None** (`0`–`10` modules; unused `EveryCharacter` import in `CritLine` bypassed). | `0`–`10` |
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
weakened `Prop` **cannot invalidate `src/Main.lean`** (because both its producer and its consumer sit
inside the kernel-checked graph!), **but** it *does* determine whether an internal file actually
formalizes the named classical theorem!

- **Exact declaration inventory (`rheval-lean-fidelity` & Chapter 13 `[Lean, read]`):** `257` theorems
  under `UpperTheory.LiteratureTheorems.*` (`176` `*_of_literature` + `60` `*_of_open` + `20` intermediate
  bundles + `1` master theorem `every_character_of_literature_of_vWin` at `:810`, discharging the
  `structure OpenLiteratureStatements : Prop` at `:215` in `EveryCharacterOfLiteratureOfVWin.lean`),
  referencing **~182–188 distinct statement constants** in `GlobalTheory.Published.*` and
  `UpperTheory.V.Published.*` (including the `True` fossil `GlobalTheory.Published.UnusedSlot72` at
  `DiscreteSpectrumResidualClassification.lean:7`, alongside unreferenced fossil declarations outside
  `src/Main.lean`'s closure).
- **Audited so far (`LUMI docs/07-named-theorems.md` `[Community]` + Chapters 11, 13, and 18 `[Lean, read]`):**
  `105` statements audited at AI-assisted community level (`65` faithful, `29` domain-restricted special
  cases such as rank-$2$ `MorelSuh` or curve/surface `KawamataViehweg`, `7` safe weakenings, `4`
  undetermined), **plus 15 propositions audited directly line by line (`R3`) in Chapters 13 and 18**
  (`GreenRegularCharacters`, `GlobalArtinReciprocity`, `HeckeLAdicCharacter`,
  `RayClassFieldSt`/`RayClassFieldMaximalSt`, `ChebotarevDegreeOne`, `FerreroWashington`,
  `SiegelKlingen`/`DeligneRibet`/`SiegelKlingenDeligneRibet`, `Kato`/`KatoUse`,
  `PoitouTateNormalised`/`PoitouTateDuality`, `ClozelPurity`/`RegularAlgebraicPurity`,
  `BaseChangeDefiniteUnitary`/`BaseChangeIsobaric`, `WeilSiegelFormula`/`WeilSiegelFormulaUnitary`/`SiegelWeilUnitaryConvergent`,
  and `DeRhamPotSemistable`).
- **Remaining `[Open]`:** Roughly **70 `GlobalTheory.Published.*` constants** have not yet been
  compared side-by-side against the published mathematical literature by a human domain specialist `[Open]`
  (see **Chapter 18**, Section 18.5.1, for the standard five-step audit rubric).

### 16.3.4 Ledger 4: Open problems in Masullo's *The Music of the Primes* (Chapter 14)

| Item | Location in Masullo's PDF | Current status (`2026-11-22`) |
|---|---|---|
| **M1. Positive-width strip spectral nuclearity ($I = [-\alpha, \alpha]$, $\alpha > 0$)** | `Terminology 10.2.1.2(2)` (`p. 444`), `(10.3.1.18)` (`p. 451`), `(10.4.2.24)` (`p. 463`, fn. 8 `p. 464`) | **Unrepaired `[Open]`** (individual biorthogonal bound is false due to close zeros; Pei's `doi:10.5281/zenodo.24409811` addresses only $I = \{0\}$ and is unreviewed `[Community]`; `leecrossley`'s strip proposal in `#1169` does not yet match `§12.5` `[Open]`). |
| **M2. Topology of adelic $\theta$-spaces (Structure Theorem I)** | `Theorem 5.2.1.1` (`p. 230`) | **Printed proof broken `[Community]` / `[Open]`** (`mccorvie/riemann-masullo` Wave 2 reports the printed proof does not work; truth of the statement is currently being tested in Lean). |
| **M3. Shell-cutoff discontinuities & omitted global-to-$S$-local section** | `Theorem 11.3.2.1` (`pp. 495–496`, issue `#1358`) and **empty `§12.3` (`p. 514`, fn. 1 *"Include section"*)** | **Incomplete / unverified `[Open]`** (`§12.3` is the exact bridge deconstructing the global geometric kernel into $S$-local + vanishing unramified shells!). |
| **M4. Explicit-formula measure factor & strip-invariance of `Theorem 12.5.1.1`** | `§B.4` (`pp. 606–625`) and `Theorem 12.5.1.1` (`pp. 519–520`, issue `#587`) | **Disputed / under recomputation `[Open]`** (`mccorvie/riemann-masullo` Wave 2 is recomputing `§B.4` local normalizations; `#587` reports a $\mu_1(C_F^1)$ discrepancy on $\mathbb Q(i), \mathbb Q(\sqrt{-3})$). |
| **M5. Unwritten Chapter 13 (deducing GRH and central-zero behavior)** | `Chapter 13` (`pp. 521–522`, `Thm. 13.3.1.2` fn. 2 *"Insert statement"*) | **Unwritten in manuscript `[Paper]` / `[Open]`** (Loeffler formalized RH $\Leftarrow$ `Thm. 12.5.1.1` `[Community]`, so all substantive weight sits in M1–M4!). |

---

## 16.4 Conditional consequences: what DOES and DOES NOT follow if `EveryCharacter` stands

Suppose the remaining single-threaded `lake comparator` runs finish with zero surprises and
`EveryCharacter` (`src/Main.lean:8`) stands as a theorem of mathematics. Because mathematical accuracy
requires knowing **exact logical boundaries**, Proposition 16.1 separates classical conditional results
that **become unconditional immediately** from famous conjectures and conditional theorems that **remain
open**!

**Proposition 16.1 (Logical boundary of `EveryCharacter`: Dirichlet GRH versus ERH, Artin GRH, automorphic GRH, and GSH).**
*Assume `UpperTheory.EveryCharacter` (`src/Main.lean:8`): for every $N \ge 1$ and every Dirichlet
character $\chi \bmod N$, $L(s, \chi) \neq 0$ on $\Re s > \frac{1}{2}$ (except $\chi = 1, s = 1$).
Then:*

1. **Statements that DO follow unconditionally (`[Expository]` / `[Community]`):**
   - **Classical Riemann Hypothesis (`src/Main.lean:4, 6`) and elementary equivalences:** $\psi(x) = x + O(x^{1/2}(\log x)^2)$
     `[Davenport2000]`, $\pi(x) = \operatorname{li}(x) + O(x^{1/2}\log x)$, Merten's sum $M(x) = \sum_{n \le x}\mu(n) = O_\varepsilon(x^{1/2+\varepsilon})$,
     and Robin's and Lagarias's divisor-sum inequalities `[Lagarias2002]` (already machine-checked in
     `ArithSolution.lean` via `kimihiro64/Robin1984` `[Community]`)!
   - **Primes in arithmetic progressions (`[Davenport2000]`, Ch. 20):** For every modulus $q \ge 1$ and
     $\gcd(a, q) = 1$, $\psi(x; q, a) = \frac{x}{\varphi(q)} + O\bigl(x^{1/2}(\log(qx))^2\bigr)$,
     eliminating **Siegel zeros** (`[Siegel1935]`) for all Dirichlet characters over $\mathbb Q$ and
     improving Linnik's least-prime bound to $p_{\min}(q, a) \ll (\varphi(q)\log q)^2$!
   - **Goldbach-type and sieve consequences depending only on Dirichlet GRH:** Deshouillers–Effinger–te
     Riele–Zinoviev's 1997 theorem that every odd integer $n > 5$ is a sum of three primes (already
     proved unconditionally by Helfgott in 2013, now given an independent short proof via Dirichlet GRH!),
     sharp Bombieri–Vinogradov-range error bounds on individual moduli $q \le x^{1-\varepsilon}$, and
     deterministic polynomial-time primality/factoring-adjacent algorithms that test quadratic/power
     nonresidues over $\mathbb Q$ via **Dirichlet** characters (e.g., Miller's deterministic primality
     bound $O((\log n)^4)$ for testing witnesses against quadratic/Dirichlet characters mod $n$).
   - **Abelian Dedekind zeta functions:** RH holds for $\zeta_K(s)$ whenever $\operatorname{Gal}(K/\mathbb Q)$
     is **abelian** (Section 16.2.1, Step 1, via Kronecker–Weber).
2. **Statements that DO NOT follow from `EveryCharacter` and remain `[Open]` (`[Expository]`):**
   - **Extended Riemann Hypothesis (ERH) for non-abelian number fields $K / \mathbb Q$:** RH for
     $\zeta_K(s)$ when $K$ is not contained in any cyclotomic field $\mathbb Q(\zeta_N)$ (e.g.
     $K = \mathbb Q(\sqrt[3]{2})$ or degree-$5$ non-solvable fields; Section 16.2.1, Steps 2–3), along
     with Bach's general $O((\log \lvert \Delta_K \rvert)^2)$ class-group generator bound for arbitrary
     number fields $K$!
   - **Unitary Hecke $L$-functions $L_F(s, \chi)$ over number fields $[F : \mathbb Q] > 1$** (`[Hecke1920]`),
     including CM Grossencharacters over imaginary quadratic fields.
   - **Non-abelian Artin $L$-functions $L(s, \rho)$ (`[Artin1924]`, `[Brauer1947]`) and Artin's primitive
     root conjecture (`[Hooley1967]`):** Hooley's theorem that every non-square integer $a \neq -1$ is a
     primitive root modulo infinitely many primes requires ERH for the **non-abelian Kummer fields
     $\mathbb Q(\zeta_q, a^{1/q})$** ($q$ prime), which are **not** abelian over $\mathbb Q$ and
     therefore **remain conditional**!
   - **Automorphic / elliptic-curve / modular-form GRH ($\mathrm{GL}_2$ and $\mathrm{GL}_n$, $n \ge 2$):**
     GRH for Ramanujan's $\Delta$-function $L(s, \Delta)$, holomorphic newforms $L(s, f)$, Maass forms,
     and elliptic curves $L(E, s)$ over $\mathbb Q$ (nor the Birch and Swinnerton-Dyer conjecture!).
   - **Simplicity of zeros, Montgomery's Pair Correlation Conjecture, and the Grand Simplicity Hypothesis (GSH):**
     None of the five theorems in `src/Main.lean` says anything about the **multiplicity** $N(\rho)$ of
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
     statement of `Theorem 5.2.1.1` (`p. 230`) holds in Lean `v4.36.0` and help recompute the exact
     measure normalizations of `Theorem B.4.4.7` (`p. 623`, issue `#587`).
2. **For algebraic number theorists, Iwasawa theorists, and arithmetic geometers:**
   - *Audit the ~70 remaining `GlobalTheory.Published.*` declarations (`P18`, Chapters 13 and 18):* Following
     the five-step protocol and 14 worked exemplars of **Chapter 18**, pick one
     unaudited file under `src/Development/AbelianVarietyTheory/PublishedTheorems/` or
     `src/Development/AutomorphicSpectrum/PublishedTheorems/`, read its Lean `def` (typically 20–60 lines!), and
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
   - *Settle Question M1/M4 on Masullo's strip spaces $W_{[-\alpha, \alpha]}^{s,2}\mathcal H_F$:* Either
     construct an explicit rigorous counterexample showing that the geometric kernel trace on
     $W_{[-\alpha, \alpha]}^{s,2}\mathcal H_F$ changes by off-strip zero residues when $\alpha$ varies
     (for a Beurling / off-line model $L$-function), or determine whether a nuclear trace formula on
     positive-width strips $I = [-\alpha, \alpha]$ can be proved and matched to `§12.5` without circularly
     assuming zero-freeness outside $\frac{1}{2} + I$!
5. **For readers of this book (`Li-Hongmin/amazing-riemann-hypothesis`):**
   - Every `src/…:line` citation, status tag, and mathematical proof in Chapters 0–18 is maintained in
     the public repository. If you read a deeper sub-cone at level `R3`, spot an imprecision, or resolve
     an `[Open]` item in Ledgers 1–4 above, open an issue or pull request with the exact `file:line` or
     page number so the public record stays sharp, honest, and reproducible.

---

**Summary of the chapter.** As of `2026-11-22 04:35 UTC`, Alpöge and Claude's five
`src/Main.lean` theorems (`RiemannHypothesis` and Dirichlet GRH over $\mathbb Q$) have been reproduced
byte-for-byte in an isolated sandbox (`61,570,595,788` bytes, sha256 `5ea74b91…244e`) and accepted by
`leanchecker`, `lean4lean`, `nanoda`, `con-leche --compare`, and `con-ron --compare` using only Lean's
three standard axioms `[Community]`, while standalone `Robin1984` has passed full `lake comparator`
(`v4.36.0`) and the single-threaded `lake comparator` Lean kernel stages on the 62 GB main and combined
exports remain in progress `[Open]`. Across Chapters 1–13 and 17–18 of this textbook, we have translated
the top-to-bottom architecture (`P0`–`P18`) into human graduate mathematics — reading the statement layer,
analytic endgame, Behrend sphere and `HostOfField` thick-frame engine (Chapter 17), Arakelov Bost-slope
library, formal chain brackets, inert-prime valuation algebra, GMA congruence-to-$\mathrm{Ш}^1$ reductions,
Iwasawa squeeze, top-level Langlands/Galois/Green interfaces, and 14 representative `Published` theorem
statements (Chapter 18) line by line (`[Lean, read]`) while demarcating the ~146,000-module deep proof
cones and ~70 unaudited `GlobalTheory.Published.*` names that await human specialists (`[Open]`). In
parallel (Chapters 14–15), we analyzed Masullo's 940-page adelic trace-formula draft `[Paper]`,
pinpointing why its strip-weighted Hardy–Sobolev strategy stalls at the Chapter 10 biorthogonal-bound
failure (`pp. 444, 451, 463`), omitted `§12.3` (`p. 514`), and unwritten Chapter 13 (`pp. 521–522`)
`[Open]`, and showed by explicit Artin/Brauer examples why Dirichlet GRH (`EveryCharacter`), even if
completely confirmed, leaves non-abelian ERH, Artin's primitive root conjecture, $\mathrm{GL}_2$
automorphic GRH, and simplicity of zeros open. Turn next to **Chapter 18** for our worked `R3`
statement-fidelity casebook on `GlobalTheory.Published.*`.
