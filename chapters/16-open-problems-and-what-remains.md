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
   carefully distinguishing that `Prop` definition (`∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art`,
   `:72`, with the structure `IsGlobalArtin` at `:25–39`) from the 17-line proof-term wrapper file
   `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8–15`
   (`globalArtinReciprocity`, `rayClassFieldSt`, `heckeLAdicCharacter`) [Lean, read]!
2. **Check quantifiers against the published theorem.** In
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:7–11`,
   every prime $\ell$ and abelian number field $K/\mathbb Q$ containing a primitive root of unity
   of order $4$ if $\ell=2$ and of order $\ell$ otherwise
   (`(∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l)) →`, `:9`) admit a uniform bound
   $\ell^r$ on $|\mathrm{Cl}(\mathcal O_{K'})/\mathrm{Cl}(\mathcal O_{K'})^\ell|$
   at all $\ell$-power cyclotomic levels $K'$. This is the bounded $\ell$-rank consequence
   of [FerreroWashington1979]. The premise is part of the statement; the archive's proof
   introduces it with `intro l _ K _ _ _ _` and does not use it
   (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104–106`). [Lean]
   Meanwhile, in `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70–72` (consumed at
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:45`
   in Chapter 10), `IsGlobalArtin` states the full idèlic Artin reciprocity theorem over **every**
   number field $E$ (*Faithful* `[Lean, read]`), while `RayClassFieldSt` and `HeckeLAdicCharacter` are
   separate companion `Prop`s (`src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:17` and `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:74`;
   all three audited in full in **Chapter 18**, Section 18.2)!
3. **Verify non-vacuity and off-center guards:** Check that no hypothesis in the `Prop` is unsatisfiable or
   silently omits a required condition (for example, in `UpperTheory.V.Published.Kato`,
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/QuotRepMk.lean:65`,
   Ishaan Dixit asked on Zulip `#642435200` whether omitting $L(f, \chi, r) \neq 0$ made the statement
   stronger than `[Kato2004]`; David Loeffler pointed out at `#642442900` `[Community]`, and we verify
   in **Chapter 18**, §18.3.4 [Expository], that the guard `2 * r ≠ k` keeps every
   integer $1 \le r \le k - 1$ at distance $\ge \frac{1}{2}$ from $\frac{k}{2}$, where Euler-product
   non-vanishing, boundary non-vanishing, and the functional equation force $L(f, \chi, r) \neq 0$ automatically!).
4. **Assign two separate tags:** Even when an internal `Prop` turns out to be a domain-restricted
   special case (as LUMI `docs/07-named-theorems.md` found for 29 of 105 audited items `[Community]`,
   and as Chapter 18 verifies for `BaseChangeDefiniteUnitary`, `PoitouTateNormalised`, and `ClozelPurity`
   `[Lean, read]`),
   the implication inside `src/Main.lean` remains 100% kernel-valid (`[Lean]`), while only *Faithful*
   statements qualify for standalone reuse as Mathlib theorems under their classical names!

---

<a id="163-consolidated-verification-ledgers-2026-11-22-0435-utc"></a>

## 16.3 Consolidated verification ledgers (22–28 November 2026)

The publication settlement covers the public chapter changes between the 22 November release and 28 November 2026. Local R3 records the proof bodies named in each linked section. Open inputs inherit the reading boundary given there. The archived module counts are import-cone counts, so they do not decrease when a local proof is read.

### 16.3.1 Ledger 1: Machine compilation, sandbox isolation, and independent proof kernels (Alpöge archive)

| Verification item | Tool / runner | Status through 28 November 2026 | Exact scope & evidence |
|---|---|---|---|
| Archive byte integrity | Sutherland, LUMI, `leanprover-community`, this book | **Passed** `[Lean, read]` / `[Community]` | 14 parts join to `239,275,554` bytes, sha256 `9631b4f0…49c7fc`; 175,187 `.lean` files, `17,374,215` lines. |
| Statement & Mathlib pin | `src/Statements.lean`, `Challenge.lean`, Chapter 1 | **Passed** `[Lean, read]` / `[Community]` | All 5 theorems in `src/Main.lean` use unmodified Mathlib `v4.33.1` (`0df444a3`); PR #34 proved machine equivalence with `formal-conjectures` Dirichlet GRH. |
| Axiom & static metaprogramming audit | `#print axioms`, `NOTES.md`, LUMI, our `rhaudit` (`186,200` `.olean` stream) | **Passed** `[Lean, read]` / `[Community]` | Only `propext`, `Classical.choice`, `Quot.sound`; zero `sorryAx`, zero `Lean.ofReduceBool`/`native_decide`, zero CShorcuts; 4 custom tactics elaborate to standard kernel terms. |
| No-network sandboxed `lake build` + export match | LUMI (8 nodes), Sonoda (RIKYU), Sutherland (bubblewrap) | **Passed** `[Community]` | Sutherland's sandboxed `lake build Main` (`18:07 UTC` 21 Nov) produced a **byte-identical** `61,570,595,788`-byte export (`5ea74b91…244e`, `19:32 UTC` 21 Nov; also matched by Dixit). |
| Module-by-module native & Lean-in-Lean replay | `leanchecker` (`v4.33.1`) & `lean4lean` (`67f63b0c`) | **Passed** `[Community]` | `175,187 / 175,187` `.olean` modules accepted (`lean4lean` passed 175,182 at default fuel + 5 `decide +kernel` modules with raised fuel). |
| Independent Rust kernel on full export | `nanoda_bin` | **Passed** `[Community]` | `exit 0` in 27m42s on 80 threads (`Sutherland`), plus independent runs by `Infatoshi` and `nasqret`. |
| Verified statement-and-kernel comparators | `con-leche --compare` (`5dc36dc1`) & Rust port `con-ron --compare` (`3f22699b`) | **Passed** `[Community]` | Both accepted all `1,468,418` solution + `51,692` challenge declarations in `--verified` mode and confirmed all 5 theorems (`con-ron` `exit 0` at `23:02 UTC` 21 Nov in 7m06s on 64 threads), plus both `Robin1984` divisor-sum inequalities! |
| Additional community export checkers | `con-agua`, `Pestka`, `Gruszka`, `nanoclo`, `tenet` | **Passed (reported)** `[Community]` | Reported accepting `solution.ndjson` by Teżewski on Lean Zulip. |
| Import-tree dead-file pruning | `leanprover-community/riemann-hypothesis` (PRs `#8, #45, #57, #60, #64`) | **22 November snapshot** `[Community]` | `10,724` unused `.lean` files pruned from `Main`'s import tree so far (`164,464` remaining; Shore/LUMI measured `146,287`–`146,437` used). |
| Single-threaded Lean default and paranoid kernels on the full export | `leanchecker` v4.36.0 | **Passed** `[Community]` | On Sutherland’s V1 stream, the stock default kernel exited 0 at 18:44:18 UTC on 22 November and the stock paranoid kernel at 19:01:08 UTC on 23 November. The tuned runs also passed. [V1 logs](https://math.mit.edu/~drew/grh/) |
| End-to-end Comparator | Standalone v4.33.0 and `lake comparator` v4.36.0 | **Passed** `[Community]` | V4.33.0 exited 0 on 23 November with the local `Challenge.lean` build and prebuilt solution. V4.36.0 used the canonical challenge export, checked statements and axioms, and accepted all five headline theorems through the paranoid, nanoda and default kernels at 21:49:00 UTC on 25 November. [V1 results and logs](https://math.mit.edu/~drew/grh/) |
| Main-theorem export dependency path | DeDeo export (V8), Chapter 16 | **Path found** `[Community-data, checked by us]` | The recorded 19-declaration path from `riemannHypothesis` reaches `exists_lt_of_stage` and `exists_divStage`. The witness-to-`WordFacts` field transport remains [Open]. [§16.6.4](#1664-the-tautology-argument-of-the-final-version-paper-nielsen-89) · [V8](../sources/SOURCES.md#v8) |

### 16.3.2 Ledger 2: Human reading depth (`R3` vs `[Open]`) across nodes `P0`–`P18`

The 22 November reading of the analytic endgame and the top-level assembly supplies the baseline below. The November publications extend local proof-body reading where their individual sections mark R3. This includes Mathlib suppliers and conditional proofs with their stated hypotheses. The linked section evidence gives the exact scope.

| Node | Block | Proof bodies read at R3 and new local readings | Deepest named unread inputs | Historical import-cone size |
|---|---|---|---|---|
| <a id="ledger-2-p0-p1-p3"></a>`P0`–`P1`, `P3` | Statement, theta, Gauss and primitive-character reductions | `src/Main.lean`, `src/Statements.lean`, `ClaimStrip.lean`, `RhOfRight.lean`, `CritLine.lean`, `Imprimitive.lean`. The new readings cover the pinned theta and Gauss suppliers, conductor descent, the Gamma/Beta integral and its domination and Bochner extension, and the Möbius multiplication fibres. The rational trace and unit-ball constructions are credited at the scope of their own chapter readings. [Section evidence](#publication-evidence-ledger-2-p0-p1-p3) | The original top-level reduction cone stays closed at its stated scope. Imported analytic results beyond the named pinned suppliers keep their local section-level status. | `0`–`10` |
| <a id="ledger-2-p4-p6"></a>`P4`–`P6` | Landau windows and square-root barrier | `LandauTheorems/`, `PrimitiveCosets/`, `LipschitzWeightAndMinimum.lean`, `TopWin.lean`, `ZeroFreeAllOfTopG.lean`. The analytic supply now reaches the local Cauchy/residue proofs, tagged-box comparison and gauges, interval measure and endpoint FTC. The finite-field and finite-étale reading reaches splitting, embeddings and tensor norm transport through the specified local norm and cyclotomic consumers. Crossley's delayed difference is a community example. [Section evidence](#publication-evidence-ledger-2-p4-p6) | The upstream production of TopG and ChainTied and the named inputs to the local tensor comparisons remain open where marked. | `9`–`753` |
| <a id="ledger-2-p7"></a>`P7` | Stepanov and chain size | Clause 7's main-path slope and signature data, pointwise detorsion, finite adelic norm lifting, crystalline Gauss seminorm and first-torsion test, and the common-record inertia polynomial receive the local readings linked below. [Section evidence](#publication-evidence-ledger-2-p7) | Host Gram and metric production and the antecedent period structures stay at their section-level boundaries. | Historical size not recomputed |
| <a id="ledger-2-p8"></a>`P8` | Inert-prime divisibility | `WeilJacquetShalikaLaw` (all 633 lines), `DataDIVDefs`, `DataParams₂`, `JointServices`, `GServT`, `DIVRecBridgeSel` (`R3`). Local R3 follows the positive Hecke and jet bounds, the restS and beta chains, LemmaOne and LemmaTwo, Dwork, the Witt norm/Frobenius model and log-law proofs, and the scalar and division-level supply at the stated domains. [Section evidence](#publication-evidence-ledger-2-p8) | The generic sharp row bounds, ea_BrClass, the named expIntegral wrapper, and analytic Lubin–Tate evaluation/reciprocity remain open where cited. | `321` / `4,699` |
| <a id="ledger-2-p9"></a>`P9` | Arakelov slopes and heights | The existing R3 reading covers `LatticeSlopes`, `HarderNarasimhan`, `DivisionHeightBoundStatement` and `GlobalBoundRefinements`. The new compact and formal-degree supply in Chapter 9 is recorded on the P10 row. [Chapter 9 slope inequalities](09-heights-slopes-and-near-orthogonality.md#951-a-reusable-mathlib-grade-gem-inside-the-archive-latticeslopes-and-hardernarasimhan) | The minor HermitianLatticesTheory helpers remain outside the recorded reading. | `1`–`763` |
| <a id="ledger-2-p10"></a>`P10` | Period gains and Gram decay | `StatementFrame` (`FrameHerm`), `GlobalTheoremInputs`, `TieGlobal`, and top wrappers `LinkG`, `LinkAltAltBis`, `LinkGl`, `Link` (`R3`). Local R3 follows polar Haar and formal degree where marked, the compact models, Pieri, Weyl and PRV/Dirac supply, coordinate densities, the tensor sandwich the weighted PsiM bound, and the compact-finite recovery at the stated cutoff. [Section evidence](#publication-evidence-ledger-2-p10) | Deep Chowla–Selberg, Siegel-mass, Rallis and Gram-matrix production outside the cited bodies stays open. | `306`–`15,578` |
| <a id="ledger-2-p11"></a>`P11` | Congruences to Sha | `IdempotentChoiceDepthZero`, `CutDetOrd.main`, `CutCoreUnit.main`, `IntegralHeckeForms`, `twist_kills_selmer`, `LinkFam.main`, `divinN_of_hypV` (`R3`). The lattice and adjugate reading reaches start_of_resBound, scalar descent, rational and finite Bloch–Kato compatibility, the fixed divisible target for annihilator detection, finite descent and compatible integral primitives. Later sections read the common corank, span, residual dimensions and length comparisons. [Section evidence](#publication-evidence-ledger-2-p11) | Global twisting-character existence and the deeper patching and determinant producers outside the cited proof bodies remain open. | `207`–`3,287` |
| <a id="ledger-2-p12"></a>`P12` | Window bound VWin | `ExistsPageN`, `IsChiField`, `LengthEqAddEigen` (`vvle_of_parts`), `CMFieldExponentialBounds/`, `HeightAndVanishing/`, Sinnott/Ferrero–Washington spine, `KatoUse`, `TaylorWilesObstructionBound`, `TopMainZj`, `VwinOfRow` (`R3`). The Sinnott, Kummer, norm and idelic suppliers are read at their cited calls. Local R3 reaches finite local Herbrand, Hilbert 90, all-integer Tate comparison and the finite cup and subgroup dévissage bodies where marked. The three local class-formation and Artin evaluation readings appear in §§11.4.3.16–18. [Section evidence](#publication-evidence-ledger-2-p12) | Deeper arithmetic invariant and Brauer proofs at the named inputs and the Euler-system, Picard modular surface and patching cones remain open. | **`157,603`** |
| <a id="ledger-2-p13"></a>`P13` | Auxiliary pairs and host primes | `PairGood`, `pairEx`, `StagePow`, `twistK`, `meanSqK`, `BadShare`, `WinPairs`, `SupplyChi`, `IsChiField` (`R3`). Local R3 reaches the Mellin and local contour chain, logarithmic derivatives, zero separation and the conditional Siegel product, elementary prime and squarefree counts, Jordan's two finite-group steps, and the top-place, ray-class and ideal arithmetic supply. Chapter 19 reads the local finite frame and host supply at the named consumers. [Section evidence](#publication-evidence-ledger-2-p13) | The full zero-density and progression input proofs, the remaining exceptional-zero constants, and the deeper host/global supply outside the cited bodies remain open. | `260`–`1,329` |
| <a id="ledger-2-p14"></a>`P14` | CM Galois representations | `WeightsConjBis` (`Row0b`, `PropsB`), `RecT`, `WeakOfAtt`, `RowSrc`, `GaloisRepresentationsOfThetaLift`, `WeightOneGeometricRealization`, `TLiftK` (`R3`). Local R3 extends to the finite-étale and Lefschetz chart bodies, the reduced fibre and Čech comparison at the cited scope, the denominator-change proof and the parameter-preserving holomorphic section. The classical Sard argument has its own exposition. [Section evidence](#publication-evidence-ledger-2-p14) | The archive's underlying Sard proof and deep Shimura cohomology, p-adic Hodge compatibility and congruence limits retain their named boundaries. | `3,150`–`66,167` |
| <a id="ledger-2-p15"></a>`P15` | Partial local Langlands | `IsRecTOfIsRec` (`LawsT`, `RecTExists`) and `LocalCentralUnits/RecTExists` (`R3`). Local R3 extends to the compact-open fixed space and contragredient, twisted Jacquet detection and conductor-ball pairing, and the ordered segment, shuffle and adjacent-pair bodies where specified. [Section evidence](#publication-evidence-ledger-2-p15) | The supercuspidal and deeper adjacent reducibility and multisegment suppliers beyond those bodies remain open. | `1,063` / `26,672` |
| <a id="ledger-2-p16"></a>`P16` | Green characters | `LabelDatum`, `GreenRegularCharacters` header, `SumRangeEqRoots` (`green_of_regular`), `TopShape` (`R3`). The cited direct proofs now reach existence of the regular cuspidal character, label and uniqueness supply, central-idempotent and Mackey orthogonality, radical sums and the mirabolic degree chain, and the finite Whittaker-cell producers. [Section evidence](#publication-evidence-ledger-2-p16) | Deeper Green shape transport, remaining series-uniqueness inputs and the literature comparison retain the individual section boundaries. | `200` / `16,990` |
| <a id="ledger-2-p17"></a>`P17` | Theta-lift chain families | `Hyps`, `SiegelEisensteinSecondTermHypotheses`, `WeilTensorModels`, `LiftLambdaBound`, kernel Fubini/chain-rule files, `TopPlug` (`R3`). Local R3 reaches the mirabolic restriction and quotient producers, parabolic product derivative bounds, compact integration, positivity, complements and the lower-derivative spectral bound. [Section evidence](#publication-evidence-ledger-2-p17) | The deep regularized Siegel–Weil and Howe-duality cones remain open. | `14,732`–`112,384` |
| <a id="ledger-2-p2-p18"></a>`P2`, `P18` | Literature layer and assembly | `MainConclusion`, `OpenLiteratureStatements`, `GlobalArtinReciprocity`, `OpenImageCondition`, `every_character_of_literature_of_vWin` (`R3`). The named Selmer and local Tate transport bodies, compact-support sequence, trace, Sha and fixed-exponent assembly, and the absolute theta, doubling, split and Rallis bridge bodies receive local reading at the cited calls. See Ledger 3 for the statement comparisons. [Section evidence](#publication-evidence-ledger-2-p2-p18) | The untouched literature proof bodies, the continuation cone and its pole clause, the local normalizations and the remaining statement-fidelity inventory stay open at the cited scope. | `151,285` |
| <a id="ledger-2-masullo-foundations"></a>`Masullo foundations` | Functional analysis and Haar supplies | The pinned Fourier, density, exponential, spectral and Haar supplies are read at their cited local proof bodies. Book arguments carry their exposition labels. [Section evidence](#publication-evidence-ledger-2-masullo-foundations) | Positive-width strip spectral nuclearity and the global-to-local and smoothing inputs retain the status in Ledger 4. | Auxiliary route |

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
  `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`, alongside unreferenced fossil declarations outside
  `src/Main.lean`'s closure).
- **Audited so far (`LUMI docs/07-named-theorems.md` `[Community]` + Chapters 11, 13, and 18 `[Lean, read]`):**
  `105` statements audited at AI-assisted community level (`65` faithful, `29` domain-restricted special
  cases such as rank-$2$ `MorelSuh` or curve/surface `KawamataViehweg`, `7` safe weakenings, `4`
  undetermined), **plus source comparisons in Chapters 13 and 18**
  (`GreenRegularCharacters`, `GlobalArtinReciprocity`, `HeckeLAdicCharacter`,
  `RayClassFieldSt`/`RayClassFieldMaximalSt`, `ChebotarevDegreeOne`, `FerreroWashington`,
  `SiegelKlingen`/`DeligneRibet`/`SiegelKlingenDeligneRibet`, `Kato`/`KatoUse`,
  `PoitouTateNormalised`/`PoitouTateDuality`, `ClozelPurity`/`RegularAlgebraicPurity`,
  `BaseChangeDefiniteUnitary`/`BaseChangeIsobaric`, `WeilSiegelFormula`/`WeilSiegelFormulaUnitary`/`SiegelWeilUnitaryConvergent`,
  and `DeRhamPotSemistable`).
- **Errata to the first case studies.** The same-source review `ssaudit-rhbook-ch17-18-1122d-11221700-11222118` (partial acceptance) identified incorrect signatures, host conditions and page references. Chapters 14, 17 and 18 record the corrections. The corrected Ferrero–Washington, Deligne–Ribet and Kato interfaces carry [Lean].
- **Second round of errata.** The audit `audit-rhbook-errata-ch16-18-and-p18-batch2-1123a-11231148-11231224` (partial acceptance) found that the first round had dropped the root-of-unity premise of `FerreroWashington`, left non-existent identifiers and a wrong quantifier order in the class-field definitions of Chapter 18, described the `NormOne` level primes of Chapter 17 as norm-one elements, and shifted several page and line references. Chapters 15–18 and `notes/squeeze-trace.md` now follow the Lean source and Masullo's PDF at those places.
- **Second batch.** Chapter 19 compares six named interfaces and traces where the main path uses them. `ShinGaloisRep` and `ChenevierHarris` are defined but never used by a proof term, and the literature bundles carry `DoublingMethod` only as `ResidueKilled.DM`, without its pole clause. Its [Lean, read] tags apply to the specific producer, consumer and local-deduction lines cited there. Full upstream proofs and exact literature normalizations remain [Open] where marked.
- <a id="ledger-3-local-bridges"></a>**Local production and transport.** Chapter 18 §§18.3.5–26 trace the Selmer exact sequence, the local Tate and normalization interfaces, the nine-term and Sha transports, and the compact-support sequence and finite-coefficient assembly. These are local proof-body readings and conditional comparisons at the scope marked in each section. [Section evidence](#publication-evidence-ledger-2-p2-p18)
- <a id="ledger-3-doubling"></a>**Chapter 19 reachability and fidelity.** The single-root V8 query reaches `ResidueKilled.DM` and `dm_of_two`. The full `DoublingMethod` and its pole clause are outside that query. The real-place continuation and the exact Lapid–Rallis split-place normalization retain the stated open boundaries. [§19.4](19-published-layer-case-studies-ii.md#194-global-doubling) · [§19.5](19-published-layer-case-studies-ii.md#195-unramified-split-doubling) · [§19.6](19-published-layer-case-studies-ii.md#196-convergent-rallis-inner-product)
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

### 16.3.5 Publication evidence for the reading ledger

Each row links the sections that document its new local proof-body readings, exposition, or retained interfaces. The [source map](../sources/SOURCES.md#november-23-28-publication-source-map) and [contribution register](../CONTRIBUTIONS.md#november-23-28-publication-attribution) give the corresponding records.

<a id="publication-evidence-ledger-2-p0-p1-p3"></a>

- **Chapter 1.** [§1.2.2.1](01-statement-and-fidelity.md#1221-how-the-theta-integral-produces-the-even-hurwitz-pole) · [§1.2.2.2](01-statement-and-fidelity.md#1222-removing-the-gamma-factor-at-zero-and-at-one) · [§1.2.2.3](01-statement-and-fidelity.md#1223-the-laurent-constant-at-one-harmonic-sums-the-integral-error-and-the-stored-value) · [§1.2.2.4](01-statement-and-fidelity.md#1224-the-derivative-of-gamma-at-one-half-duplication-log-convexity-and-the-deligne-factor) · [§1.2.2.5](01-statement-and-fidelity.md#1225-log-convexity-the-bohrmollerup-theorem-and-the-duplication-formula) · [§1.2.2.6](01-statement-and-fidelity.md#1226-from-the-theta-transformation-to-the-completed-hurwitz-functional-equation) · [§1.2.2.7](01-statement-and-fidelity.md#1227-from-poisson-summation-to-theta-inversion) · [§1.2.2.8](01-statement-and-fidelity.md#1228-hilbert-expansion-and-the-norm-behind-poisson-summation) · [§1.2.2.9](01-statement-and-fidelity.md#1229-unordered-summation-finite-tail-cauchy-criteria-and-banach-completeness) · [§1.2.2.10](01-statement-and-fidelity.md#12210-rational-cauchy-completion-dedekind-suprema-and-realinstcompletespace) · [§1.2.2.11](01-statement-and-fidelity.md#12211-nonnegative-extended-sums-and-finite-majorants) · [§1.2.2.12](01-statement-and-fidelity.md#12212-nonnegative-product-sums-and-the-finite-dimensional-theta-majorant) · [§1.2.2.13](01-statement-and-fidelity.md#12213-from-a-rational-trace-form-to-gaussian-summability) · [§1.2.2.14](01-statement-and-fidelity.md#12214-from-a-rational-hermitian-trace-form-to-a-euclidean-lattice) · [§1.3.2](01-statement-and-fidelity.md#132-from-the-finite-hurwitz-sum-to-the-classical-dirichlet-l-function) · [§1.3.2.1](01-statement-and-fidelity.md#1321-the-odd-hurwitz-part-and-its-mellin-transform) · [§1.3.2.2](01-statement-and-fidelity.md#1322-producing-odd-theta-inversion-and-primitive-fourier-shifts) · [§1.3.2.3](01-statement-and-fidelity.md#1323-conductor-descent-nonunit-gauss-vanishing-and-the-imprimitive-bridge). [Source map](../sources/SOURCES.md#publication-sources-chapter-1)
- **Chapter 2.** [§2.3.2.1](02-functional-equations-and-primitive-characters.md#2321-why-gamma-has-no-zeros-in-the-right-half-plane) · [§2.3.2.2](02-functional-equations-and-primitive-characters.md#2322-the-beta-integral-and-the-gamma-product-total-scale-and-proportion-coordinates) · [§2.3.2.3](02-functional-equations-and-primitive-characters.md#2323-eulers-integral-for-gamma-convergence-at-both-ends-and-what-gamma_eq_integral-actually-proves) · [§2.3.2.4](02-functional-equations-and-primitive-characters.md#2324-nonnegative-derivatives-and-improper-integrals-the-integrability-criteria-behind-both-ends-of-eulers-integral) · [§2.3.2.5](02-functional-equations-and-primitive-characters.md#2325-the-vitalicarath%C3%A9odory-majorant-lower-semicontinuous-upper-bounds-for-integrable-functions-and-what-the-one-sided-fundamental-theorem-takes-from-them) · [§2.3.2.6](02-functional-equations-and-primitive-characters.md#2326-monotone-convergence-on-truncation-domains-the-lower-integral-theorem-behind-lemma-c-and-the-signed-limits-at-both-ends-of-eulers-integral) · [§2.3.2.7](02-functional-equations-and-primitive-characters.md#2327-dominated-convergence-through-the-l1-extension-the-filter-to-sequence-reduction-the-decreasing-tail-supremum-step-and-local-uniform-domination-of-the-complex-gamma-kernel) · [§2.3.2.7.1](02-functional-equations-and-primitive-characters.md#banach-dense-extension) · [§2.3.2.7.4](02-functional-equations-and-primitive-characters.md#integral-holder-normalization) · [§2.3.2.7.5](02-functional-equations-and-primitive-characters.md#finite-weighted-holder) · [§2.3.2.7.6](02-functional-equations-and-primitive-characters.md#holder-lp-product) · [§2.3.2.8](02-functional-equations-and-primitive-characters.md#metric-valued-ae-limits) · [§2.3.4](02-functional-equations-and-primitive-characters.md#234-measurable-fundamental-domains-for-discrete-quotients) · [§2.3.5](02-functional-equations-and-primitive-characters.md#235-why-the-adelic-unitary-group-is-locally-compact-and-second-countable) · [§2.3.5.1](02-functional-equations-and-primitive-characters.md#2351-finite-residue-fields-and-compact-unit-balls) · [§2.6.3](02-functional-equations-and-primitive-characters.md#263-the-m%C3%B6bius-inverse-on-the-open-half-plane) · [§2.6.3.1](02-functional-equations-and-primitive-characters.md#2631-regrouping-an-absolutely-convergent-product-by-multiplication). [Source map](../sources/SOURCES.md#publication-sources-chapter-2)

<a id="publication-evidence-ledger-2-p4-p6"></a>

- **Chapter 3.** [Why a zero contributes its order to the residue](03-landau-window-criterion.md#why-a-zero-contributes-its-order-to-the-residue) · [Why a nonzero analytic germ has a first nonzero coefficient](03-landau-window-criterion.md#why-a-nonzero-analytic-germ-has-a-first-nonzero-coefficient) · [From complex differentiability to a power series](03-landau-window-criterion.md#from-complex-differentiability-to-a-power-series) · [Weighted circle integrals and the rectangle theorem](03-landau-window-criterion.md#weighted-circle-integrals-and-the-rectangle-theorem) · [Rectangular divergence with countable exceptions](03-landau-window-criterion.md#rectangular-divergence-with-countable-exceptions) · [Fubini and the box comparison on a rectangle](03-landau-window-criterion.md#fubini-and-the-box-comparison-on-a-rectangle) · [The Henstock–Sacks inequality: tagged sums over part of a rectangle](03-landau-window-criterion.md#the-henstocksacks-inequality-tagged-sums-over-part-of-a-rectangle) · [Cousin's lemma: fine tagged partitions of a box](03-landau-window-criterion.md#cousins-lemma-fine-tagged-partitions-of-a-box) · [Exact complements by splitting half-open boxes](03-landau-window-criterion.md#exact-complements-by-splitting-half-open-boxes) · [Subbox filters and the Cauchy net of tagged sums](03-landau-window-criterion.md#subbox-filters-and-the-cauchy-net-of-tagged-sums) · [From the box filter to epsilon and gauges](03-landau-window-criterion.md#from-the-box-filter-to-epsilon-and-gauges) · [Where interval lengths in real Lebesgue measure come from](03-landau-window-criterion.md#where-interval-lengths-in-real-lebesgue-measure-come-from) · [How rational open intervals determine a real Borel measure](03-landau-window-criterion.md#how-rational-open-intervals-determine-a-real-borel-measure) · [Completing a Borel measure and transporting integrals](03-landau-window-criterion.md#completing-a-borel-measure-and-transporting-integrals) · [From a finite filter to an integrable endpoint neighborhood](03-landau-window-criterion.md#from-a-finite-filter-to-an-integrable-endpoint-neighborhood) · [Differentiating an oriented interval integral at its right endpoint](03-landau-window-criterion.md#differentiating-an-oriented-interval-integral-at-its-right-endpoint) · [A normalized holomorphic logarithm on a zero-free disk](03-landau-window-criterion.md#a-normalized-holomorphic-logarithm-on-a-zero-free-disk) · [§3.4.5](03-landau-window-criterion.md#345-the-landau-window-criterion-landau_window-lemmal-zerofree_of_rpow_window). [Source map](../sources/SOURCES.md#publication-sources-chapter-3)
- **Chapter 5.** [§5.3.1.1](05-the-square-root-barrier-core-gm.md#5311-why-inertia-averaging-recovers-the-primitive-character) · [§5.3.1.2](05-the-square-root-barrier-core-gm.md#5312-frobenius-and-inertia-in-the-cyclotomic-host) · [§5.3.1.3](05-the-square-root-barrier-core-gm.md#5313-the-second-host-sign-from-a-quadratic-gauss-sum) · [§5.3.1.4](05-the-square-root-barrier-core-gm.md#5314-quadratic-reciprocity-and-the-host-splitting-signs) · [§5.3.1.5](05-the-square-root-barrier-core-gm.md#5315-eulers-criterion-over-a-finite-field) · [§5.3.1.6](05-the-square-root-barrier-core-gm.md#5316-cyclic-multiplicative-groups-of-finite-fields) · [§5.3.1.7](05-the-square-root-barrier-core-gm.md#5317-trace-pairings-and-the-additive-input-to-gauss-sums) · [§5.3.1.8](05-the-square-root-barrier-core-gm.md#5318-why-the-finite-field-trace-is-a-frobenius-sum) · [§5.3.1.9](05-the-square-root-barrier-core-gm.md#5319-primitive-elements-and-power-bases-for-separable-extensions) · [§5.3.1.10](05-the-square-root-barrier-core-gm.md#53110-power-bases-from-the-quotient-ring-remainders-multiplication-matrices-and-transport) · [§5.3.1.11](05-the-square-root-barrier-core-gm.md#53111-the-separable-greatest-common-divisor-in-the-primitive-element-proof) · [§5.3.1.12](05-the-square-root-barrier-core-gm.md#53112-root-multisets-and-separable-root-counting) · [§5.3.1.13](05-the-square-root-barrier-core-gm.md#53113-finite-divisibility-orders-and-prime-factors) · [§5.3.1.14](05-the-square-root-barrier-core-gm.md#53114-constructing-splitting-fields-and-extending-embeddings) · [§5.3.1.15](05-the-square-root-barrier-core-gm.md#53115-mutual-embeddings-of-algebraic-extensions) · [§5.3.1.16](05-the-square-root-barrier-core-gm.md#53116-product-decomposition-and-tensor-splitting-of-finite-%C3%A9tale-algebras) · [§5.3.1.17](05-the-square-root-barrier-core-gm.md#53117-finite-place-completion-embeddings-and-tensor-norm-transport) · [§5.3.1.18](05-the-square-root-barrier-core-gm.md#53118-the-same-tensor-norm-witness-at-a-real-place) · [§5.3.1.19](05-the-square-root-barrier-core-gm.md#53119-from-prime-degree-norms-to-the-cyclic-hasse-norm-principle) · [§5.3.1.20](05-the-square-root-barrier-core-gm.md#53120-cancelling-a-power-in-a-local-tensor-norm) · [§5.3.1.21](05-the-square-root-barrier-core-gm.md#53121-descending-an-odd-prime-degree-norm-after-adjoining-roots-of-unity). [Source map](../sources/SOURCES.md#publication-sources-chapter-5)

<a id="publication-evidence-ledger-2-p13"></a>

- **Chapter 4.** [§4.7](04-auxiliary-prime-pairs-and-host-fields.md#47-zero-density-mean-squares-and-siegels-lower-bound-from-the-large-sieve-to-pairgood) · [§4.7.1](04-auxiliary-prime-pairs-and-host-fields.md#471-motivation-why-a-crude-zero-density-bound-is-enough) · [§4.7.2](04-auxiliary-prime-pairs-and-host-fields.md#472-examples-the-primes-11-and-3-both-3mod8) · [§4.7.3](04-auxiliary-prime-pairs-and-host-fields.md#473-definitions) · [§4.7.4](04-auxiliary-prime-pairs-and-host-fields.md#474-lemmas-and-proofs-the-zero-density-box) · [§4.7.5](04-auxiliary-prime-pairs-and-host-fields.md#475-mean-squares-and-siegels-lower-bound-the-other-classical-inputs) · [§4.7.6](04-auxiliary-prime-pairs-and-host-fields.md#476-remarks) · [§4.8](04-auxiliary-prime-pairs-and-host-fields.md#48-from-the-zero-free-box-to-the-truncated-perron-tail) · [§4.8.1](04-auxiliary-prime-pairs-and-host-fields.md#481-motivation) · [§4.8.2](04-auxiliary-prime-pairs-and-host-fields.md#482-a-parameter-example-expository) · [§4.8.3](04-auxiliary-prime-pairs-and-host-fields.md#483-definitions-and-analytic-inputs) · [§4.8.4](04-auxiliary-prime-pairs-and-host-fields.md#484-lemma-the-box-supplies-a-bound-for-the-numerator) · [§4.8.5](04-auxiliary-prime-pairs-and-host-fields.md#485-theorem-conditional-truncated-tail-bound) · [§4.8.6](04-auxiliary-prime-pairs-and-host-fields.md#486-source-map-and-reading-boundary) · [§4.8.7](04-auxiliary-prime-pairs-and-host-fields.md#487-mellin-inversion-and-the-finite-rectangle) · [§4.8.8](04-auxiliary-prime-pairs-and-host-fields.md#488-local-zeros-and-the-logarithmic-derivative-in-tailbox) · [§4.9](04-auxiliary-prime-pairs-and-host-fields.md#49-counting-enough-candidates-before-the-sieve) · [§4.9.1](04-auxiliary-prime-pairs-and-host-fields.md#491-motivation) · [§4.9.2](04-auxiliary-prime-pairs-and-host-fields.md#492-a-small-progression-and-two-character-tests-expository) · [§4.9.3](04-auxiliary-prime-pairs-and-host-fields.md#493-definitions-and-named-analytic-inputs) · [§4.9.4](04-auxiliary-prime-pairs-and-host-fields.md#494-conditional-counting-proposition-lean-read) · [§4.9.5](04-auxiliary-prime-pairs-and-host-fields.md#495-from-candidate-count-to-a-window) · [§4.9.6](04-auxiliary-prime-pairs-and-host-fields.md#496-source-map-and-reading-boundary) · [4.10. Joining the two ranges of the relative progression estimate](04-auxiliary-prime-pairs-and-host-fields.md#410-joining-the-two-ranges-of-the-relative-progression-estimate) · [4.10.1. Two model calculations [Expository]](04-auxiliary-prime-pairs-and-host-fields.md#4101-two-model-calculations-expository) · [4.10.2. The common normalization](04-auxiliary-prime-pairs-and-host-fields.md#4102-the-common-normalization) · [4.10.3. Conditional splice and proof](04-auxiliary-prime-pairs-and-host-fields.md#4103-conditional-splice-and-proof) · [4.10.4. Scope and source map](04-auxiliary-prime-pairs-and-host-fields.md#4104-scope-and-source-map) · [§4.10.5](04-auxiliary-prime-pairs-and-host-fields.md#4105-the-far-range-numerical-absorption-lemma-num_main) · [§4.10.6](04-auxiliary-prime-pairs-and-host-fields.md#4106-the-differenced-explicit-formula-differenced_explicit_formula) · [§4.10.7](04-auxiliary-prime-pairs-and-host-fields.md#4107-the-residual-of-the-smoothed-explicit-formula) · [§4.10.8](04-auxiliary-prime-pairs-and-host-fields.md#4108-the-local-expansion-and-the-rectangle-identity-ex_local-and-ex_rect_fchi) · [§4.10.9](04-auxiliary-prime-pairs-and-host-fields.md#4109-uniform-polynomial-growth-in-the-half-plane-lfunction_polynomial_growth-and-exlf_growth) · [§4.10.10](04-auxiliary-prime-pairs-and-host-fields.md#41010-the-pole-subtracted-zeta-logarithmic-derivative) · [§4.10.11](04-auxiliary-prime-pairs-and-host-fields.md#41011-finite-height-contours-and-weighted-zero-sums) · [§4.10.12](04-auxiliary-prime-pairs-and-host-fields.md#p13-turan-finish) · [§4.10.13](04-auxiliary-prime-pairs-and-host-fields.md#41013-hyperbola-splitting-and-prime-moments-for-deuringheilbronn) · [§4.10.14](04-auxiliary-prime-pairs-and-host-fields.md#p13-chebyshev-tailmertens) · [§4.10.15](04-auxiliary-prime-pairs-and-host-fields.md#41015-the-chebyshev-lower-bound-from-least-common-multiples) · [§4.10.16](04-auxiliary-prime-pairs-and-host-fields.md#41016-the-costapereira-comparison) · [§4.10.17](04-auxiliary-prime-pairs-and-host-fields.md#41017-a-strict-prime-count-in-a-real-dyadic-interval) · [§4.10.18](04-auxiliary-prime-pairs-and-host-fields.md#41018-counting-the-prime-degree-factor-exception) · [§4.10.19](04-auxiliary-prime-pairs-and-host-fields.md#41019-rational-factors-and-the-seven-eighths-bound-for-squarefree-degree-splits) · [§4.10.21](04-auxiliary-prime-pairs-and-host-fields.md#41021-counting-roots-after-translation-by-a-unit) · [§4.10.22](04-auxiliary-prime-pairs-and-host-fields.md#41022-how-exceptional-prime-sets-avoid-each-other) · [§4.10.23](04-auxiliary-prime-pairs-and-host-fields.md#41023-when-prime-to-parts-of-roots-collide) · [§4.10.24](04-auxiliary-prime-pairs-and-host-fields.md#41024-separating-a-real-zero-from-1) · [§4.10.25](04-auxiliary-prime-pairs-and-host-fields.md#41025-the-siegel-lower-bound-from-biquadratic-product-series) · [§4.10.26](04-auxiliary-prime-pairs-and-host-fields.md#41026-regularizing-the-four-factor-product-and-bounding-its-taylor-remainder) · [§4.11](04-auxiliary-prime-pairs-and-host-fields.md#411-from-separated-inertia-lines-to-residual-irreducibility) · [§4.11.1](04-auxiliary-prime-pairs-and-host-fields.md#4111-why-a-prime-cycle-forces-primitivity-in-small-degree) · [§4.11.2](04-auxiliary-prime-pairs-and-host-fields.md#4112-why-three-fixed-points-suffice-in-jordans-theorem). [Source map](../sources/SOURCES.md#publication-sources-chapter-4)
- **Chapter 17.** [§17.4.5](17-behrends-sphere-lemma-and-host-geometry.md#1745-from-congruence-primes-to-a-usable-host-field-scale) · [§17.4.6](17-behrends-sphere-lemma-and-host-geometry.md#1746-bernoulli-selection-of-the-top-places) · [§17.4.7](17-behrends-sphere-lemma-and-host-geometry.md#1747-from-the-von-mangoldt-sum-to-the-prime-count) · [§17.4.8](17-behrends-sphere-lemma-and-host-geometry.md#1748-short-norm-primes-from-the-principal-ray-class) · [§17.4.9](17-behrends-sphere-lemma-and-host-geometry.md#1749-the-finite-character-projection-onto-the-principal-ray) · [§17.4.10](17-behrends-sphere-lemma-and-host-geometry.md#17410-the-exceptional-zero-in-the-trivial-ray-class-interval) · [§17.4.11](17-behrends-sphere-lemma-and-host-geometry.md#17411-producing-the-ray-class-endpoint-formula) · [§17.4.12](17-behrends-sphere-lemma-and-host-geometry.md#17412-producing-the-finite-local-zero-formula) · [§17.4.13](17-behrends-sphere-lemma-and-host-geometry.md#17413-mellin-continuation-and-uniform-growth-in-the-ray-class-family) · [§17.4.14](17-behrends-sphere-lemma-and-host-geometry.md#17414-euler-nonvanishing-and-the-center-of-the-local-disk) · [§17.4.15](17-behrends-sphere-lemma-and-host-geometry.md#17415-ray-class-size-and-theta-counts-at-a-fixed-modulus) · [§17.4.16](17-behrends-sphere-lemma-and-host-geometry.md#17416-the-ideal-level-weight-lamray-its-convolution-and-the-real-character-square) · [§17.4.17](17-behrends-sphere-lemma-and-host-geometry.md#17417-small-ideal-representatives-and-short-bases-at-a-fixed-modulus) · [§17.4.18](17-behrends-sphere-lemma-and-host-geometry.md#17418-minkowski-volume-and-small-ordinary-class-representatives) · [§17.4.19](17-behrends-sphere-lemma-and-host-geometry.md#17419-the-integral-model-and-canonical-raydata) · [§17.4.20](17-behrends-sphere-lemma-and-host-geometry.md#17420-from-the-identity-ideal-class-to-ray-multipliers) · [§17.4.21](17-behrends-sphere-lemma-and-host-geometry.md#17421-finite-modules-and-the-integrality-step-in-ideal-inversion) · [§17.4.22](17-behrends-sphere-lemma-and-host-geometry.md#17422-finite-ideal-quotients-and-the-absolute-norm) · [§17.4.23](17-behrends-sphere-lemma-and-host-geometry.md#17423-multiplicativity-of-the-absolute-ideal-norm) · [§17.4.24](17-behrends-sphere-lemma-and-host-geometry.md#17424-prime-ideal-norm-fibres-and-the-cost-of-removing-higher-residue-degrees) · [§17.4.25](17-behrends-sphere-lemma-and-host-geometry.md#17425-radial-haar-measure-and-the-gamma-factor-in-minkowski-volume) · [§17.4.26](17-behrends-sphere-lemma-and-host-geometry.md#17426-angular-measure-and-the-haar-product-in-polar-coordinates). [Source map](../sources/SOURCES.md#publication-sources-chapter-17)
- **Chapter 19.** [§19.3.8](19-published-layer-case-studies-ii.md#1938-cm-types-and-the-place-identification) · [§19.3.9](19-published-layer-case-studies-ii.md#1939-the-host-fields-raw-data-derived-properties-and-their-producers) · [§19.3.10](19-published-layer-case-studies-ii.md#19310-producing-the-raw-host-from-a-character-group) · [§19.3.11](19-published-layer-case-studies-ii.md#19311-the-layer-host-of-the-second-constructor) · [§19.3.11.1](19-published-layer-case-studies-ii.md#193111-complex-conjugation-the-real-fixed-field-and-the-cm-type-of-the-layer-host) · [§19.3.12](19-published-layer-case-studies-ii.md#19312-the-finite-group-and-the-stable-frame-order) · [§19.3.13](19-published-layer-case-studies-ii.md#19313-the-discriminant-of-the-second-hosts-real-subfield) · [§19.3.14](19-published-layer-case-studies-ii.md#19314-integral-power-bases-and-discriminants-at-prime-power-conductor) · [§19.3.15](19-published-layer-case-studies-ii.md#19315-integral-bases-at-general-cyclotomic-conductor) · [§19.3.16](19-published-layer-case-studies-ii.md#19316-relative-trace-after-extending-the-base-field) · [§19.3.17](19-published-layer-case-studies-ii.md#19317-cyclotomic-integer-quotients-and-translated-integral-bases) · [§19.3.18](19-published-layer-case-studies-ii.md#19318-cyclotomic-irreducibility-and-the-primitive-roots-minimal-polynomial) · [§19.3.19](19-published-layer-case-studies-ii.md#19319-from-conjugate-roots-to-power-basis-isomorphisms). [Source map](../sources/SOURCES.md#publication-sources-chapter-19)

<a id="publication-evidence-ledger-2-p7"></a>

- **Chapter 6.** [§6.4.5](06-stepanovs-method-and-multiplicity.md#645-from-lattice-slopes-to-the-weighted-mean-the-main-path-instance-of-clause-7) · [§6.4.6](06-stepanovs-method-and-multiplicity.md#646-from-local-lengths-to-clause-7-the-weight-partition) · [§6.4.7](06-stepanovs-method-and-multiplicity.md#647-the-rank-and-slope-at-the-level-prime) · [§6.4.8](06-stepanovs-method-and-multiplicity.md#648-from-residue-field-units-to-the-level-zero-forms) · [§6.4.9](06-stepanovs-method-and-multiplicity.md#649-why-the-split-diamonds-act-freely) · [§6.4.10](06-stepanovs-method-and-multiplicity.md#6410-local-torsion-and-the-finite-rational-stabilizer) · [§6.4.11](06-stepanovs-method-and-multiplicity.md#6411-level-zero-stabilizers-in-a-family) · [§6.4.12](06-stepanovs-method-and-multiplicity.md#6412-rational-finite-order-on-a-fixed-host) · [§6.4.13](06-stepanovs-method-and-multiplicity.md#6413-split-local-groups-and-the-pro-g-transport) · [§6.4.14](06-stepanovs-method-and-multiplicity.md#6414-definiteness-of-the-host-gram-matrix-at-real-embeddings) · [§6.4.15](06-stepanovs-method-and-multiplicity.md#6415-extending-a-real-embedding-to-the-host-field-the-algebraically-closed-lift) · [§6.4.16](06-stepanovs-method-and-multiplicity.md#6416-producing-pure-signatures-from-the-host-spaces) · [§6.4.17](06-stepanovs-method-and-multiplicity.md#6417-producing-the-finite-adelic-element-of-norm-minus-one) · [§6.4.17.1](06-stepanovs-method-and-multiplicity.md#64171-from-adic-completeness-to-a-local-norm-solution) · [§6.4.18](06-stepanovs-method-and-multiplicity.md#crystalline-tensor-and-lines) · [§6.4.19](06-stepanovs-method-and-multiplicity.md#acris-gauss-slope) · [§6.4.20](06-stepanovs-method-and-multiplicity.md#acris-gauss-extension) · [§6.4.21](06-stepanovs-method-and-multiplicity.md#6421-why-the-frobenius-matrix-in-an-adapted-basis-is-a-unit) · [§6.4.22](06-stepanovs-method-and-multiplicity.md#6422-reading-the-second-block-on-the-first-torsion-group) · [§6.4.23](06-stepanovs-method-and-multiplicity.md#local-record-inertia-polynomial). [Source map](../sources/SOURCES.md#publication-sources-chapter-6)

<a id="publication-evidence-ledger-2-p17"></a>

- **Chapter 7.** [§7.4.3.1](07-chains-of-theta-lifts.md#7431-spherical-transfer-at-a-split-place) · [§7.4.3.2](07-chains-of-theta-lifts.md#7432-evaluation-on-a-single-bruhat-cell) · [§7.4.3.3](07-chains-of-theta-lifts.md#7433-compact-bumps-and-averaged-kernels-on-a-single-cell) · [§7.4.3.4](07-chains-of-theta-lifts.md#7434-from-one-cell-to-the-full-bruhat-filtration) · [§7.4.3.5](07-chains-of-theta-lifts.md#7435-levels-in-the-unipotent-radical-and-supports-on-a-cell) · [§7.4.3.6](07-chains-of-theta-lifts.md#7436-composition-factors-of-a-cell-module) · [§7.4.3.7](07-chains-of-theta-lifts.md#7437-exterior-tensor-classification-on-a-block-levi) · [§7.4.3.8](07-chains-of-theta-lifts.md#7438-jacquet-modules-and-induction-of-exterior-tensors) · [§7.4.3.9](07-chains-of-theta-lifts.md#7439-open-normal-levels-in-compact-groups) · [§7.4.3.10](07-chains-of-theta-lifts.md#74310-local-iwasawa-decomposition-for-normalized-induction) · [§7.4.3.11](07-chains-of-theta-lifts.md#74311-the-compact-integral-and-unitarisability-of-normalized-induction) · [§7.4.3.12](07-chains-of-theta-lifts.md#74312-tensor-positive-forms-on-algebraic-levi-coefficients) · [§7.4.3.13](07-chains-of-theta-lifts.md#74313-invariant-complements-of-admissible-smooth-representations) · [§7.4.3.14](07-chains-of-theta-lifts.md#74314-central-eigenvalues-of-the-highest-derivative) · [§7.4.3.15](07-chains-of-theta-lifts.md#74315-strict-spectral-bounds-below-the-highest-product-derivative) · [§7.4.3.16](07-chains-of-theta-lifts.md#74316-the-highest-derivative-of-a-parabolic-product) · [§7.4.3.17](07-chains-of-theta-lifts.md#74317-separating-mirabolic-vectors-by-small-box-averages) · [§7.4.3.18](07-chains-of-theta-lifts.md#74318-from-successive-mirabolic-quotients-to-one-grouped-derivative) · [§7.4.3.19](07-chains-of-theta-lifts.md#74319-why-normalized-jacquet-modules-have-finite-length) · [§7.4.3.20](07-chains-of-theta-lifts.md#74320-from-positive-semidefinite-forms-to-the-strict-lower-derivative-bound) · [Normalized induction and Jacquet modules](07-normalized-induction-reading-guide.md#normalized-induction-and-jacquet-modules). [Source map](../sources/SOURCES.md#publication-sources-chapter-7)

<a id="publication-evidence-ledger-2-p8"></a>

- **Chapter 8.** [§8.4.4](08-divisibility-at-inert-primes.md#844-finite-jets-of-the-local-formal-group-kernel) · [§8.4.5](08-divisibility-at-inert-primes.md#845-from-the-single-kernel-expansion-to-the-low-term-lattice-bound-lowtermbound) · [§8.4.7](08-divisibility-at-inert-primes.md#847-frame-changes-and-integral-normalization-in-local-interpolation) · [§8.4.8](08-divisibility-at-inert-primes.md#848-from-target-pairings-to-the-lattice-bound) · [§8.4.9](08-divisibility-at-inert-primes.md#849-the-second-gauss-bound-and-the-even-position-loss) · [§8.4.10](08-divisibility-at-inert-primes.md#8410-the-positive-hecke-index-and-the-weighted-gauss-bound) · [§8.4.11](08-divisibility-at-inert-primes.md#8411-partition-multiplicities-residual-capacities-and-the-numerical-bridge-ea_brnum) · [§8.4.12](08-divisibility-at-inert-primes.md#8412-transporting-the-restricted-kernel-jet-to-the-three-frames) · [§8.4.13](08-divisibility-at-inert-primes.md#8413-the-normalized-local-norm-supply-nm_restnorm_of_place) · [§8.4.14](08-divisibility-at-inert-primes.md#8414-producing-ea_restsu-logarithmic-coordinate-integrality-restsinta-and-the-exponential-factor-reduction-ea_restsexpv_of) · [§8.4.16](08-divisibility-at-inert-primes.md#8416-the-biadditive-supply-restbeta-from-beprop-to-the-frobenius-fixed-class-of-gser) · [§8.4.17](08-divisibility-at-inert-primes.md#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar) · [§8.4.18](08-divisibility-at-inert-primes.md#8418-projection-and-first-derivatives-for-betaisg) · [§8.4.19](08-divisibility-at-inert-primes.md#8419-classifying-slice-coboundaries-and-the-lemmaone-supply) · [§8.4.20](08-divisibility-at-inert-primes.md#8420-two-variable-coboundaries-and-the-lemmatwo-supply) · [§8.4.21](08-divisibility-at-inert-primes.md#8421-frobenius-congruence-and-the-integral-odd-logarithm-coboundary) · [§8.4.22](08-divisibility-at-inert-primes.md#8422-the-multivariable-dwork-criterion-and-exponential-equivalence) · [§8.4.23](08-divisibility-at-inert-primes.md#8423-the-witt-vector-norm-and-frobenius-model-supply) · [§8.4.24](08-divisibility-at-inert-primes.md#8424-existence-uniqueness-and-all-orders-integrality-of-the-formal-group-logarithm-law) · [§8.4.25](08-divisibility-at-inert-primes.md#8425-symmetry-of-the-logarithm-law-and-the-multivariable-divided-derivative) · [§8.4.26](08-divisibility-at-inert-primes.md#8426-scalar-endomorphisms-and-the-norms-of-division-points) · [§8.4.31](08-divisibility-at-inert-primes.md#8431-control-class-change-and-the-existence-and-uniqueness-of-the-rescaled-logarithm) · [§8.4.32](08-divisibility-at-inert-primes.md#8432-why-the-two-controls-differ-by-a-multiple-of-p). [Source map](../sources/SOURCES.md#publication-sources-chapter-8)

<a id="publication-evidence-ledger-2-p10"></a>

- **Chapter 9.** [§9.4.5](09-heights-slopes-and-near-orthogonality.md#945-a-positive-semidefinite-bound-for-the-period-rows) · [§9.4.6](09-heights-slopes-and-near-orthogonality.md#946-polar-haar-measure-and-the-discrete-series-integrability-bound) · [§9.4.7](09-heights-slopes-and-near-orthogonality.md#947-formal-degree-ratios-under-a-shift-of-the-parameter) · [§9.4.8](09-heights-slopes-and-near-orthogonality.md#948-analytic-orbits-and-conditional-schur-formal-degree) · [§9.4.9](09-heights-slopes-and-near-orthogonality.md#949-derived-irreducibility-of-a-compact-k-type) · [§9.4.10](09-heights-slopes-and-near-orthogonality.md#9410-the-highest-weight-line-of-a-compact-k-type) · [§9.4.11](09-heights-slopes-and-near-orthogonality.md#9411-independence-of-generalized-eigenspaces) · [§9.4.12](09-heights-slopes-and-near-orthogonality.md#9412-from-torus-characters-to-diagonal-eigenvalues) · [§9.4.13](09-heights-slopes-and-near-orthogonality.md#9413-primary-decomposition-for-a-split-characteristic-polynomial) · [§9.4.14](09-heights-slopes-and-near-orthogonality.md#9414-constructing-a-compact-k-type-from-an-integral-dominant-label) · [§9.4.15](09-heights-slopes-and-near-orthogonality.md#9415-the-unitary-identification-of-two-compact-k-types) · [§9.4.21](09-heights-slopes-and-near-orthogonality.md#9421-compact-pieri-branching-and-the-tensor-step) · [§9.4.22](09-heights-slopes-and-near-orthogonality.md#9422-the-polynomial-model-behind-compact-weyl-dimensions) · [§9.4.23](09-heights-slopes-and-near-orthogonality.md#9423-the-prv-extremal-component-and-the-highest-weight-graph) · [§9.4.24](09-heights-slopes-and-near-orthogonality.md#9424-the-exterior-degree-of-the-physical-fock-highest-weight-line) · [§9.4.25](09-heights-slopes-and-near-orthogonality.md#9425-when-the-casimir-puts-the-physical-highest-weight-line-in-the-dirac-kernel) · [§9.4.26](09-heights-slopes-and-near-orthogonality.md#9426-recovering-the-formal-degree-constant-from-a-translation-ray) · [§9.4.27](09-heights-slopes-and-near-orthogonality.md#9427-paying-the-shared-compact-dual-haar-normalization-from-coordinate-densities) · [§9.4.28](09-heights-slopes-and-near-orthogonality.md#9428-how-the-tensor-sandwich-determines-a-one-step-formal-degree-ratio) · [§9.4.29](09-heights-slopes-and-near-orthogonality.md#9429-polar-bounds-for-the-weighted-psim-kernel) · [§9.4.30](09-heights-slopes-and-near-orthogonality.md#9430-recovering-the-k-finite-vectors-of-the-generated-closure). [Source map](../sources/SOURCES.md#publication-sources-chapter-9)

<a id="publication-evidence-ledger-2-p11"></a>

- **Chapter 10.** [§10.4.5](10-congruence-modules-to-sha.md#1045-the-dvr-determinant-lemma-and-block-cocycle-lengths) · [§10.4.6](10-congruence-modules-to-sha.md#1046-twist-existence-how-the-selmer-killing-character-is-chosen) · [§10.4.7](10-congruence-modules-to-sha.md#1047-where-does-adm2-come-from) · [§10.4.7.1](10-congruence-modules-to-sha.md#10471-lattice-specialization-one-index-bound-for-every-coprime-power) · [§10.4.7.2](10-congruence-modules-to-sha.md#10472-toric-hecke-relations-and-simultaneous-level-exponent-selection) · [§10.4.7.3](10-congruence-modules-to-sha.md#10473-theta-euler-factors-and-the-isotypic-lattice-where-non-divisibility-comes-from) · [§10.4.7.4](10-congruence-modules-to-sha.md#10474-one-family-of-auxiliary-places-for-the-selmer-polynomials-and-the-theta-steps) · [§10.4.7.5](10-congruence-modules-to-sha.md#10475-odd-prime-and-mod-two-production-of-the-selmer-coefficient-bound) · [§10.4.7.6](10-congruence-modules-to-sha.md#10476-producing-the-initial-adjugate-seed-scalar-descent-unused-left-places-and-the-ramified-ideal-threshold) · [§10.4.7.7](10-congruence-modules-to-sha.md#10477-producing-the-initial-selmer-corank-witness) · [§10.4.7.8](10-congruence-modules-to-sha.md#10478-dyadic-cocycle-evaluations-and-symmetric-annihilators) · [§10.4.7.9](10-congruence-modules-to-sha.md#10479-full-cocycle-span-in-the-residually-nonisomorphic-branch) · [§10.4.7.10](10-congruence-modules-to-sha.md#104710-equal-dimensions-for-the-original-residual-selmer-spaces) · [§10.4.7.11](10-congruence-modules-to-sha.md#104711-lifting-residual-cocycles-to-the-blochkato-lattice) · [§10.4.7.12](10-congruence-modules-to-sha.md#104712-integral-local-duality-and-the-two-finite-condition-annihilators) · [§10.4.7.13](10-congruence-modules-to-sha.md#104713-rational-local-duality-field-trace-coboundaries-and-the-general-coefficient-annihilator) · [§10.4.7.14](10-congruence-modules-to-sha.md#104714-exact-blochkato-annihilators-at-finite-level) · [§10.4.7.15](10-congruence-modules-to-sha.md#104715-descending-a-cyclotomic-coboundary-to-finite-coefficients) · [§10.4.8](10-congruence-modules-to-sha.md#1048-from-tame-inertia-to-the-order-of-a-selmer-determinant) · [§10.4.9](10-congruence-modules-to-sha.md#1049-positive-order-induction-and-the-determinant-coefficient-bound) · [§10.4.10](10-congruence-modules-to-sha.md#10410-from-an-adjugate-entry-to-a-frobenius-witness) · [§10.4.11](10-congruence-modules-to-sha.md#10411-the-local-presentation-at-the-new-pair-of-places) · [§10.4.11.1](10-congruence-modules-to-sha.md#104111-the-global-invariant-sum-in-the-new-place-reciprocity) · [§10.4.12](10-congruence-modules-to-sha.md#10412-a-square-presentation-of-the-global-selmer-functor) · [§10.4.13](10-congruence-modules-to-sha.md#10413-choosing-the-auxiliary-primes-in-a-common-galois-quotient) · [§10.4.14](10-congruence-modules-to-sha.md#10414-a-compatible-tate-generator-for-torsion-coefficients) · [§10.4.15](10-congruence-modules-to-sha.md#10415-finite-first-cohomology-for-the-fundamental-local-cocycle) · [§10.4.16](10-congruence-modules-to-sha.md#10416-one-integral-primitive-from-coboundaries-at-every-level) · [§10.4.17](10-congruence-modules-to-sha.md#10417-recovering-invariant-length-from-torsion-level-counts). [Source map](../sources/SOURCES.md#publication-sources-chapter-10)

<a id="publication-evidence-ledger-2-p12"></a>

- **Chapter 11.** [§11.4.3.1](11-the-window-bound-vwin.md#11431-from-a-finite-difference-to-stickelberger-nonvanishing) · [§11.4.3.2](11-the-window-bound-vwin.md#11432-from-the-stickelberger-membership-to-a-uniform-class-group-rank-bound) · [§11.4.3.3](11-the-window-bound-vwin.md#11433-kummer-reflection-and-the-root-of-unity-kernel) · [§11.4.3.4](11-the-window-bound-vwin.md#11434-signs-of-real-generators-and-the-binary-minus-defect) · [§11.4.3.5](11-the-window-bound-vwin.md#11435-norms-of-local-units-in-unramified-extensions) · [§11.4.3.6](11-the-window-bound-vwin.md#11436-the-idelic-norm-as-a-restricted-product-from-local-norms-to-one-idele) · [§11.4.3.7](11-the-window-bound-vwin.md#11437-the-second-inequality-for-cyclic-extensions-and-the-vanishing-of-the-minus-one-tate-group-of-the-idele-class-group) · [§11.4.3.8](11-the-window-bound-vwin.md#11438-the-two-arithmetic-suppliers-of-the-herbrand-quotient) · [§11.4.3.9](11-the-window-bound-vwin.md#11439-the-herbrand-quotient-of-a-finite-local-extension) · [§11.4.3.10](11-the-window-bound-vwin.md#114310-cyclic-hilbert-90-and-the-local-norm-index) · [§11.4.3.11](11-the-window-bound-vwin.md#114311-cyclic-tate-periodicity-and-the-local-degree-two-order) · [§11.4.3.12](11-the-window-bound-vwin.md#114312-the-tate-cup-product-by-augmentation-shifts) · [§11.4.3.13](11-the-window-bound-vwin.md#114313-the-degree-zero-unit-of-the-tate-cup-product) · [§11.4.3.14](11-the-window-bound-vwin.md#114314-the-zero-degree-normalization-of-tates-isomorphism) · [§11.4.3.15](11-the-window-bound-vwin.md#114315-detecting-cohomological-triviality-on-subgroups) · [§11.4.3.16](11-the-window-bound-vwin.md#114316-fundamental-classes-and-the-three-subgroup-hypotheses-in-a-class-formation) · [§11.4.3.17](11-the-window-bound-vwin.md#114317-arithmetic-realization-of-the-non-archimedean-local-class-formation-localclassformation) · [§11.4.3.18](11-the-window-bound-vwin.md#114318-local-cup-symbols-and-evaluation-of-artin-reciprocity) · [§11.4.5](11-the-window-bound-vwin.md#1145-from-two-zero-annihilators-to-a-perfect-local-cup-pairing) · [§11.4.6](11-the-window-bound-vwin.md#1146-from-the-root-of-unity-base-to-arbitrary-finite-local-coefficients) · [§11.4.7](11-the-window-bound-vwin.md#1147-the-open-subgroup-kummer-bridge-in-degree-three) · [§11.4.8](11-the-window-bound-vwin.md#1148-low-degree-finiteness-on-an-open-subgroup). [Source map](../sources/SOURCES.md#publication-sources-chapter-11)

<a id="publication-evidence-ledger-2-p14"></a>

- **Chapter 12.** [The holomorphic Lefschetz input to the odd-rank seed](12-galois-representations-and-local-langlands.md#the-holomorphic-lefschetz-input-to-the-odd-rank-seed) · [From a finite étale chart to the local Lefschetz weight](12-galois-representations-and-local-langlands.md#from-a-finite-%C3%A9tale-chart-to-the-local-lefschetz-weight) · [From fixed-point vanishing to a global Čech boundary](12-galois-representations-and-local-langlands.md#from-fixed-point-vanishing-to-a-global-%C4%8Dech-boundary) · [From the finite-algebra trace to the reduced fibre](12-galois-representations-and-local-langlands.md#from-the-finite-algebra-trace-to-the-reduced-fibre) · [From a general projection to a reduced origin fibre](12-galois-representations-and-local-langlands.md#from-a-general-projection-to-a-reduced-origin-fibre) · [Forms with prescribed jets at finitely many points](12-galois-representations-and-local-langlands.md#forms-with-prescribed-jets-at-finitely-many-points) · [The Sard step: translation parameters that keep the jets](12-galois-representations-and-local-langlands.md#the-sard-step-translation-parameters-that-keep-the-jets) · [Holomorphic local sections of étale families](12-galois-representations-and-local-langlands.md#holomorphic-local-sections-of-%C3%A9tale-families) · [Why the transversal zeros are finite: Nakayama and minimal primes](12-galois-representations-and-local-langlands.md#why-the-transversal-zeros-are-finite-nakayama-and-minimal-primes) · [Choosing the denominator and detecting the open cover](12-galois-representations-and-local-langlands.md#choosing-the-denominator-and-detecting-the-open-cover) · [Changing the denominator in cotangent generation](12-galois-representations-and-local-langlands.md#changing-the-denominator-in-cotangent-generation). [Source map](../sources/SOURCES.md#publication-sources-chapter-12)

<a id="publication-evidence-ledger-2-p15"></a>

- **Chapter 12.** [§12.4.5](12-galois-representations-and-local-langlands.md#1245-compact-open-fixed-spaces-and-the-smooth-contragredient) · [§12.4.6](12-galois-representations-and-local-langlands.md#1246-detecting-a-vector-by-all-its-twisted-jacquet-images) · [§12.4.7](12-galois-representations-and-local-langlands.md#1247-integral-matrices-and-the-compact-open-congruence-basis) · [§12.4.8](12-galois-representations-and-local-langlands.md#1248-why-ordered-segment-quotients-exhaust-the-irreducible-representations) · [§12.4.9](12-galois-representations-and-local-langlands.md#1249-jacquet-shuffles-and-the-descending-segment-word) · [§12.4.10](12-galois-representations-and-local-langlands.md#12410-producing-the-increasing-segment-from-adjacent-pairs) · [§12.4.11](12-galois-representations-and-local-langlands.md#12411-from-a-conductor-ball-average-to-the-mirabolic-pairing). [Source map](../sources/SOURCES.md#publication-sources-chapter-12)

<a id="publication-evidence-ledger-2-p16"></a>

- **Chapter 13.** [§13.4.4](13-greens-theorem-and-the-literature-layer.md#1344-where-greenregularcharacters-comes-from-regular-characters-produce-cuspidal-characters) · [§13.4.5](13-greens-theorem-and-the-literature-layer.md#1345-why-lifted-power-sums-are-virtual-characters) · [§13.4.6](13-greens-theorem-and-the-literature-layer.md#1346-the-gram-matrix-and-fourier-expansion-of-primitive-class-functions) · [§13.4.7](13-greens-theorem-and-the-literature-layer.md#1347-parabolic-induction-and-the-virtual-character-subtraction) · [§13.4.8](13-greens-theorem-and-the-literature-layer.md#1348-why-the-cuspidal-count-exhausts-greens-list) · [§13.4.9](13-greens-theorem-and-the-literature-layer.md#1349-teichm%C3%BCller-lifts-frobenius-orbits-and-choice-of-labels) · [§13.4.9.1](13-greens-theorem-and-the-literature-layer.md#13491-from-one-eigenspace-to-the-polynomial-kernel) · [§13.4.9.2](13-greens-theorem-and-the-literature-layer.md#13492-from-invariant-subspaces-to-the-primary-character-value) · [§13.4.9.3](13-greens-theorem-and-the-literature-layer.md#13493-m%C3%B6bius-inversion-of-affine-dimension-sums) · [§13.4.9.3.1](13-greens-theorem-and-the-literature-layer.md#134931-the-adjoinroot-quotient-and-its-coordinates) · [§13.4.10](13-greens-theorem-and-the-literature-layer.md#13410-from-a-norm-one-virtual-character-to-a-positive-irreducible-character) · [§13.4.11](13-greens-theorem-and-the-literature-layer.md#13411-why-virtual-characters-have-integral-coefficients) · [§13.4.12](13-greens-theorem-and-the-literature-layer.md#13412-naming-laws-pmgreencuspidal-and-label-well-definedness-across-consumers) · [§13.4.13](13-greens-theorem-and-the-literature-layer.md#13413-elliptic-character-formulas-and-determination-of-cuspidal-characters-on-regular-elliptic-elements) · [§13.4.14](13-greens-theorem-and-the-literature-layer.md#13414-converse-regular-label-existence-exists_regular) · [§13.4.15](13-greens-theorem-and-the-literature-layer.md#13415-central-idempotent-orthogonality-zidemorthogonal_holds-and-the-representation-level-bridge-to-pmgreencuspidal) · [§13.4.16](13-greens-theorem-and-the-literature-layer.md#13416-cuspidality-from-unipotent-radical-sums) · [§13.4.17](13-greens-theorem-and-the-literature-layer.md#13417-mackey-orthogonality-for-cuspidal-induction) · [§13.4.18](13-greens-theorem-and-the-literature-layer.md#13418-whittaker-averages-and-the-degree-of-a-green-series) · [§13.4.19](13-greens-theorem-and-the-literature-layer.md#13419-fourier-decomposition-on-the-finite-mirabolic-group) · [§13.4.20](13-greens-theorem-and-the-literature-layer.md#13420-block-diagonal-mirabolic-induction-and-the-gelfandgraev-factor) · [§13.4.21](13-greens-theorem-and-the-literature-layer.md#13421-why-every-non-open-whittaker-cell-vanishes) · [§13.4.22](13-greens-theorem-and-the-literature-layer.md#13422-the-open-whittaker-cell-and-its-exact-weight) · [§13.4.23](13-greens-theorem-and-the-literature-layer.md#13423-column-reduction-and-the-unique-monomial-core-bruhat-decomposition) · [§13.4.24](13-greens-theorem-and-the-literature-layer.md#13424-degenerate-whittaker-eigenspaces-on-parabolic-mackey-cells) · [§13.4.25](13-greens-theorem-and-the-literature-layer.md#13425-why-the-levi-whittaker-space-is-a-line). [Source map](../sources/SOURCES.md#publication-sources-chapter-13)

<a id="publication-evidence-ledger-2-masullo-foundations"></a>

- **Chapter 14.** [§14.4.2](14-masullos-trace-formula-route.md#1442-poisson-summation-and-jumps-on-the-local-logarithmic-lattice) · [§14.4.2.1](14-masullos-trace-formula-route.md#14421-fourier-completeness-on-the-circle-and-pointwise-reconstruction) · [§14.4.2.2](14-masullos-trace-formula-route.md#14422-stoneweierstrass-for-the-circle-character-algebra) · [§14.4.2.3](14-masullos-trace-formula-route.md#14423-continuous-functions-are-dense-in-l2-of-the-circle) · [§14.4.2.3.1](14-masullos-trace-formula-route.md#144231-finite-measure-simple-functions-in-lp) · [§14.4.2.4](14-masullos-trace-formula-route.md#14424-urysohn-cutoffs-with-finite-measure) · [§14.4.2.5](14-masullos-trace-formula-route.md#14425-compactly-supported-continuous-functions-are-dense-in-l2) · [Absolute Cauchy products in a Banach algebra](14-masullos-trace-formula-route.md#absolute-cauchy-products-in-a-banach-algebra) · [Factorial ratios and the infinite radius of the Banach exponential](14-masullos-trace-formula-route.md#factorial-ratios-and-the-infinite-radius-of-the-banach-exponential) · [Differentiating the Banach exponential](14-masullos-trace-formula-route.md#differentiating-the-banach-exponential) · [The logarithm of a near-identity unitary matrix](14-masullos-trace-formula-route.md#the-logarithm-of-a-near-identity-unitary-matrix) · [Why self-adjoint elements have real spectrum](14-masullos-trace-formula-route.md#why-self-adjoint-elements-have-real-spectrum) · [Spectral permanence by propagation of the resolvent](14-masullos-trace-formula-route.md#spectral-permanence-by-propagation-of-the-resolvent) · [Continuous functional calculus and the positive square root](14-masullos-trace-formula-route.md#continuous-functional-calculus-and-the-positive-square-root) · [The spectral decomposition of a positive compact operator](14-masullos-trace-formula-route.md#the-spectral-decomposition-of-a-positive-compact-operator). [Source map](../sources/SOURCES.md#publication-sources-chapter-14)
- **Chapter 15.** [§15.4.3.1](15-two-proofs-side-by-side.md#15431-half-densities-the-modulus-the-multiplicative-haar-measure-and-the-diagonal-weight) · [§15.4.3.2](15-two-proofs-side-by-side.md#15432-from-real-linear-haar-determinants-to-density-weighted-l2-transport) · [§15.4.3.3](15-two-proofs-side-by-side.md#15433-uniqueness-of-haar-measure-proportionality-normalization-and-the-constant-in-the-half-density-transport) · [§15.4.3.4](15-two-proofs-side-by-side.md#15434-constructing-haar-measure-from-finite-covers) · [§15.4.3.5](15-two-proofs-side-by-side.md#15435-finite-place-products-from-rectangles-and-marginals) · [§15.4.3.6](15-two-proofs-side-by-side.md#15436-from-outer-measure-to-a-countably-additive-measure) · [§15.4.3.7](15-two-proofs-side-by-side.md#ch15-tychonoff-haar-content) · [§15.4.3.8](15-two-proofs-side-by-side.md#ch15-preregular-compact-covers) · [§15.4.3.9](15-two-proofs-side-by-side.md#ch15-concentrating-kernels) · [§15.4.3.10](15-two-proofs-side-by-side.md#154310-how-powers-of-a-unique-peak-concentrate-at-a-point) · [§15.4.3.11](15-two-proofs-side-by-side.md#154311-haar-measure-on-p-adic-balls-and-shells) · [§15.4.3.12](15-two-proofs-side-by-side.md#154312-completing-the-rationals-at-a-prime) · [§15.4.3.13](15-two-proofs-side-by-side.md#154313-the-canonical-discrete-value-group-of-a-local-field). [Source map](../sources/SOURCES.md#publication-sources-chapter-15)

<a id="publication-evidence-ledger-2-p2-p18"></a>

- **Chapter 18.** [§18.3.5](18-auditing-the-published-layer-case-studies.md#1835-local-conditions-and-the-selmer-exact-sequence) · [§18.3.6](18-auditing-the-published-layer-case-studies.md#1836-the-unramified-local-condition-and-its-dual) · [§18.3.7](18-auditing-the-published-layer-case-studies.md#1837-local-euler-characteristics-away-from-the-residue-prime) · [§18.3.8](18-auditing-the-published-layer-case-studies.md#1838-decomposition-groups-as-galois-groups-of-completions) · [§18.3.9](18-auditing-the-published-layer-case-studies.md#1839-counting-the-local-degree-closed-balls-integral-approximation-and-the-power-kernel) · [§18.3.10](18-auditing-the-published-layer-case-studies.md#18310-integral-elements-the-prime-below-a-valuation-ring-and-conjugation-over-a-place) · [§18.3.11](18-auditing-the-published-layer-case-studies.md#18311-frobenius-elements-at-a-place-existence-inertia-cosets-and-conjugation) · [§18.3.12](18-auditing-the-published-layer-case-studies.md#18312-transporting-galois-groups-along-a-field-isomorphism-conjugation-decomposition-groups-and-quotients) · [§18.3.13](18-auditing-the-published-layer-case-studies.md#18313-pulling-back-local-invariants-and-trace-pairings) · [§18.3.14](18-auditing-the-published-layer-case-studies.md#18314-transporting-residue-fields-prime-norms-and-local-brauer-normalizations) · [§18.3.15](18-auditing-the-published-layer-case-studies.md#18315-cyclotomic-characters-and-total-complexity-under-field-isomorphisms) · [§18.3.16](18-auditing-the-published-layer-case-studies.md#18316-transporting-the-poitoutate-nine-term-sequence) · [§18.3.17](18-auditing-the-published-layer-case-studies.md#18317-transporting-the-tateshafarevich-kernels-in-degrees-one-and-two) · [§18.3.18](18-auditing-the-published-layer-case-studies.md#18318-single-model-assembly) · [§18.3.19](18-auditing-the-published-layer-case-studies.md#18319-the-arithmetic-sha-dictionary-and-its-restriction-squares) · [§18.3.20](18-auditing-the-published-layer-case-studies.md#18320-from-compact-support-to-the-nine-term-poitoutate-sequence) · [§18.3.21](18-auditing-the-published-layer-case-studies.md#18321-from-the-coefficient-trace-to-surjective-compact-corestriction) · [§18.3.22](18-auditing-the-published-layer-case-studies.md#18322-the-upper-field-root-of-unity-pairing) · [§18.3.23](18-auditing-the-published-layer-case-studies.md#18323-open-subgroups-larger-fixed-fields-and-the-local-family) · [§18.3.24](18-auditing-the-published-layer-case-studies.md#18324-combining-prime-power-compact-pairings-on-the-same-module) · [§18.3.25](18-auditing-the-published-layer-case-studies.md#18325-from-coinduced-coefficients-to-compact-duality-at-a-fixed-exponent) · [§18.3.26](18-auditing-the-published-layer-case-studies.md#18326-extending-continuous-cohomology-from-a-closed-subgroup). [Source map](../sources/SOURCES.md#publication-sources-chapter-18)
- **Chapter 19.** [§19.0](19-published-layer-case-studies-ii.md#190-how-the-main-path-reaches-the-literature-layer) · [§19.1](19-published-layer-case-studies-ii.md#191-shins-galois-representation) · [§19.2](19-published-layer-case-studies-ii.md#192-chenevierharris-and-monodromy) · [§19.3](19-published-layer-case-studies-ii.md#193-absolute-theta-convergence) · [§19.3.1](19-published-layer-case-studies-ii.md#1931-siegel-sets-and-the-integrable-majorant) · [§19.3.2](19-published-layer-case-studies-ii.md#1932-rational-reduction-and-the-covering-of-the-adelic-quotient) · [§19.3.3](19-published-layer-case-studies-ii.md#1933-the-lattice-majorant-for-the-inverse-torus) · [§19.3.4](19-published-layer-case-studies-ii.md#1934-from-finite-support-to-a-fixed-minkowski-lattice) · [§19.3.5](19-published-layer-case-studies-ii.md#1935-a-common-finite-support-for-schwartz-majorants) · [§19.3.6](19-published-layer-case-studies-ii.md#1936-compatible-adelic-coordinates-and-real-parameters) · [§19.3.7](19-published-layer-case-studies-ii.md#1937-unit-cells-and-the-uniform-weighted-lattice-count) · [§19.4](19-published-layer-case-studies-ii.md#194-global-doubling) · [§19.5](19-published-layer-case-studies-ii.md#195-unramified-split-doubling) · [§19.6](19-published-layer-case-studies-ii.md#196-convergent-rallis-inner-product) · [§19.7](19-published-layer-case-studies-ii.md#197-status-of-the-open-items). [Source map](../sources/SOURCES.md#publication-sources-chapter-19)

### 16.3.6 Errata located in the 23–28 November settlement

Status is measured against the public chapter text. N1–N13 refer to the 02:12 FRONTIER-rhbook §7 review codes. The 13:57 edition records later findings and revised audit classifications, with paths below identifying the reports across editions. The paths are run-relative locators in the editorial archive.

| ID | Published locus | Status | Audit finding and disposition | Review record |
|---|---|---|---|---|
| N1 | [§1.2.2.14](01-statement-and-fidelity.md#12214-from-a-rational-hermitian-trace-form-to-a-euclidean-lattice) | **Located; addressed** | Integer-cutoff theta estimate retained. The interpolation to a real radius needs floor(N)+1. The text uses integer N and does not claim the rejected real-radius bound. | Same-source preliminary review R078 · `ssaudit-rhbook-ch01-theta-coercive-1126r-11260822-i1-11260928-11261228/REPORT.md` |
| N2 | [§10.4.7.14](10-congruence-modules-to-sha.md#104714-exact-blochkato-annihilators-at-finite-level) | **Located; addressed** | The finite Bloch–Kato annihilator proof uses nondegeneracy at the specified divisible-twist coboundary target. Its converse keeps the original-side finite local condition explicit. | Same-source preliminary review R047 · `ssaudit-rhbook-ch10-bkc-finite-1127e-11260133-i1-11260239-11260522-i1-11260852/REPORT.md` |
| N3 | [From a finite filter to an integrable endpoint neighborhood](03-landau-window-criterion.md#from-a-finite-filter-to-an-integrable-endpoint-neighborhood) | **Located; addressed** | The publication uses the publisher and indexed original for attribution. The mismatched PDF in the earlier package supplies no evidence. The four local integrability results retain their original scope. | Same-source preliminary review R088 · `ssaudit-rhbook-ch03-local-integrable-1126s-11260846-i1-1126095-11261340/REPORT.md` |
| N4 | [§12.4.11](12-galois-representations-and-local-langlands.md#12411-from-a-conductor-ball-average-to-the-mirabolic-pairing) | **Located; addressed** | The high-dimensional conductor-ball example restores the factor a₀ᵐ for arbitrary Haar and states a₀=1 in the normalized examples. | Same-source preliminary review R102 · `ssaudit-rhbook-ch12-pairing-conductor-1126v-11261058-11261446/REPORT.md` |
| N5 | [§18.3.23](18-auditing-the-published-layer-case-studies.md#18323-open-subgroups-larger-fixed-fields-and-the-local-family) | **Located; addressed** | The completion factors are cited to Milne, ANT Proposition 8.2, p. 136, and the unramified extension to Corollary 7.52. | Same-source preliminary review R105 · `ssaudit-rhbook-ch18-open-field-1126v-11261058-11261440/REPORT.md` |
| N6 | [Completing a Borel measure and transporting integrals](03-landau-window-criterion.md#completing-a-borel-measure-and-transporting-integrals) | **Located; addressed** | Adjacency requires IntervalIntegrable on both legs. With the pinned zero convention, the omitted-premise example gives 0+1≠0. | Review R133 (R011, same-source in the later register) · `audit-rhbook-ch03-realvolume-1126aa-11261446-i1-11261552-i2--11261740/REPORT.md` |
| N7 | [Factorial ratios and the infinite radius of the Banach exponential](14-masullos-trace-formula-route.md#factorial-ratios-and-the-infinite-radius-of-the-banach-exponential) | **Located; addressed** | The exponential identity survives. The star operation reverses products in the noncommutative case. The published proof applies the involution to each power and passes to the limit by continuity (bc1e57a). | Review R134 (R057, same-source in the later register) · `audit-rhbook-ch14-exp-radius-1126ad-11261710-i1-11261734-11261828/REPORT.md` |
| N8 | [Factorial ratios and the infinite radius of the Banach exponential](14-masullos-trace-formula-route.md#factorial-ratios-and-the-infinite-radius-of-the-banach-exponential) | **Located; addressed** | The radius-zero reverse-ratio remark requires a hypothesis such as NormOneClass. The published remark adds unit norm and gives the zero-algebra exception (bc1e57a). | Review R134 (R057, same-source in the later register) · `audit-rhbook-ch14-exp-radius-1126ad-11261710-i1-11261734-11261828/REPORT.md` |
| N9 | [§9.4.26](09-heights-slopes-and-near-orthogonality.md#9426-recovering-the-formal-degree-constant-from-a-translation-ray) | **Located; text pending (citations)** | The quadratic comparison already uses the negative trace. The printed references still need Harish-Chandra §39, p. 90, for acceptability and Atiyah–Schmid through p. 47. | Same-source preliminary review R137 · `ssaudit-rhbook-ch09-degree-limit-1126z-11261346-i1-11261452-i2-11261822/REPORT.md` |
| N10 | [§8.4.31](08-divisibility-at-inert-primes.md#8431-control-class-change-and-the-existence-and-uniqueness-of-the-rescaled-logarithm) | **Located; addressed** | The section retains the control-class and log-rescaling conclusions and omits the rejected identification of the q-power series with the logarithm of pT+T^q. | Review R147 (R032, same-source in the later register) · `audit-rhbook-ch08-logchange-1126ac-11261640-i1-11261740-11261852/REPORT.md` |
| N11 | [§9.4.6](09-heights-slopes-and-near-orthogonality.md#946-polar-haar-measure-and-the-discrete-series-integrability-bound) · [§9.4.27](09-heights-slopes-and-near-orthogonality.md#9427-paying-the-shared-compact-dual-haar-normalization-from-coordinate-densities) | **Located; addressed** | In mixed signature the compact factor has probability Haar, while its image has ambient polar measure zero. The log-exp chart comparison uses the derivative at the origin and a local error bound. | Review R159 (R033, same-source in the later register) · `audit-rhbook-ch09-cd-density-1126af-11261840-11262040/REPORT.md` |
| N12 | [§9.4.27](09-heights-slopes-and-near-orthogonality.md#9427-paying-the-shared-compact-dual-haar-normalization-from-coordinate-densities) | **Located; addressed** | The QR change of variables retains the global constant for probability Haar on the unitary factor. | Review R159 (R033, same-source in the later register) · `audit-rhbook-ch09-cd-density-1126af-11261840-11262040/REPORT.md` |
| N13 | [§4.11.1](04-auxiliary-prime-pairs-and-host-fields.md#4111-why-a-prime-cycle-forces-primitivity-in-small-degree) | **Located; addressed** | The text uses Jordan's 1871 high transitivity and his 1873 theorem for the odd-prime range. The OCR of the narrower 1871 corollary gives no general degree bound for this use. | Same-source preliminary review R187 · `ssaudit-rhbook-ch04-primitive-1126ah-11262016-i1-11262122-11262304/REPORT.md` |
| N14 | [Chapter 11](11-the-window-bound-vwin.md#1146-from-the-root-of-unity-base-to-arbitrary-finite-local-coefficients) | **Located; text pending** | The fixed order-16 quotient in the printed example supplies a particular finite model. The assertion about every 2-primary extension of the 3-adic field and the unrestricted descent of continuous 3-torsion cochains to the maximal pro-3 quotient require correction. Inflation can kill a nonzero finite-quotient class. | R043 · `audit-rhbook-ch11-localdevissage-1126am-11262358-r-11280156-11280250/REPORT.md` |
| N15 | [Chapter 11](11-the-window-bound-vwin.md#1147-the-open-subgroup-kummer-bridge-in-degree-three) | **Located; addressed** | The open-subgroup bridge uses the specified carry cocycles and computes the invariant before the stated twisted inflation. The narrower comparison leaves N14 open. | R272 · `ssaudit-rhbook-ch11-kummeropen-1128f-11280426-11280527/REPORT.md` |
| N16 | [Chapter 15](15-two-proofs-side-by-side.md#154312-completing-the-rationals-at-a-prime) | **Located; addressed** | The rational completion uses the isometric dense embedding for its own p-adic norm. The map into another characteristic-zero local field needs a matching norm normalization for an isometry. | R062 · `audit-rhbook-ch15-padic-completion-1126am-11262358-r-1128015-11280232/REPORT.md` |
| N17 | [Chapter 15](15-two-proofs-side-by-side.md#154312-completing-the-rationals-at-a-prime) | **Located; addressed** | The discarded arXiv identifier referred to a different subject. The Lewis reference for formalizing the p-adic numbers is arXiv:1909.11342. | R062 · `audit-rhbook-ch15-padic-completion-1126am-11262358-r-1128015-11280232/REPORT.md` |
| N18 | [Chapter 18](18-auditing-the-published-layer-case-studies.md#18326-extending-continuous-cohomology-from-a-closed-subgroup) | **Located; text pending** | The product model admits a homomorphic projection. The audit supplies a quaternion-group replacement for the obstruction to a homomorphic retraction. The extension theorem needs only its stated transversal properties. | R067 · `audit-rhbook-ch18-cochainextend-1128i-11280551-11280627/REPORT.md` |
| N19 | [Chapter 13](13-greens-theorem-and-the-literature-layer.md#13415-central-idempotent-orthogonality-zidemorthogonal_holds-and-the-representation-level-bridge-to-pmgreencuspidal) | **Located; text pending** | The Green label bridge still refers to an absent U3 identifier and describes a label interface at odds with the archive's actual fields. Follow the cuspidal bridge in §13.4.16 and the specific identifiers in the audit. | R054 · `audit-rhbook-ch13-mirabolicpub-11280915-11280951/REPORT.md` |
| N20 | [Chapter 18](18-auditing-the-published-layer-case-studies.md#1833-exact-lean-definitions-and-verbatim-literature-comparison-cluster-ii) · [Chapter 18](18-auditing-the-published-layer-case-studies.md#1834-fidelity-lemma-and-line-by-line-r3-proofs-cluster-ii) | **Located; text pending** | The older statement comparison still uses DualMod. The twisted dual and the exact scope of the all-complex higher-vanishing consumer need the corrections in the audit. | R071 · `audit-rhbook-ch18-selmerladderpub-11281121-11281157-r-11281215/REPORT.md` |
| N21 | [Chapter 10](10-congruence-modules-to-sha.md#104710-equal-dimensions-for-the-original-residual-selmer-spaces) | **Located; text pending (source coordinates)** | The source entry still gives an out-of-range line 273 for ResidualSelmerFinrankEqDual. The audited 226–273 range belongs to LocalDualityFiniteDiscreteModules, and the first file should be cited at 17–270. | R041 · `audit-rhbook-ch10-spanpub-1128r-11280827-11280915/REPORT.md` |
| N22 | [Chapter 4](04-auxiliary-prime-pairs-and-host-fields.md#41013-hyperbola-splitting-and-prime-moments-for-deuringheilbronn) | **Located; text pending** | The audit gives three corrected printed example values: 3946/45045, 1/35 and 3/(8√2). The main result retains its audited scope. | R014 · `audit-rhbook-ch04-momentpublish-1128m-11280657-11280721/REPORT.md` |
| N23 | [Chapter 9](09-heights-slopes-and-near-orthogonality.md#94-lemmas-and-proofs) | **Located; follow-up inspected** | The renumbered compact-model publication had seven failed internal links and six old chapter/source references at audit. Check specific post-audit repairs at the current links before closing the remaining references. | R037 · `audit-rhbook-ch09-midblockpub-11281121-11281151-r-11281215/REPORT.md` |
| N24 | [Chapter 5](05-the-square-root-barrier-core-gm.md#53117-finite-place-completion-embeddings-and-tensor-norm-transport) | **Located; addressed** | The old HasseEt member digest was corrected before this settlement. The follow-up confirmed the old value is absent from the public tree. | R022 · `audit-rhbook-ch05-placepub-1128u-11281051-11281127/REPORT.md` |
| N25 | [Chapter 2](02-functional-equations-and-primitive-characters.md#2327-dominated-convergence-through-the-l1-extension-the-filter-to-sequence-reduction-the-decreasing-tail-supremum-step-and-local-uniform-domination-of-the-complex-gamma-kernel) | **Located; rendering follow-up** | The audit lists corrupted formula tokens that can survive a zero KaTeX-error check. Its per-page controls cover SOURCES and the related Chapter 10, 12 and 8 findings. The formula render check for this settlement concerns new records and reproduces the baseline warnings separately. | R007 · `audit-rhbook-ch02-holderpublish-1128p-11280733-11280757/REPORT.md` |
| N26 | [Chapter 1](01-statement-and-fidelity.md#12210-rational-cauchy-completion-dedekind-suprema-and-realinstcompletespace) | **Located; attribution follow-up** | The Mathlib 2020 paper and Carneiro credit do not establish the exact inducedOrderRingIso proof attribution. The cited CompleteField history distinguishes the Best and Dillies work. | R004 · `audit-rhbook-ch01-seriespublish-1128p-11280733-11280809/REPORT.md` |

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
     Trace how `FormalGroupSystem.Conclusion1`/`Conclusion2` (`src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:633, 649`) proves
     single-step Lubin–Tate theta-kernel divisibility at inert primes, and how `U3` Picard modular
     surface congruences feed `PropGK` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:36`, Chapter 11).
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
exports have published passing replays (Ledger 1). Across Chapters 1–13 and 17–18 of this textbook, we have translated
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


---

## 16.6 The Nielsen vacuity critique: what a `True` predicate does and does not show

On 20–22 November 2026 Jenny Lorraine Nielsen (Center for Topological Physics, Lawrence, Kansas) posted
*Invalidity of the Alpoge Proposed Proof of the Riemann Hypothesis* on PhilArchive (16 versions by
2026-11-22 18:09 UTC; not peer reviewed) [Community · [E14](../sources/SOURCES.md#e14)]. Its claim is
that the proof is invalid because the geometric and lattice witnesses on which the argument rests are
vacuous. We separate the claim into what can be checked in the archive and the inference drawn from it.

### 16.6.1 What the archive contains `[Lean, read]`

Checked by us against the pinned archive (`lean.tar.gz`, sha256 `9631b4f0…7fc`):

- `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:19` defines
  `def anyGeometry : GeoP := fun _ _ _ => True`, six lines below the contentful predicate `geoOf`
  (a positive `c` with `IsGeoOf` and `HasTrueSurf`). Both have type `GeoP`.
- `GeoCl Γ` (`NotGeoClFalse.lean`) is an inductive closure whose `base` constructor accepts any proof of
  `Γ`; hence `geoCl anyGeometry` holds of every input, by `GeoCl.base trivial`.
- `anyGeometry` occurs in 24 `.lean` files. In particular `geoCl anyGeometry` is supplied four times in
  the proof of `nonempty_hyps_definite_side_of_closed_bound`
  (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44`), which builds the hypothesis bundle
  consumed on the route to `every_character_of_theta_integrals_local_matching` in the same file, and in
  `src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/EveryCharacterE.lean:57–64`.
- `Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean` defines models named `geoDegenerateNoTau`
  (l. 14), `mdlJunk` (l. 147), `geoDegenerate` (l. 241) and `algDegenerate` (l. 390).

- The extraction lemmas `geoOf_surf` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotLamAreShift.lean:30`), `GeoTiedP.geoTied` and
  `GeoTiedP.formsTieX` (`src/Formalism/LocalToGlobal/LatticeGeometry/GeoTiedP.lean:136, 140`) and `degree_value_of_determinant`
  (`src/Formalism/SharpRestriction/Divisibility/PlaceRankTwoOne.lean:349`) each occur exactly once in the source tree, at their own declaration:
  no file applies them. The zero-map divisor datum `divXFl` (`src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean:829`) is used in 3 files,
  and the height formula `hExpl6` in 16.

Harry Tong compiled the pinned release (source commit `753431bf…`) and walked the stored dependency
closures of all five `Main.lean` theorems [Community · E14]. He reports that `anyGeometry`,
`geoDegenerate`, `algDegenerate`, `padDegenerate`, `mdlJunk` and `divXFl` lie in all five closures, that
the four extraction lemmas lie in none, and that the live route runs through
`nonempty_hyps_definite_side_of_closed_bound`, not through `hypsE₂`/`plugAll` as Nielsen first described;
his own conclusion is that reachability of a trivial predicate does not establish that no proof was
supplied. Our source reading agrees on each of these points; we have not rerun his closure walk.

### 16.6.2 Why this does not make the proof invalid `[Expository]`

A Lean proof is invalid only if (i) the theorem proved is not the intended statement, (ii) it depends on
axioms beyond `propext`, `Classical.choice`, `Quot.sound`, or (iii) the kernel accepts an ill-typed term.
Point (i) is settled by Chapter 1 and by the `comparator` / `con-leche --compare` runs; (ii) by
`#print axioms`; (iii) by acceptance in several independent kernels (§16.3.1). The critique addresses
none of the three.

Vacuity points the other way. Instantiating a hypothesis with `True` makes it *easier* to discharge, not
the conclusion false: if a lemma `∀ Γ, H Γ → C` is applied at `Γ := anyGeometry`, then `C` is proved and
the geometric layer simply carried no information. In the polarity language of §18.1.2, a trivial
predicate in hypothesis position is a weakening that the kernel has already accounted for. A vacuous
witness can mislead about *why* `RiemannHypothesis` holds; it cannot make a closed, type-correct term of
type `RiemannHypothesis` fail to prove it.

### 16.6.3 What the critique does establish `[Open]`

1. **Naming does not explain the proof.** The construction is named for a geometric realisation and a
   lattice identification that, along the live route, are degenerate. Any human account that reads the
   proof through those names (for instance a "geometric height" matching a "divisor height") describes a
   structure the formal term does not use.
2. **The content sits elsewhere.** If the geometric side is trivial, the divisor height enters through
   `setDiv`, which sets it equal to its explicit formula, together with separately supplied inequalities
   derived from matrix-norm, covolume and valuation estimates. Identifying and explaining those estimates
   is now the central open task for human understanding of the archive (cf. Chapters 9 and 11).
3. **Audit practice.** Statement fidelity of `Main.lean` (Chapter 1) and of the literature layer
   (Chapters 13, 18) does not cover internal definitions. A complete reading should also flag
   predicates defined as `True`, data defined as copies of other data, and maps defined as zero, and then
   record which conclusions remain non-trivial once they are removed.

### 16.6.4 The "tautology" argument of the final version `[Paper; Nielsen §§8–9]`

The 17-page version of 2026-11-22 (PDF timestamp 18:08 UTC) corrects the route to
`nonempty_hyps_definite_side_of_closed_bound` (§1) and adds a stronger claim (§8, pp. 11–12): with the
geometry `True`, the lattice seed defined as a copy of the row-side data (so `MjAre`, `LamAre` and the
constant match close by `rfl`/`HEq.rfl`), and `setDiv` installing `hExpl6` as the height (so
`div.h u = hExpl6 …` is `rfl`), "the divisor/geometric side and the row/analytic side are definitionally
the same object", the squeeze $\|\text{pairing}\| \le h$, $\mu + h - F_o \le \text{MAIN} + \text{error}$
"compares a quantity with itself", and the kernel has certified only "`RiemannHypothesis =
RiemannHypothesis`".

The three definitional facts are consistent with our reading (§16.6.1). What follows from them must be
stated with care.

*What is established, and on what it rests.* `RiemannHypothesis` is a proposition; a closed term has
that type only if it is a proof of it. So if (a) Mathlib's `RiemannHypothesis` expresses RH (Chapter 1),
(b) the term uses only `propext`, `Classical.choice`, `Quot.sound`, and (c) the kernels that accepted it
are sound, then RH is proved, whatever the internal definitions are called. Definitional unfolding cannot
turn a term of type `RiemannHypothesis` into a proof of something weaker: the kernel checks the type up to
definitional equality, and that type is `RiemannHypothesis`. The phrase "certifies only
`RiemannHypothesis = RiemannHypothesis`" therefore has no precise meaning. Points (b) and (c) rest on
community checks (§16.3.1) that we have not rerun; (a) we have read.

*What the paper would need.* An invalidity claim must locate a failure of (a), (b) or (c). The paper
locates none. Its §9 argument ("a geometric argument cannot be both essential and trivially discharged")
is an argument about the intended strategy: it shows that, on the live route, the geometric layer does
no work. That is compatible with a valid proof whose work is done elsewhere.

*What a first trace shows* `[Lean, read; partial]` (details: `notes/squeeze-trace.md`). After `setDiv`,
both inequalities are fields of `WordFacts` (`src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:128–133`):

```lean
(D.div.Bk u ≠ 0 → htMap … (D.div.Bk u) ≤ D.div.h u) ∧
D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u + C * … + C * … * L.sc.x ^ (Cabs * L.sc.eps)
```

Neither is closed by `rfl` or `le_rfl` on identical sides; both are proved in `divClausesR_of`
(`src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:184–245`) and both are consumed downstream (`frameRealF_of`, `linkCore`).
So "compares a quantity with itself" is not literally correct. Two qualifications:

1. **The lower bound is conditional on `Bk u ≠ 0`.** `exists_divStage`
   (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsDivStage.lean:334`) builds a divisor stage with `Bk := fun _ => 0` and
   `h := fun _ => 0` (l. 347–348); `setDiv` overwrites `h` but not `Bk`. If the live divisor datum descends
   from this construction, the lower bound is vacuous. `[Community-data, checked by us]` In DeDeo's
   `lean4export` dump of the main theorems (`alp-export-main-theorems.ndjson.gz`, sha256-verified; the
   dump ends with `riemannHypothesis`), the name `GlobalTheory.Mem.DivModel.exists_divStage` occurs, as do
   `setDiv`, `hExpl6`, `WordFacts`, `divClausesR_of`, `anyGeometry`, `geoDegenerate` and `divXFl`. An
   export contains only declarations reached from its roots, so `exists_divStage` lies in the
   dependency closure of the headline theorems. Membership does not yet show that the `Bk = 0` datum is
   the one fed to `WordFacts` on the live route; a path from `divClausesR_of` to `exists_divStage` is
   still to be extracted.

   *Path extraction* `[Lean, export graph; run by us on TSUBAME]`. Over the 1,476,753 declarations of the
   export, a breadth-first walk of constant references gives a path of 19 declarations from
   `riemannHypothesis`, through `nonempty_hyps_definite_side_of_closed_bound`,
   `member_exists_baseLattice_alt` and `exists_ext_twisted_places`, to
   `GlobalTheory.Mem.R3.Rw.Second.exists_lt_of_stage`, which calls `exists_divStage`. No path exists from
   `divClausesR_of` or `WordFacts` themselves; this is expected, since both are stated for an arbitrary
   divisor datum, which the caller supplies. In `exists_lt_of_stage`
   (`…/IwasawaDecomposition/ExistsExtTwistedPlaces.lean`) the `Bk = 0` stage `V` is packed, with a row
   datum whose projection `eOp` is set to `0`, into the witness `⟨W', V, S, N, G⟩`. So the degenerate
   divisor stage is part of the live construction. Whether the `D7` passed to `WordFacts` on the live
   route is the one built from this `V` (in which case the lower bound is vacuous) requires following the
   witness from `exists_lt_of_stage` to the call of `divClausesR_of`; that step remains `[Open]`.
2. **The upper bound is non-trivial but one-sided.** Its two sides (`R.hu` and `R.rhs`) are distinct
   expressions, proved from a valuation bound, `L3main` and about 35 record facts; but both are built from
   row-side data, so it relates row-side quantities to each other and does not compare an independent
   geometric height with the main term.

Open: whether `Bk = 0` on the live route; how `geoCl anyGeometry` reaches `DivInputs0R`; the proofs (not
only statements) of `height_chain_atR`, `boundsMu`, `divIneqRecord`; and whether
`zeroFreeOn_of_tiedWin_cyc` uses these inequalities essentially. None of this bears on validity under
(a)–(c); it bears on what the proof actually proves along the way.

**Verdict on this point.** The code observations in Nielsen's paper are largely correct. The inference
in her title does not follow from them: the observations concern the explanatory meaning of internal
definitions, which the kernel checks do not claim to certify, and not the validity of the formal proof
of the stated theorem.
