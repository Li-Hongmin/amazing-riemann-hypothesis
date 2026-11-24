# Chapter 18. Auditing `GlobalTheory.Published`: worked statement-fidelity case studies (`P18`)

> **Status tags used in this chapter:** `[Lean, read]` for `Prop` definitions, helper structures,
> and local bridge proofs read line by line (`R3`) across
> `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean`,
> `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean`,
> `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean`,
> `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean`,
> `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean`,
> `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/QuotRepMk.lean`,
> `src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNormalised.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsPrimitiveRootPow.lean`,
> `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesOfPoitouTate.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/ClozelPurity.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/RegularAlgebraicPurity.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeIsobaric.lean`,
> `src/Development/AutomorphicArithmetic/Foundations/BaseChangeIdentities/Narrow.lean`,
> `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/WeilSiegelFormula.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean`,
> `src/Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean`, and
> `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/DeRhamPotSemistable.lean`;
> `[Lean]` for statement-level inspections (`R2`) of period-ring construction
> `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281`;
> `[Paper]` for published monographs and manuscripts; `[Community]` for public verification and
> named-theorem audit reports; `[Expository]` for mathematical comparisons and worked examples;
> `[Open]` for unread upstream proof cones and the ~70 named literature `Prop`s not yet audited
> line by line.

In Chapters 13 and 16 we surveyed node **P18** — the 257 theorem headers in
`UpperTheory.LiteratureTheorems.*` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215–813`)
that assemble propositions in `GlobalTheory.Published.*` and `UpperTheory.V.Published.*` and discharge
every hypothesis of `OpenLiteratureStatements` on the path to `src/Main.lean` [Lean, read]. We
stressed a foundational principle of formal proof auditing: **Lean's kernel checks logical validity,
not English naming.** For the five top-level theorems of `src/Main.lean`, statement fidelity is
already settled (Chapter 1), because their types mention only vetted Mathlib definitions. Inside the
archive, however, intermediate interfaces carry classical literature names (`GlobalArtinReciprocity`,
`FerreroWashington`, `Kato`, `PoitouTateNormalised`, `BaseChangeDefiniteUnitary`,
`DeRhamPotSemistable`, …). Whether each internal `Prop` states the textbook theorem its name evokes,
a harmless specialization tailored to CM host fields, a weaker corollary that still suffices
downstream, or a vacuous placeholder can only be answered by opening the `.lean` file and comparing
every quantifier, typeclass, and custom structure against the published theorem [Expository].

In this closing chapter of Part IV, we turn that principle into a concrete graduate-level casebook.
We select **three load-bearing sub-clusters** spanning **14 named `Published` declarations** across
class field theory, Iwasawa theory and Galois cohomology, and automorphic / $p$-adic Hodge theory,
read their full `Prop` definitions and surrounding local deduction files line by line (`R3`), test
each against explicit small examples where boundary hypotheses bite, and record a reusable five-step
audit protocol for specialists examining the remaining `[Open]` entries of `P18`.

---

## 18.1 Motivation: logical polarity and how internal `Prop`s can diverge from their names

### 18.1.1 Why `src/Main.lean` remains unconditional while internal names still require auditing

Suppose an archive defines an internal proposition `P_lean : Prop`, proves a theorem `h_prod : P_lean`
in one sub-cone, and proves an implication `h_cons : P_lean → Goal` in another sub-cone, combining
them by modus ponens `h_cons h_prod : Goal` [Expository]. What does kernel verification guarantee,
and what does it *not* guarantee?

1. **Unconditional soundness of `Goal`:** Because `P_lean` is **proved** (not assumed as an `axiom`
   or left as `sorry`), modus ponens `h_cons h_prod` is valid in Lean's logic *even if `P_lean` were
   defined to be `True`*! Indeed, the archive actually contains such a fossil:
   `GlobalTheory.Published.UnusedSlot72 : Prop := True`
   (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`,
   proved by `trivial` in `discrete_spectrum_residual_classification_of_literature`) [Lean, read].
   Because nothing downstream extracts information from `UnusedSlot72`, defining it as `True` does
   not compromise `src/Main.lean` in the slightest.
2. **Why statement-fidelity auditing is nonetheless indispensable:** Human mathematicians cannot
   verify a 17.37-million-line proof by reading all 1,478,243 kernel constants linearly; they verify
   it **modularly**, dividing the argument along classical milestones ("by Artin reciprocity…", "by
   Kato's Euler system…", "by definite unitary base change…"). If an internal milestone `P_lean`
   differs from the published theorem $P_{\mathrm{lit}}$, three distinct phenomena can occur:
   - **Mathematical extraction risk:** A community project hoping to upstream "the archive's proof
     of Theorem X" into Mathlib needs to know whether `P_lean` proves full Theorem X or only a
     special case over CM fields or $\ell$-power conductors.
   - **Architectural misreading risk:** If `P_lean` weakens the conclusion of $P_{\mathrm{lit}}$ (or
     adds an extra hypothesis), a human reader auditing only the downstream file might think Theorem
     X was used in full, whereas an uninspected upstream file might have pushed the hard work into a
     side hypothesis — or conversely, a seemingly alarming omission (such as `Kato` omitting
     $L(f, \chi, r) \neq 0$!) might turn out to be completely sound because a side inequality (`2 * r ≠ k`)
     keeps $(f, \chi, r)$ strictly off the central critical line!
   - **Custom-bundle vacuity risk:** When `P_lean` quantifies over an archive-defined structure
     `∀ B : CustomBundle, Concl B`, `P_lean` is vacuously `True` if `CustomBundle` happens to be
     empty! Auditing fidelity therefore requires checking **non-vacuity** at a genuine consumer or
     instantiation site.

### 18.1.2 Polarity calculus: strengthening vs weakening in hypotheses and conclusions

When comparing a formal proposition $P_{\mathrm{lean}} \equiv (\forall x \in \mathcal D_{\mathrm{lean}},\ H_{\mathrm{lean}}(x) \to C_{\mathrm{lean}}(x))$
against a textbook theorem $P_{\mathrm{lit}} \equiv (\forall x \in \mathcal D_{\mathrm{lit}},\ H_{\mathrm{lit}}(x) \to C_{\mathrm{lit}}(x))$,
keep the **variance (polarity)** of logical implication firmly in view [Expository]:

| Modification in $P_{\mathrm{lean}}$ relative to $P_{\mathrm{lit}}$ | Logical strength of $P_{\mathrm{lean}}$ | Easier to prove upstream? | Harder to use downstream? | Audit verdict category |
|---|---|---|---|---|
| **Domain restriction** ($\mathcal D_{\mathrm{lean}} \subsetneq \mathcal D_{\mathrm{lit}}$, e.g. CM fields only) | Weaker than $P_{\mathrm{lit}}$ ($P_{\mathrm{lit}} \implies P_{\mathrm{lean}}$) | Yes | Requires consumer $x \in \mathcal D_{\mathrm{lean}}$ | **Special case** (sound if consumer lies in $\mathcal D_{\mathrm{lean}}$) |
| **Added / stronger hypothesis** ($H_{\mathrm{lean}} \implies H_{\mathrm{lit}}$, e.g. $\zeta_\ell \in K$ or $E/E^+$ unramified) | Weaker than $P_{\mathrm{lit}}$ | Yes | Consumer must supply $H_{\mathrm{lean}}$ | **Domain-restricted / harmless base hypothesis** |
| **Weakened hypothesis** ($H_{\mathrm{lit}} \implies H_{\mathrm{lean}}$, e.g. `IsAlgPos` on $E_+^\times$ instead of $E^\times$) | **Stronger** than $P_{\mathrm{lit}}$! | Harder! | Strictly easier to apply | **Faithful (slightly stronger)** |
| **Weakened conclusion** ($C_{\mathrm{lit}} \implies C_{\mathrm{lean}}$, e.g. infinitude without natural density) | Weaker than $P_{\mathrm{lit}}$ | Yes | Consumer must only need $C_{\mathrm{lean}}$ | **Safe weakening** |
| **Placeholder / tautology** ($C_{\mathrm{lean}} \equiv \mathrm{True}$) | Trivial | Trivial (`trivial`) | Useless (carries 0 bits) | **`True` fossil** (`UnusedSlot72`) |

Every single row of this polarity table occurs naturally among the 14 declarations we audit below!

---

## 18.2 Cluster I — Class field theory, finite-order Hecke characters, and Chebotarev

### 18.2.1 Motivation: separating proof wrappers from `Prop` definitions

In Chapters 10, 13, and 16 we flagged an easy trap for newcomers navigating the archive: the 17-line
file `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean`
contains definitions such as
`noncomputable def globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity := ...` (`:8`),
`rayClassFieldSt` (`:11`), and `heckeLAdicCharacter` (`:14`). Those three declarations are **not**
the propositions; they are **proof-term wrappers** (`def` witnessing a `Prop`, importing a cone of
`1,015` modules) [Lean, read]! To audit whether the archive's Artin reciprocity, ray class field
existence, Hecke $\ell$-adic character realization, and Chebotarev density statements match
classical class field theory `[Artin1927]`, `[Tate1967]`, `[Neukirch1999]`, `[Tschebotareff1926]`,
we must open the three files where those `Prop`s are actually defined — and read the downstream
deductions that test their interfaces!

### 18.2.2 Worked example: ray classes and Artin reciprocity on $E = \mathbb Q(i)$ modulo $\mathfrak m = (2 + 2i)$

Test the definitions of Cluster I on the Gaussian field $E = \mathbb Q(i)$ ($\mathcal O_E = \mathbb Z[i]$,
class number $1$, totally complex so no real places exist, $E_+^\times = E^\times$) at the modulus
$\mathfrak m = (2 + 2i)$ of norm $N(\mathfrak m) = (2+2i)(2-2i) = 8$ [Expository]:

1. **Local congruence quotient and global units:** Because $2 = -i(1+i)^2$ and $2 + 2i = 2(1+i) = -i(1+i)^3$,
   the ring $\mathcal O_E / \mathfrak m = \mathbb Z[i]/(2+2i)$ has cardinality $8$, and its unit
   group $(\mathcal O_E / \mathfrak m)^\times$ consists of the $4$ classes coprime to $1+i$:
   $$(\mathbb Z[i]/(2+2i))^\times \;=\; \bigl\{\overline{1},\; \overline{i},\; \overline{-1},\; \overline{-i}\bigr\}.$$
   Check the prime above $5$ carefully! Since $(-1 + 2i) - 1 = -2 + 2i = i(2 + 2i) \in \mathfrak m$, we have
   **$-1 + 2i \equiv 1 \pmod{2+2i}$**, whereas $2 + i = (-i)(-1 + 2i) \equiv -i \not\equiv 1 \pmod{2+2i}$!
   Meanwhile, the global unit group $\mathcal O_E^\times = \{\pm 1, \pm i\}$ maps **bijectively**
   onto $\{\overline{1}, \overline{-1}, \overline{i}, \overline{-i}\} = (\mathbb Z[i]/(2+2i))^\times$!
2. **Ray class group $\mathrm{Cl}_{\mathfrak m}(E)$ and Artin map:** By the exact sequence
   $\mathcal O_E^\times \to (\mathcal O_E/\mathfrak m)^\times \to \mathrm{Cl}_{\mathfrak m}(E) \to \mathrm{Cl}(E) = 1$,
   surjectivity of $\mathcal O_E^\times \to (\mathcal O_E/\mathfrak m)^\times$ forces the ray class
   group $\mathrm{Cl}_{(2+2i)}(\mathbb Q(i))$ to be **trivial**! Consequently, the ray class field
   $L_{\mathfrak m}$ of $\mathbb Q(i)$ modulo $(2 + 2i)$ is $E$ itself (`RayClassFieldSt`), whereas
   raising the modulus to $\mathfrak m' = (4)$ ($(\mathbb Z[i]/(4))^\times$ of order $8$, quotient
   by $\{\pm 1, \pm i\}$ of order $2$) cuts out the quadratic ray class field
   $L_{(4)} = \mathbb Q(i, \sqrt{2}) = \mathbb Q(\zeta_8)$!
3. **Uniformizer Frobenius sign convention (`IsGlobalArtin.frob`):** In `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:34–36`,
   for a finite place $v$, a valuation subring $A$ of $\Omega$ over $v$ (`IsPlaceOver A v`) and a local
   uniformizer $\varpi_v \in E_v^\times$ (`IsUnifAt v x`), the Artin map
   $\mathrm{art}_E : \mathbb A_E^\times \to G_E^{\mathrm{ab}}$ sends the single-place idèle
   `localIdele E v x` to `toAb E Ω σ⁻¹`, where `IsFrob A (normV v) σ` says that $\sigma$ lies in the
   decomposition group of $A$ and induces $x \mapsto x^{N(v)}$ on its residue field
   (`src/Formalism/ConjugateSelfDual/Statement.lean:23,28–29`). Thus **uniformizers map to geometric Frobenius $\mathrm{Frob}_v^{\mathrm{geom}} = (\mathrm{Frob}_v^{\mathrm{arith}})^{-1}$**
   — matching Deligne's convention `[Tate1967]` and the algebraic Hecke character package `HeckeLAdicCharacter`!

### 18.2.3 Exact Lean definitions and verbatim literature comparison (Cluster I)

**Definition 18.1 (Cluster I `Published` propositions).** [Lean]

1. **`GlobalTheory.Published.GlobalArtinReciprocity` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70–72`, cone `9`):**
   $$\forall (E : \mathrm{Type})\,[\mathrm{Field}\,E]\,[\mathrm{NumberField}\,E]\,(\Omega : \mathrm{Type})\,[\mathrm{Field}\,\Omega]\,[\mathrm{Algebra}\,E\,\Omega]\,[\mathrm{IsAlgClosure}\,E\,\Omega],\;
   \exists\,\mathrm{art} : \mathrm{Ideles}\,E \to_* \mathrm{Gab}\,E\,\Omega,\; \mathrm{IsGlobalArtin}\,\mathrm{art},$$
   where `Gab E Ω` is the topological abelianization of $G_E=\mathrm{Gal}(\Omega/E)$ (`:15`) and
   `IsGlobalArtin art` (`:25–39`) bundles five fields. In the last three, $v$ is a finite place and
   $A$ is a valuation subring of $\Omega$ lying over $v$ (`IsPlaceOver A v`):
   - `quot : IsOpenQuotientMap art` (continuous open surjection $\mathbb A_E^\times \twoheadrightarrow G_E^{\mathrm{ab}}$, where $G_E^{\mathrm{ab}} = G_E / \overline{[G_E, G_E]}$ carries the quotient Krull topology);
   - `ker : art.ker = ((diagUnits E).range ⊔ infConn E).topologicalClosure` (kernel equals the closure of $E^\times \cdot (E_\infty^\times)^\circ$ inside $\mathbb A_E^\times$);
   - `ine` (the image of the local units $\mathcal O_v^\times$ under $\mathrm{art}\circ\iota_v$ **equals** the image of the inertia group of $A$ in $G_E^{\mathrm{ab}}$; no closure is taken);
   - `frob` (the images of the local uniformizers $\varpi_v$ are **exactly** the elements $\mathrm{toAb}(\sigma^{-1})$ with $\sigma$ an arithmetic Frobenius at $A$; this is an `↔` for each $g$);
   - `dec` (the topological closure of the image of $E_v^\times$ **equals** the image of the decomposition group of $A$).
2. **`GlobalTheory.Published.HeckeLAdicCharacter` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:74–78`, cone `9`):**
   For every $E$ and algebraic closure $\Omega$ **there exists** an Artin map `art` with
   `IsGlobalArtin art` such that for every prime $\ell$, comparison isomorphism
   $\iota : \overline{\mathbb Q}_\ell \simeq \mathbb C$, Hecke character $\chi$ and infinity type $n$
   with `IsAlgPos χ n` (`:41–42`), there exists a **unique** continuous
   $r : G_E \to (\overline{\mathbb Q}_\ell)^\times$ satisfying `IsLAdicOf art ι χ n r` (`:57–60`).
   The quantifier order is $\forall E\,\Omega,\ \exists\,\mathrm{art},\ \ldots$; the statement does
   not apply to an arbitrary Artin map. `IsLAdicOf` is a relation on all of `Ideles E`: whenever
   $\mathrm{art}(x)=\mathrm{toAb}(\sigma)$, the value $r(\sigma)$ is $\iota^{-1}$ of $\chi(x)$ corrected
   by the archimedean and $\ell$-adic power factors `infPow n x` and `lPow ι n x`. Frobenius values at
   unramified places prime to $\ell$ are a consequence (`IsLAdicOf.frob_unr`, `:296–301`, which also
   uses the `frob` field of `IsGlobalArtin`).
3. **`GlobalTheory.Published.RayClassFieldSt` & `RayClassFieldMaximalSt` (`src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:17,32`, cone `686`):**
   `RayClassFieldSt` is defined as `GlobalTheory.NT.RayField`
   (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LFunctionPositiveConductorFourEight.lean:84–92`):
   for every number field $K$ and nonzero ideal $\mathfrak m$ there is a finite abelian $L/K$,
   unramified at every prime not dividing $\mathfrak m$, whose Frobenius elements at those primes
   generate $\mathrm{Gal}(L/K)$, and such that a nonzero ideal $I$ prime to $\mathfrak m$ has trivial
   value under every character of $\mathrm{Gal}(L/K)$ exactly when $I$ lies in the ray modulo
   $\mathfrak m$. The Artin-isomorphism formulation is the proved equivalent form at `:19–25`.
   In `RayClassFieldMaximalSt` (`:32–36`), $L$ is a field with `IsRay L 𝔪` and
   every candidate finite abelian $L'/K$ must satisfy
   `∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, IsModulus L' χ 𝔪`. Under this character-by-character conductor
   hypothesis, the conclusion is `Nonempty (L' →ₐ[K] L)`.
4. **`GlobalTheory.Published.ChebotarevDegreeOne` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:12–18`, cone `211`):**
   For every number field $F$, finite Galois extension $L/F$, element $\sigma \in \operatorname{Gal}(L/F)$,
   and finite set $S$ of maximal ideals of $\mathcal O_F$, there exists a maximal ideal $v \notin S$
   unramified in $L$ of **absolute inertia degree $1$** ($\mathrm{absNorm}(v) = p$ prime, i.e.
   $\mathcal O_F / v \cong \mathbb F_p$) whose Frobenius conjugacy class in $\operatorname{Gal}(L/F)$
   contains $\sigma$.

| Lean `Prop` | Classical source | Word-for-word comparison (hypotheses & conclusion) | Verdict |
|---|---|---|---|
| `GlobalArtinReciprocity` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70`) | Artin `[Artin1927]`; Tate `[Tate1967]`; Neukirch `[Neukirch1999, Thm. VI.6.1]` | Matches idèlic Artin reciprocity over **every** number field $E$: open quotient $\mathbb A_E^\times \twoheadrightarrow G_E^{\mathrm{ab}}$, exact kernel $\overline{E^\times (E_\infty^\times)^\circ}$, image of inertia $= \mathrm{art}(\mathcal O_v^\times)$, uniformizer $\mapsto \mathrm{Frob}_v^{\mathrm{geom}}$, image of decomposition $= \overline{\mathrm{art}(E_v^\times)}$. (Tate's fuller isomorphism $\pi_0(C_E) \xrightarrow{\sim} G_E^{\mathrm{ab}}$ is equivalent because $C_E^\circ = \overline{E^\times (E_\infty^\times)^\circ} / E^\times$.) | **Faithful** (`[Lean, read]` for `Prop`; `1,015`-module proof cone `[Open]`) |
| `HeckeLAdicCharacter` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:74`) | Weil (1956) $A_0$-type algebraic Hecke characters; Serre (1968) | Hypothesis `χ.IsAlgPos n` requires algebraic infinity-type only on **totally positive** $k \in E_+^\times$ (`IsTotallyPositive k`), which is *weaker* in hypothesis (hence **slightly stronger** as a theorem!) than requiring all $k \in E^\times$ (`isAlgPos_of_isAlg`, `:86`). The Artin map is existentially quantified together with the statement, and the compatibility is the idèlic relation `IsLAdicOf`; unramified Frobenius values away from $\ell$ follow from it (`IsLAdicOf.frob_unr`, `:296–301`). | **Faithful** (`[Lean]` for the `Prop`, as in Def. 18.1; `[Lean, read]` for the finite-order bridge, Lemma 18.1(1)) |
| `RayClassFieldSt` & `RayClassFieldMaximalSt` (`src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:17,32`) | Takagi (1920); Neukirch `[Neukirch1999, Thm. VI.6.2]` | Uses narrow ray class group `RayClassGroup 𝔪` (totally positive principal generators at all real places, `:149`). `RayClassFieldMaximalSt` is **proved outright in the same file**: `rayClassFieldMaximalSt_holds : RayClassFieldMaximalSt` (`:204–225`) has no hypotheses, and its Frobenius-closure input `closure_isFrob_eq_top` (`:118–139`) comes from a zeta-pole argument on pairs of primes, not from `RayClassFieldSt` or `ChebotarevDegreeOne`. | **Faithful** (narrow real-place convention; `[Lean, read]`) |
| `ChebotarevDegreeOne` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:12`) | Chebotarev `[Tschebotareff1926]`; Neukirch `[Neukirch1999, Thm. VII.13.4]` | Asserts **existential infinitude** (avoiding any finite $S$) of unramified degree-one primes hitting the conjugacy class of $\sigma$, omitting natural/Dirichlet density $\lvert C \rvert / \lvert G \rvert$ (density 1 of degree-one primes makes the existential form true; proved in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean:17–64`!). | **Safe weakening** (existential, no density value; suffices for `dense` & `eq_of_frob` `[Lean, read]`) |

### 18.2.4 Fidelity lemma and line-by-line `R3` proofs (Cluster I)

**Lemma 18.1 (Cluster I internal deductions verifying non-vacuity and strength).** [Lean, read]

1. *(Finite-order Galois–Hecke correspondence: `exists_unique_hchar_of_finite_order`, `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:381–418`, and `HeckeLAdicCharacter.full`, `:466–491`)*
   *(a) Let `art` satisfy `IsGlobalArtin art`. For every prime $\ell$, $\iota : \overline{\mathbb Q}_\ell \simeq \mathbb C$, $m \ge 1$ and continuous $r : G_E \to_* (\overline{\mathbb Q}_\ell)^\times$ with $r^m = 1$, there is a unique Hecke character $\chi$ with `χ.OrderDvd m` and `IsLAdicOf art ι χ 0 r`. This direction uses only `IsGlobalArtin`.*
   *(b) Assume `H : HeckeLAdicCharacter` and let `art` be the Artin map that `H` supplies. Then every $\chi$ with `χ.OrderDvd m` has a unique continuous $r$ with $r^m = 1$ and `IsLAdicOf art ι χ 0 r`. This direction uses `H`.*
   *For the Artin map of `H`, (a) and (b) together make `IsLAdicOf art ι · 0 ·` a bijection between continuous characters $r$ with $r^m=1$ and Hecke characters of order dividing $m$. The relation is the idèlic relation `IsLAdicOf … 0` at infinity type zero, which reads $r(\sigma)=\iota^{-1}(\chi(x))$ whenever $\mathrm{art}(x)=\mathrm{toAb}(\sigma)$; it is not a Frobenius relation.*
2. *(Topological Frobenius density from `ChebotarevDegreeOne`, and unconditional ray class field maximality: `ChebotarevDegreeOne.dense` and `eq_of_frob`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:51–68`, and `rayClassFieldMaximalSt_holds`, `src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:204–225`)*
   *Existential `ChebotarevDegreeOne` implies that unramified Frobenius elements are topologically dense in $G_F = \operatorname{Gal}(\Omega/F)$ and that two continuous representations $G_F \to_* M$ into any $T_2$ group agreeing on Frobenius outside $S$ are identical. Separately, `rayClassFieldMaximalSt_holds : RayClassFieldMaximalSt` holds with no hypotheses.*

*Proof.*
(1)(a) In `exists_unique_hchar_of_finite_order` (`:381–418`), the continuous $r$ factors through
the abelianization as `liftAb r hr` (`:319–323`), and $\psi := \mathrm{liftAb}(r)\circ\mathrm{art}$
is continuous with $\psi^m=1$ (`:384–390`). By `isOpen_ker_of_pow` (`:363–372`) its kernel is
open, so $\chi_0 := \iota\circ\psi$ has open kernel and is continuous (`continuous_of_isOpen_ker'`,
`:374–379`). It is trivial on $E^\times$ because the diagonal units lie in $\ker\mathrm{art}$ by the
`ker` field (`:396–401`). The relation `IsLAdicOf art ι χ₀ 0 r` holds because `infPow 0` and
`lPow ι 0` are identically $1$ (`infPow_zero`, `lPow_zero`, `:191–195`) and
`liftAb r (toAb σ) = r σ` (`:326–327`); see `:407–410`. For uniqueness, take $\chi$ with the same
relation, write $\mathrm{art}(x)=\mathrm{toAb}(\tau)$ via `toAb_surjective` (`:236`), and compare the
two values at $\tau$ (`:411–418`).
(1)(b) In `HeckeLAdicCharacter.full` (`:466–491`), the converse branch obtains $r$ from `H` at
infinity type $0$ (`:489`), using `isAlgPos_zero_of_orderDvd` (`:420–444`) to verify the
algebraicity premise for a character of finite order. Then `IsLAdicOf.pow_eq_one` (`:446–454`)
and surjectivity of `art` give $r^m=1$, and `IsLAdicOf.unique` (`:243–247`) gives uniqueness
(`:490–491`). The other branch (`:484`) is exactly (a).

(2) In `ChebotarevDegreeOne.dense` (`:51–61`), every open $U \subseteq G_F$ in the Krull topology
contains a coset $\tau \cdot \ker(\mathrm{res}_{L/F})$ for some finite Galois $L/F$ (`isTopologicalBasis_krull`).
Applying `ChebotarevDegreeOne` to $L/F$ and $\sigma = \mathrm{res}_{L/F}(\tau)$ produces $v \notin S$
and $\rho \in D_v$ with $\mathrm{res}_{L/F}(\rho) = \mathrm{res}_{L/F}(\tau)$, so $\rho \in U$!
Two continuous maps into a Hausdorff group agreeing on a dense set are equal (`eq_of_frob`, `:63–68`).
In `rayClassFieldMaximalSt_holds` (`src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:204–225`), given a ray class
field $L/K$ modulo $\mathfrak m$ and an abelian $L'/K$ satisfying the characterwise modulus
hypothesis, the proof embeds both in a compositum $M$ inside an algebraic closure of $K$
(`:206–222`) and applies `range_le` (`:141–198`) with the input
`closure_isFrob_eq_top M hm` (`:223`). The latter (`:118–139`) shows that Frobenius elements at
primes prime to $\mathfrak m$ generate $\mathrm{Gal}(M/K)$. It argues by contradiction: from a
nontrivial $\sigma$ (`:123`), `exists_two_primes_of_isFrob_one` produces two distinct primes above
each prime outside a finite set (`:124–126`), and the zeta-pole lemma
`ZetaPole.not_injective_double_primes` rules this out (`:130–139`). These two lemmas are used at
statement level here [Lean]. No `RayClassFieldSt` or `ChebotarevDegreeOne` hypothesis enters. `range_le` compares restrictions of Frobenius using the ray class and modulus conditions
and passes to the required inclusion of ranges. This gives the $K$-algebra embedding.

---

## 18.3 Cluster II — Iwasawa theory, $p$-adic $L$-values, Kato's Euler system, and Poitou–Tate duality

### 18.3.1 Motivation: where $p$-adic and cohomological edge hypotheses hide

Cluster II audits five `Published` declarations powering Chapters 10 and 11 (`P11` and `P12` `VWin`):
`FerreroWashington`, `SiegelKlingen` / `DeligneRibet`, `Kato`, and `PoitouTateNormalised` /
`PoitouTateDuality`. In algebraic number theory, every one of these theorems has notorious edge cases:
$\ell = 2$ vs odd $\ell$, real archimedean places where $H^2(\mathbb R, \mu_2) \neq 0$, the denominator
$\frac{1}{12}$ of $\zeta(-1)$ before Deligne–Ribet smoothing, and central vs off-center critical points
of modular $L$-functions! Reading the five files at `R3` shows that the archive navigated all four
edge cases explicitly — and in `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean:223–245`, even included an internal
machine-checked `example` sanity-checking its own smoothing formula at $s = -1$!

### 18.3.2 Worked examples: Deligne–Ribet smoothing at $\zeta_{\{2\}}(-1) = \frac{1}{12}$ and the $\ell = 2$ real-place obstruction

For $F=\mathbb Q$, $\ell=2$, $n=1$, $k=2$, $\varepsilon=1$ and $\mathfrak c=(3)$,
the modulus is $(2)$. The example computes the ray value
$(1-2)\zeta(-1)=1/12$ at $1-k=-1$. Its $2$-adic norm is $4$, so the unsmoothed value fails
`InZl`. Translation fixes the constant function and smoothing gives
$1/12-3^2/12=-2/3$, of $2$-adic norm $1/2$. This is an explicit counterexample to
unshifted integrality. [Lean, read] See
`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean:223–245`.

For Poitou–Tate, $F=\mathbb Q$ and $\ell=2$ fail the guard `l ≠ 2 ∨ IsTotallyComplex F`.
The real Galois group has order two, so its Tate cohomology with trivial $\mathbb F_2$
coefficients is nonzero. A totally complex field such as $\mathbb Q(i)$ satisfies the guard
even at $\ell=2$. [Expository]

### 18.3.3 Exact Lean definitions and verbatim literature comparison (Cluster II)

**Definition 18.2 (Cluster II interfaces).**

1. **`UpperTheory.V.Published.FerreroWashington`.** For every prime $\ell$ and abelian number
   field $K/\mathbb Q$ that contains a primitive root of unity of order $4$ if $\ell=2$ and of
   order $\ell$ otherwise (the premise `(∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l)) →`,
   `:9`), there exists $r\in\mathbb N$ such that for every $n\in\mathbb N$ and every
   cyclotomic extension $K'/K$ of order $\ell^n$ in the sense of `IsCyclotomicExtension {l ^ n} K K'`,
   the class group $A=\mathrm{Cl}(\mathcal O_{K'})$ satisfies $|A/A^\ell|\le\ell^r$.
   The universal tower-level quantifier follows the existential bound. There is no localization
   premise. The root-of-unity premise is present in the statement, but the archive's proof
   `UpperTheory.V.FW.ferreroWashington` introduces it anonymously in `intro l _ K _ _ _ _` and never
   uses it, so the same argument bounds every abelian $K$
   (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104–106`).
   This is a bounded mod-$\ell$ rank formulation of a consequence of the classical $\mu=0$ theorem
   [FerreroWashington1979]. [Lean]
   See `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:7–11`.
2. **`GlobalTheory.Published.SiegelKlingen`, `DeligneRibet` and `SiegelKlingenDeligneRibet`.**
   Siegel–Klingen provides a continuation with rational values at $1-k$ for $k\ge1$,
   over totally real fields and nonzero moduli, for rational-valued ray functions.
   Deligne–Ribet uses $\mathfrak f=(\ell^n)$ with $n\ge1$. For every ray function $\varepsilon$
   whose values on ideals coprime to $\mathfrak f$ are in $\mathbb Z_{(\ell)}$ and every
   $\mathfrak c$ coprime to $\mathfrak f$, it takes two rational values as premises.
   `IsRayValue` at $1-k$ specifies $a$ for $\varepsilon$ and $a'$ for
   `translate` by $\mathfrak c$, the function $I\mapsto\varepsilon(\mathfrak c I)$.
   The conclusion is `InZl` for $a-N(\mathfrak c)^k a'$. The combined declaration is a conjunction.
   The integrality interface specializes the modulus and the smoothing test of [DeligneRibet1980].
   [Lean] See `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean:14–32`
   and `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean:40–52`.
3. **`UpperTheory.V.Published.Kato`.** For every weight $k\ge2$, `Newform k`, prime $\ell$,
   algebraic closure of $\mathbb Q$, and comparison isomorphism $\iota$, the declaration asserts
   finite dimensionality of `coefField g ι` and existence of a continuous two-dimensional
   representation $V$ over it satisfying `g.Att ι (toBar V)`. This same $V$ must give finite
   `Sel` after cyclotomic twist by $r$ and restriction to every abelian $K/\mathbb Q$ in
   the closure, for every $1\le r\le k-1$ with $2r\ne k$ and every `IsLat` lattice for the twist.
   `IsLat` includes stability. `Sel` uses the quotient by this lattice and the away, above and
   archimedean conditions in `IsSel`. The prime quantifier includes $2$, and residual irreducibility
   is absent. Off-center critical twists restrict the conclusion's domain. A full comparison of
   the attachment and local conditions with [Kato2004, Thm. 14.2] remains [Open]. [Lean]
   See `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/QuotRepMk.lean:27–38`,
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/QuotRepMk.lean:44–59`
   and `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/QuotRepMk.lean:65–73`.

4. **`GlobalTheory.Published.PoitouTateNormalised` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNormalised.lean:12–28`, cone `11`) & `PoitouTateDuality` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsPrimitiveRootPow.lean:13–27`, cone `10`):**
   For any number field $F$, prime $\ell$ with **`l ≠ 2 ∨ IsTotallyComplex F`**, finite set $S$
   containing all primes above $\ell$, $r \ge 1$, and finite continuous $G_{F,S}$-module $M$ killed by
   $\ell^r$ (`∀ m : M, (l ^ r) • m = 0`), with dual $M' := \operatorname{Hom}_{\mathbb Z/\ell^r\mathbb Z}(M, \mu_{\ell^r}(F_{S,\mathrm{max}}))$
   (`DualMod`), there exists a $9$-term exact sequence
   $$0 \to H^0(G_{F,S}, M) \to \prod_{v \in S} H^0(G_v, M) \to H^2(G_{F,S}, M')^\vee \to H^1(G_{F,S}, M) \to \prod_{v \in S} H^1(G_v, M) \to H^1(G_{F,S}, M')^\vee \to H^2(G_{F,S}, M) \to \prod_{v \in S} H^2(G_v, M) \to H^0(G_{F,S}, M')^\vee \to 0$$
   whose three middle/boundary restriction maps (`f1`, `f4`, `f7`) coincide definitionally (`Normalized9`)
   with standard `resProd`!

### 18.3.4 Fidelity lemma and line-by-line `R3` proofs (Cluster II)

**Lemma 18.2 (Cluster II consumer alignment and Greenberg–Wiles cancellation).**

1. **Off-center non-vanishing.** In the classical normalization, either $r$ or $k-r$ is at least
   $(k+1)/2$ when $2r\ne k$. Absolute Euler-product convergence handles the strict inequality,
   boundary non-vanishing handles equality, and the functional equation transfers the result
   at $k-r$ to $r$. This addresses the non-vanishing premise raised in the community discussion.
   `KatoUse` is a separate `Prop`. It assumes $\ell\ne2$, odd weight $2e+1$ with $e\ge1$,
   continuity, an attachment for the inverse cyclotomic twist of $W$, and `KillsMu M φ`
   with $M\ge1$. It concludes `BlochKatoSelmerVanishes` for the twist of $W$ by $\varphi$.
   This records the consumer interface [Lean]. See
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:13–17`.

2. *(Global cohomological dimension $2$ and Greenberg–Wiles formula from `PoitouTateNormalised`: `cohDimTwoGlobal`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsPrimitiveRootPow.lean:70–85`, and `greenbergWiles_of_poitouTate`, `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesOfPoitouTate.lean:45–106`)*
   *`PoitouTateNormalised` implies the Greenberg–Wiles Euler-characteristic identity `[Wiles1995, Prop. 1.6]` for every finite $G_{F,S}$-module $M$ (`l ≠ 2 ∨ IsTotallyComplex F`) and local Selmer conditions $\mathcal L_v \le H^1(G_v, M)$ with orthogonal complements $\mathcal L_v^\perp \le H^1(G_v, M')$ ($\lvert \mathcal L_v \rvert \cdot \lvert \mathcal L_v^\perp \rvert = \lvert H^1(G_v, M) \rvert$):*
   $$\lvert H^1_{\mathcal L}(G_{F,S}, M) \rvert \cdot \lvert H^0(G_{F,S}, M') \rvert \cdot \prod_{v \in S} \lvert \mathcal L_v \rvert
   \;=\;
   \lvert H^1_{\mathcal L^\perp}(G_{F,S}, M') \rvert \cdot \lvert H^0(G_{F,S}, M) \rvert \cdot \prod_{v \in S} \lvert H^0(G_v, M) \rvert.$$

*Proof.*
(2) Open `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesOfPoitouTate.lean:45–106` [Lean, read]. Let $Q := \prod_{v \in S} H^1(G_v, M)$
and $L := \prod_{v \in S} \mathcal L_v \le Q$. Applying `PoitouTateNormalised` (`:65`) gives the
normalized $9$-term exact sequence (`f1`..`f8`). Splitting the exact sequence at $H^1(G_{F,S}, M) \xrightarrow{f_4} Q \xrightarrow{f_5} H^1(G_{F,S}, M')^\vee$,
the global Selmer group is $H^1_{\mathcal L}(G_{F,S}, M) = f_4^{-1}(L)$, while by local Tate duality
and Pontryagin orthogonality (`dualSel_card`, `:80`), $\lvert H^1_{\mathcal L^\perp}(G_{F,S}, M') \rvert$
equals the cardinality of the quotient of $H^1(G_{F,S}, M')^\vee$ by $f_5(L)$, i.e. $\lvert H^1(G_{F,S}, M')^\vee \rvert / \lvert f_5(L) \rvert$
times $\lvert \ker(f_5\rvert_L) \cap \dots \rvert$ — more precisely, `ker_f5_inter` (`:82`) identifies
$L \cap \ker f_5 = L \cap \operatorname{im} f_4$, so the first isomorphism theorem on $f_4 : H^1_{\mathcal L} \to L \cap \operatorname{im} f_4$
and $f_5\rvert_L : L \to f_5(L)$ gives
$$\lvert H^1_{\mathcal L} \rvert = \lvert \ker f_4 \rvert \cdot \lvert L \cap \operatorname{im} f_4 \rvert,
\qquad
\lvert L \rvert = \lvert L \cap \operatorname{im} f_4 \rvert \cdot \lvert f_5(L) \rvert.$$
Substituting the alternating Euler-characteristic relations along `f1`..`f8` (`exact_head`, `exact_tail`,
`:74–78`) reduces the entire proof to the 14-line natural-number cancellation lemma `arith` (`:21–34`),
closed by `nlinarith`! $\square$


### 18.3.7 Local Euler characteristics away from the residue prime

**Motivation.** At a finite place $v$, the unramified local condition has the same order as $H^0$ of the coefficient module. To count its annihilator one also needs the order of the ambient $H^1$. The local Euler formula supplies that order from $H^0$ and $H^2$. We will see exactly which two Frobenius endomorphisms enter the count. The calculation also applies when the coefficient module is ramified.

Fix a non-Archimedean local field $K$, with ring of integers $\mathcal O_K$, residue characteristic $p$ and residue field of order $q$. Write $G_K$ for its absolute Galois group, $I$ for inertia and $\Gamma=G_K/I$ for the Galois group of the residue field. Let $\phi$ be arithmetic Frobenius, acting on the algebraic closure of the residue field by $x\mapsto x^q$. Fix a prime $\ell\ne p$ and a finite discrete continuous $G_K$-module $M$ killed by $N=\ell^r$, with $r\ge 1$. We write $H^i(K,M)=H^i_{\mathrm{cts}}(G_K,M)$.

**First example — a trivial module.** Take $K=\mathbb Q_5$ and $M=\mathbb F_3$ with trivial action. The invariant group is $\mathbb F_3$. The unramified degree-one classes are all determined by an arbitrary value on $\phi$, so they form a copy of $\mathbb F_3$. The only part of inertia contributing to degree one is the pro-$3$ tame factor, generated topologically by $\tau$. An inertia character $c$ is determined by $x=c(\tau)$. Frobenius acts on this value by $5^{-1}x=2x$ in $\mathbb F_3$, since $\phi^{-1}\tau\phi=\tau^{5^{-1}}$ on that factor. Both the fixed group and the quotient by $2-1$ are zero. The two-column calculation below therefore gives $H^1(K,M)=\mathbb F_3$ and $H^2(K,M)=0$. In order notation the answer is $(3,3,1)$, where the zero group has order one. In particular $3=3\cdot 1$.

**Second example — a nontrivial Frobenius action.** Keep $K=\mathbb Q_5$ and $\ell=3$, and let $M=\mathbb F_3 e_1\oplus\mathbb F_3 e_2$ be unramified with Frobenius matrix $A=\operatorname{diag}(1,-1)$. This action factors through the unramified quotient of order two. On $M$, the matrix $A-1$ has kernel $\mathbb F_3 e_1$ and image $\mathbb F_3 e_2$, so the unramified classes form $\mathbb F_3\overline e_1$. Evaluation on $\tau$ identifies the inertia cohomology with $M$, now with Frobenius $5^{-1}A=\operatorname{diag}(-1,1)$. Its fixed group is $\mathbb F_3 e_2$ and its coinvariants are $\mathbb F_3\overline e_2$. The degree-one short exact sequence below has two one-dimensional terms, so $H^1(K,M)\simeq\mathbb F_3^2$. The degree-two group is $\mathbb F_3\overline e_2$, from the inertia coinvariants. The orders are $(3,9,3)$, giving $9=3\cdot3$. On the cyclotomic dual $M^D=\operatorname{Hom}(M,\mu_3)$, Frobenius is $5 A^{-t}=\operatorname{diag}(-1,1)$. Thus the unramified classes on the dual side also have order three, represented by $\overline e_2^\vee$ in its Frobenius coinvariants.

**Definition.** For a finite $\Gamma$-module $B$ write $B^\phi=\ker(\phi-1)$ and $B_\phi=B/(\phi-1)B$. The multiplicative Euler characteristic is $\chi(K,M)=|H^0(K,M)|\,|H^2(K,M)|/|H^1(K,M)|$ when these groups are finite and higher groups vanish. Denote the unramified subgroup by $U(M)=\ker(H^1(K,M)\to H^1(I,M))$.

**Lemma (the two inertia rows).** Put $D=M^I$ and $C=H^1(I,M)$, with their natural $\Gamma$-actions. Both are finite. There are canonical identifications and an exact sequence
$$
H^0(K,M)=D^\phi,\qquad
0\longrightarrow D_\phi\longrightarrow H^1(K,M)\longrightarrow C^\phi\longrightarrow0,\qquad
H^2(K,M)\simeq C_\phi.
$$
In particular $H^i(K,M)=0$ for $i>2$, $U(M)\simeq D_\phi$ and $\chi(K,M)=1$.

**Proof.** Let $P$ be wild inertia. The local ramification structure gives a normal pro-$p$ subgroup $P$ of $I$ and $I/P\simeq\prod_{s\ne p}\mathbb Z_s(1)$, with $s$ running over primes. Write $J$ for the kernel of projection of $I/P$ onto its $\ell$-factor $T_\ell=\mathbb Z_\ell(1)$. The notation $(1)$ records Frobenius conjugation by $q$. Indeed the tame character records the ratio of a conjugate of a prime-to-$p$ root of a uniformizer to that root over the maximal unramified field. Conjugation by a lift of Frobenius acts on these ratios by their $q$-th power. For the subgroup structure and continuous cohomology argument see [Milne, *Arithmetic Duality Theorems*, I, Lemma 2.9, pp. 31–32](https://www.jmilne.org/math/Books/ADTnot.pdf).

The higher continuous cohomology of $P$ on $M$ vanishes by averaging over finite $p$-group quotients. The same argument kills higher cohomology of $J$ on $M^P$, since the orders of its finite quotients are prime to $\ell$. In both cases continuous cohomology is computed by passing to the direct limit of finite quotients with the corresponding fixed coefficients. Inflation and Hochschild–Serre therefore give
$$
H^j(I,M)\simeq H^j(T_\ell,B),\qquad B=(M^P)^J.
$$
The procyclic group $T_\ell$ has $\ell$-cohomological dimension one. For a generator $\tau$, its degree-zero and degree-one cohomology are the kernel and cokernel of $\tau-1$ on $B$. The analogous formulas hold for $\Gamma\simeq\widehat{\mathbb Z}$ with generator $\phi$. These formulas follow from the length-one completed group-ring resolution for $\mathbb Z_\ell$, whose differential is multiplication by a generator minus one. For $\widehat{\mathbb Z}$, first take exact invariants for its prime-to-$\ell$ factor, then apply the resolution on the $\ell$-factor. Averaging over the finite image of the prime-to-$\ell$ factor splits off its fixed part. A $\phi$-fixed element of the complementary summand is fixed by the whole group by topological generation, hence vanishes. Therefore $\phi-1$ is a bijection on the finite complementary summand. This recovers the kernel and cokernel on the original module. In particular $D$ and $C$ are finite, even if wild inertia acts nontrivially on $M$.

In the Hochschild–Serre spectral sequence for $I\triangleleft G_K$, only rows of inertia degrees zero and one and columns of residue degrees zero and one can survive. The edge maps give the displayed short exact sequence in degree one and the single graded term in degree two. The same cohomological-dimension bounds apply to discrete $\ell$-primary torsion coefficients, giving $\operatorname{cd}_\ell(G_K)\le 2$. Equality follows by taking $M=\mu_\ell$: inertia acts trivially, and on $C=\operatorname{Hom}_{\mathrm{cts}}(T_\ell,\mu_\ell)$ the two $q$-actions cancel, giving $H^2(K,\mu_\ell)$ of order $\ell$.

For any finite $B$, the kernel and cokernel of $\phi-1$ have the same order, by counting its image. Apply this first to $D$, then to $C$. The degree-one sequence yields $|H^1(K,M)|=|D_\phi|\,|C^\phi|=|H^0(K,M)|\,|H^2(K,M)|$. $\square$

**Remark (what the twist requires).** For unramified $M$, $D=M$ and $C=\operatorname{Hom}_{\mathrm{cts}}(T_\ell,M)$ with $\phi(c)(t)=\phi(c(\phi^{-1}t\phi))$. Under evaluation on a generator of $T_\ell$, the resulting matrix is $q^{-1}A$ if $A$ is the matrix on $M$. For a ramified module one instead uses the induced conjugation action on $H^1(I,M)$. In either case $M^D$ uses $\mu_N(K^{\mathrm{sep}})$ with its Galois action. Because $p\nmid N$, the roots of $X^N-1$ in the residue algebraic closure are simple and lift uniquely by Hensel's lemma in finite unramified extensions. Thus inertia acts trivially on $\mu_N$ and Frobenius acts by $q$. A generator identifies $\mu_N$ additively with $\mathbb Z/N\mathbb Z$. The action in those coordinates is cyclotomic and is trivial over $K$ precisely when $q\equiv1\bmod N$. In particular an unramified $M$ has an unramified dual, without requiring the roots to lie in $K$ or $M$ to be free over $\mathbb Z/N\mathbb Z$.

**The residue-prime term.** [Paper] The local Euler–Poincaré theorem for a non-Archimedean local field $K$ and a finite discrete continuous $G_K$-module $A$ of order $m$ whose image in $K$ is nonzero gives finite cohomology, vanishing above degree two, and
$$
\frac{|H^0(K,A)|\,|H^2(K,A)|}{|H^1(K,A)|}
=\frac{1}{|\mathcal O_K/m\mathcal O_K|}.
$$
Here $K^{\mathrm{sep}}$ is a separable closure and the cohomology is continuous. Milne states the order formula in Theorem 2.8 and sets out the finiteness and vanishing used in it immediately before that theorem. In the archive $K$ is a finite extension of $\mathbb Q_p$, its separable closure is modeled by the algebraic closure of $\mathbb Q_p$, and $A$ is the finite discrete integral representation obtained from the given action. Its order is $\ell^a$ for some $a\ge 0$ and maps to a nonzero element by characteristic zero. For $p\ne\ell$, $m$ is a unit and the quotient has order one. For $p=\ell$, with $d=[K:\mathbb Q_\ell]$, the free $\mathbb Z_\ell$-module $\mathcal O_K$ has rank $d$, so the quotient has order $\ell^{ad}=|A|^d$. Consequently the equation for $|H^1|$ gains the factor $|A|^d$. The wild-inertia averaging argument above is specific to $p\ne\ell$. In equal characteristic $p$ the theorem as stated excludes nonzero modules of $p$-power order greater than one. [Milne, *Arithmetic Duality Theorems*, I, Theorem 2.8, pp. 31–34](https://www.jmilne.org/math/Books/ADTnot.pdf).

**How the archive supplies the formula.** [Lean, read] The references below are relative to archive A2, joined SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. The proof above is the continuous-cohomology argument of Milne's Lemma 2.9. The archive proves the general order formula by dévissage and uses a finite Galois extension in its simple-module step.

1. In `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/EulerCharGaloisOfCardEq.lean`, lines 18–90, strong induction on $|A|$ starts with the zero module and delegates simple modules to `eulerChar_of_forall_eq_bot_or_eq_top`. Otherwise a nonzero proper stable subgroup and its quotient both have strictly smaller orders. The long exact cohomology sequence, finite and zero above degree two, makes $\chi$ multiplicative. The index on the right is multiplicative because a nonzero element of the discrete valuation ring is a unit times a power of a uniformizer and valuations add under multiplication. Lines 92–101 specialize the induction and rewrite the Euler product as the quotient of three orders. The formula requires finiteness, including in degree one where the quotient will be cleared.
2. In `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/MainSimple.lean`, lines 50–113, simplicity and Cauchy's theorem force the module to be killed by one prime $\ell$. Choose a finite Galois extension $L/K$ over which both the action and $\mu_\ell$ are trivial. For $\ell\ne p$, let $G_0,G_1$ be inertia and wild inertia in $\operatorname{Gal}(L/K)$. The preimage in $G_K$ of the inverse image of the prime-to-$\ell$ part of $G_0/G_1$ has either zero or full fixed space. If zero, lines 194–213 use inertia vanishing in degrees zero through two. The proof takes invariants across an index prime to the coefficient prime, starting with a subgroup that fixes both the coefficients and the roots. Inertia fixes the roots and acts trivially on their cohomology in the degrees used there, so the zero fixed space of the coefficient factor forces vanishing. Otherwise take the preimage of the $\ell$-primary part of the residue quotient $\operatorname{Gal}(L/K)/G_0$, denoted `primaryQuotientPreimage G₀ ℓ` at the finite level. It contains all of inertia. Its quotient by the previous subgroup is an $\ell$-group, so its fixed space is nonzero by the finite $\ell$-group fixed-point argument and is the whole module by simplicity. Its index in $G_K$ is prime to $\ell$. It fixes $\mu_\ell$ by the roots-of-unity lemma used at lines 247–248. The residue action there has $\ell$-power order, while the automorphisms of $\mu_\ell$ have order dividing $\ell-1$. The coprime-index calculation then gives Euler characteristic one (lines 215–259).
3. In the equal-prime branch of the same proof (lines 114–182), the finite wild $p$-group fixes the simple module by the same fixed-point argument. The cyclic $\ell$-power quotient obtained by removing the prime-to-$\ell$ part of inertia permits restriction to a subgroup where the remaining calculation has prime-to-$\ell$ index and the smaller subgroup fixes the coefficients and $\mu_\ell$. If the cyclic quotient has order $\ell^b$, the Euler characteristic on restriction is the original raised to $\ell^b$. The integer-ring quotient index scales by the same power, since the corresponding extension has degree $\ell^b$. Positivity then determines the original Euler characteristic. The coprime-index proof in `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Coprime.lean`, lines 213–355 and 405–433, uses restriction and averaging to take fixed vectors, tensors the cohomology of $\mu_\ell$ by $\operatorname{Hom}(\mu_\ell,A)$ on the finite quotient, and uses the alternating dimension identity for the units modulo powers and their torsion. Its full hypotheses are open subgroups $V\triangleleft U$ of $G_K$ with $[U:V]$ prime to $\ell$, $\ell$ nonzero in $K$, $V$ fixing $\mu_\ell$ and the finite discrete $\ell$-killed module $A$, and $|\mathcal O_{K^{U}}/\ell|=\ell^n$. Its conclusion is $\chi(U,A)=|A|^{-n}$. With $E=K^U$, $L=K^V$ and $H=\operatorname{Gal}(L/E)$, the published alternating-class identity used for comparison is Milne I, Lemma 2.11 in the mixed-characteristic case. For $E/\mathbb Q_\ell$ finite, $L/E$ finite Galois containing $\mu_\ell$, and $A$ a finite $\mathbb F_\ell[H]$-module, the alternating class of the $H^i(L,A)$ in the Grothendieck group of finite $\mathbb F_\ell[H]$-modules is $-[E:\mathbb Q_\ell]\dim_{\mathbb F_\ell}(A)[\mathbb F_\ell[H]]$. Here $V$ fixing $A$ makes it an $H$-module, $V$ fixing the roots gives $\mu_\ell\subset L$, and $n=[E:\mathbb Q_\ell]$. Exact $H$-invariants, by the index condition, turn the regular representation into a one-dimensional invariant space. The archived proof establishes its own units identity and comparison maps. [Milne, *Arithmetic Duality Theorems*, I, Lemma 2.11, pp. 33–34](https://www.jmilne.org/math/Books/ADTnot.pdf).
4. In `src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CardH1EqCardH0MulCardH2.lean`, lines 15–50, `card_H1_eq_card_H0_mul_card_H2` uses `gcField` for the local-field structure and separable closure and `gcRep`, `gc0`, `gc1`, `gc2` for transport. Since $|A|$ is an $\ell$-power, it is a unit in $\mathcal O_K$. The proof uses Bézout with $p$ and the fact that $\mathcal O_K/(p)$ has more than one element, invokes degree-one finiteness to clear the rational denominator, and transports the orders back. Lines 52–92 supply the prime below $v$ and the two branches of `LocalEulerCharAt`. The comparison `decEquiv` identifies the decomposition group with the absolute group of a finite extension $K/\mathbb Q_p$, identifies the local degree with `locDeg v`, and allows the continuous action to be pulled across the group isomorphism. At $v\mid\ell$, `top_euler` uses the same order quotient with its factor $|A|^{[K:\mathbb Q_\ell]}$. The definition of `LocalEulerCharAt` in `src/ReciprocityTheory/Hypotheses/GalCoh.lean:54–59` binds $r>0$, the valuation lying over $v$, and continuity of the action before splitting on $\ell\in v$. The proof constructs the proposition from the preceding calculation.

**Finiteness in the archive.** [Lean, read] The theorem `finite_cohomology_localField` in `src/GroundTheory/ProfiniteCohomology/LocalTateDuality/TensorHomDualRepRootsOfUnityIsoCartierPairing.lean:111–113` invokes `finite_cohomology_galois_top` with the order of $A$ as an annihilator. The declaration shares a file with local duality and invokes the separate finiteness theorem. In `src/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing.lean:16–34,60–76` the underlying proof treats degrees at most two by dévissage from trivial coefficients over open subgroups fixing the relevant roots of unity. Higher degrees use the degree-three-and-above vanishing theorem. At a number-field place, `finCd2_GK` and `localFiniteness` transport these statements back to the decomposition group. [Archive source references](../sources/SOURCES.md#chapter-18-1837-local-euler-characteristic)

**Where it is used.** [Lean, read] At `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LoceulerHolds.lean:8`, the wrapper `loceuler_holds` supplies `localEulerChar_alt_alt`, which fills `LitCoh.le` and the separate field `localEulerChar` and is passed directly to `greenbergWiles`. The assignment sites are `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:571–578,630,726`. The open-image wrapper `localEulerChar_alt` supplies the same proof to its parallel assembly. In `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisCochains/LocEuler.lean`, lines 5–121, `GC.locEuler` uses local finiteness, local Tate duality and the Euler formula as three inputs. For a finite field $k$ of characteristic $\ell$, it restricts the action to $\mathbb Z/\ell\mathbb Z$ without changing cocycles or coboundaries, imports finiteness, and writes every order as a power of $|k|$. Injectivity of these powers gives the dimension identities, with the extra term $\operatorname{locDeg}(v)\dim_k M$ at $v\mid\ell$. The final equality with the dimension of the twisted dual invariants uses degree $(2,0)$ Tate duality. The finite-field trace identifies the two scalar versions of twisted functionals: trace nondegeneracy gives injectivity and their orders agree. In `src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/AdjointCoefficients/ExAbove.lean`, line 97, `ecG` applies this lemma to the quotient coefficients $W/b_v$ and at lines 125–129 uses the branch at $\ell$ to sum the local dimensions. This is a concrete consumer of the same two-branch interface.

**Read boundary.** [Open] The [source ledger](../sources/SOURCES.md#chapter-18-1837-local-euler-characteristic) records the archive and literature editions. The proof of `decEquiv` and its inputs `exists_embedding`, `exists_decompositionGroup_equiv_padicGalois`, `localInertia_iff_mem_placeInertia` and `finrank_closure_eq_locDeg` are comparison inputs. The underlying group-cochain comparisons `gcRep`, `gc0`, `gc1`, `gc2` and `gcn` and the transport equivalences `equivH0OfIso`, `equivH1OfIso`, `equivH2OfIso` are used as interfaces here. The local Tate-duality core `tate_core` and `localDualityHypotheses` are also inputs. Within the Euler and finiteness arguments the deeper inputs include the cyclic restriction calculation `eulerChar_coind_res_eq_pow`, the ramification-group and root containment lemmas, the units lattice behind `g_units_eq`, the inertia cohomology computation behind `cohomologyConj_galRootsOfUnity_eq_id`, and the trivial-module finiteness and degree-three vanishing theorems. The published Euler theorem supplies an independent classical comparison for these conclusions. R3 covers the named bodies and specified assembly expressions.

**Return to the unramified condition.** At $v\nmid\ell$, assume $M$ is unramified and use the perfect local Tate pairing, its degree $(2,0)$ order equality and the unramified vanishing of the cup pairing from the cited unramified orthogonality result. We have $|U(M)|=|H^0(K,M)|$ and $|U(M^D)|=|H^0(K,M^D)|=|H^2(K,M)|$. The Euler formula gives $|U(M)|\,|U(M^D)|=|H^1(K,M)|$. Thus the cited orthogonality argument identifies the two unramified conditions as exact annihilators and identifies the dual unramified condition with the dual of $H^1(K,M)/U(M)$. For $L_v=U(M)$ the Greenberg–Wiles local ratio $|L_v|/|H^0(K,M)|$ is one. The pairing, its normalization and the passage to the quotient are the results cited in Tate’s unramified orthogonality theorem and the separately delivered companion §18.3.6, “The unramified local condition and its dual.” [Tate, *Duality theorems in Galois cohomology*, Theorem 2.4, p. 290](https://math.stanford.edu/~conrad/BSDseminar/refs/TateICM.pdf).


### 18.3.8 Decomposition groups as Galois groups of completions

**Motivation.** The local Euler formula of §18.3.7 concerns the absolute Galois group $G_K$ of a finite extension $K/\mathbb Q_p$. The interface that consumes it, `LocalEulerCharAt` in `src/ReciprocityTheory/Hypotheses/GalCoh.lean:54–59`, is phrased for a number field. There the coefficients are a representation of the decomposition group $D_A\subset\operatorname{Gal}(\Omega/F)$ of a valuation ring $A$ of an algebraic closure $\Omega$ of $F$, and the residue-prime factor is $|M|^{\operatorname{locDeg}(v)}$ with $\operatorname{locDeg}(v)=e(v/p)f(v/p)$. The producer `localEulerChar_holds` bridges the two settings with one call to `decEquiv` in each branch. It needs a finite extension $K/\mathbb Q_p$ and an isomorphism of topological groups $D_A\simeq G_K$ along which continuous cochains can be pulled back. At places above $\ell$ it also needs $[K:\mathbb Q_p]=\operatorname{locDeg}(v)$. Two further outputs, the matching of inertia groups and of cyclotomic characters, are produced and discarded. None of these data is canonical. The isomorphism is built from an embedding $\Omega\to\overline{\mathbb Q}_p$, and another embedding changes it by a conjugation. This subsection proves the comparison and computes it at a split and an inert prime of $\mathbb Q(i)$. It also shows why the Euler count does not depend on the choice.

**Setting.** Let $F$ be a number field, $\Omega$ an algebraic closure and $G_F=\operatorname{Gal}(\Omega/F)$ with the Krull topology. Fix a prime $p$. As in the archive, $\overline{\mathbb Q}_p$ is an algebraic closure of $\mathbb Q_p$ with the unique extension of $|\cdot|_p$, and $G_{\mathbb Q_p}=\operatorname{Aut}_{\mathbb Q_p}(\overline{\mathbb Q}_p)$. Every element of $G_{\mathbb Q_p}$ preserves $|\cdot|$. For $K\subset\overline{\mathbb Q}_p$ finite over $\mathbb Q_p$, $G_K\subset G_{\mathbb Q_p}$ is the subgroup fixing $K$. Since $\overline{\mathbb Q}_p$ is an algebraic closure of $K$, this is the absolute Galois group of $K$. Let $A\subset\Omega$ be a valuation subring with valuation $v_A$ and $v_A(p)<1$. Its decomposition and inertia groups are
$$D_A=\{g\in G_F : g(A)=A\},\qquad I_A=\{g\in D_A : v_A(gx-x)<1\ \text{for all}\ x\in A\}.$$
The ring $A$ lies over a maximal ideal $w$ of $\mathcal O_F$ if $x\in w\iff v_A(x)<1$ for all $x\in\mathcal O_F$.

**First example — a split prime.** Let $F=\mathbb Q(i)$ and $p=5=(2+i)(2-i)$. Since $3^2\equiv-1\pmod 5$, Hensel's lemma gives $\iota\in\mathbb Z_5$ with $\iota^2=-1$ and $\iota\equiv3\pmod 5$. Extend $i\mapsto\iota$ to a ring embedding $j\colon\Omega\to\overline{\mathbb Q}_5$. This is possible because $\overline{\mathbb Q}_5$ is algebraically closed. Put $A=\{x\in\Omega:|j(x)|\le1\}$, a valuation subring to which $j$ is adapted in the sense of the definition below. As $j(2+i)=2+\iota\equiv0$ and $j(2-i)\equiv-1\pmod 5$, the ring $A$ lies over $w=(2+i)$. The field $K_j=\mathbb Q_5(j(F))=\mathbb Q_5(\iota)$ is $\mathbb Q_5$. So $[K_j:\mathbb Q_5]=1$, which agrees with $\operatorname{locDeg}(w)=1\cdot1$, because $\mathcal O_F/w\simeq\mathbb F_5$ via $i\mapsto-2$. The theorem below gives an isomorphism $i_j\colon D_A\to G_{\mathbb Q_5}$ with $i_j(g)\circ j=j\circ g$.

Take $\ell=3$, so $\ell\notin w$, and let $M=\mu_3(\Omega)$ with its natural action of $D_A$. Transport along $i_j$ lets $h\in G_{\mathbb Q_5}$ act on $M$ through $i_j^{-1}(h)$. Since $j(i_j^{-1}(h)\zeta)=h(j(\zeta))$, the map $j$ identifies this module with $\mu_3(\overline{\mathbb Q}_5)$. Inertia acts trivially and Frobenius acts by $5\equiv-1$. In the notation of the two-row lemma of §18.3.7, $D=M$ has Frobenius matrix $-1$ and $C=\operatorname{Hom}(T_3,M)$ has matrix $5^{-1}\cdot(-1)=1$ in $\mathbb F_3$. Hence $D^\phi=D_\phi=0$ and $C^\phi=C_\phi=\mathbb F_3$, and the orders of $H^0,H^1,H^2$ are $(1,3,3)$. As a check, Kummer theory gives $H^1(\mathbb Q_5,\mu_3)\simeq\mathbb Q_5^\times/\mathbb Q_5^{\times3}$. This has order three, because $\mathbb Q_5^\times=5^{\mathbb Z}\times\mu_4\times(1+5\mathbb Z_5)$ and the last two factors are $3$-divisible. The transport isomorphisms give the same orders for $D_A$. The prime-to-residue branch of `LocalEulerCharAt` reads $3=1\cdot3$, and the dimension identity of `GC.locEuler` with $k=\mathbb F_3$ reads $1=0+1$.

Now change the embedding. Let $\theta\in G_{\mathbb Q_5}$ be a lift of Frobenius and $j'=\theta\circ j$. Since $\theta$ preserves absolute values, $j'$ is adapted to the same $A$, and $K_{j'}=\theta(\mathbb Q_5)=\mathbb Q_5$. By part 6 of the theorem, $i_{j'}(g)=\theta\,i_j(g)\,\theta^{-1}$. This is a different isomorphism. Let $L$ be the splitting field of $X^3-5$ over $\mathbb Q_5$. The polynomial is Eisenstein and $\mu_3\not\subset\mathbb Q_5$ because $3\nmid5-1$, so $\operatorname{Gal}(L/\mathbb Q_5)\simeq S_3$ with inertia subgroup $A_3$ of order $e=3$. The restriction of $\theta$ acts nontrivially on the residue field $\mathbb F_{25}$, so it is a transposition. If $h\in I_{\mathbb Q_5}$ restricts to a $3$-cycle $c$, then $\theta h\theta^{-1}$ restricts to $c^{-1}\ne c$, so $g=i_j^{-1}(h)$ satisfies $i_{j'}(g)\ne i_j(g)$.

On cohomology the change is a sign. Since $\theta\in G_{\mathbb Q_5}=i_j(D_A)$, put $g_0=i_j^{-1}(\theta)$; then $j'=j\circ g_0$. The two transported actions on $M$ coincide, because $D_A$ acts on $\mu_3$ through the abelian group $(\mathbb Z/3)^\times$. By part (c) of the corollary below, the two transports $T_j,T_{j'}\colon H^n(D_A,M)\to H^n(\mathbb Q_5,M)$ satisfy $T_{j'}=\chi(g_0)^{-1}T_j$, where $\chi(g_0)=5\equiv-1$ is the action of $g_0$ on $\mu_3$. Thus $T_{j'}=-T_j$ on $H^1$ and $H^2$, both of order three. If $T_j(x)$ is the Kummer class of $5$ under the identification by $j$, then $T_{j'}(x)$ is the Kummer class of $5^{-1}$. If instead the module is transported along the embedding itself, by $j$ in one case and by $j'$ in the other, the signs cancel, since $j'(\zeta)=j(\zeta)^5=j(\zeta)^{-1}$ on $\mu_3$. This is the independence statement recalled in the last remark. The orders $(1,3,3)$ are the same in every version.

**Second example — an inert prime.** Let $F=\mathbb Q(i)$ and $p=3$. Since $X^2+1$ has no root modulo $3$, $w=3\mathcal O_F$ is prime with $\mathcal O_F/w\simeq\mathbb F_9$. So $e=1$, $f=2$ and $\operatorname{locDeg}(w)=2$. Any embedding $j\colon\Omega\to\overline{\mathbb Q}_3$ defines an adapted valuation ring $A$, which lies over $w$, the only prime above $3$. Here $K_j=\mathbb Q_3(j(i))$ is the unramified quadratic extension, and $[K_j:\mathbb Q_3]=2=\operatorname{locDeg}(w)$, as part 4 of the theorem asserts. Its counting proof is visible here: $\mathcal O_F/w^e$ and $\mathcal O_{K_j}/3\mathcal O_{K_j}=\mathbb Z_3[j(i)]/(3)$ are both $\mathbb F_9$, of order $3^2$.

Take $\ell=3\in w$ and $M=\mathbb F_3$ with trivial action. Then $|H^0(K,M)|=3$. Local duality identifies $H^2(K,\mathbb F_3)$ with the dual of $H^0(K,\mu_3)$, and $\mu_3(K)=1$. Indeed $-3$ has odd valuation in the unramified field $K$, so it is not a square. [Paper] [Milne, *Arithmetic Duality Theorems*, I, Corollary 2.3, p. 28](https://www.jmilne.org/math/Books/ADTnot.pdf). The residue-prime Euler formula of §18.3.7 then gives
$$|H^1(K,\mathbb F_3)|=3\cdot1\cdot3^{[K:\mathbb Q_3]}=27.$$
Local class field theory gives an independent check. [Paper] The reciprocity map identifies $H^1(K,\mathbb F_3)=\operatorname{Hom}_{\mathrm{cts}}(G_K,\mathbb F_3)$ with $\operatorname{Hom}(K^\times/K^{\times3},\mathbb F_3)$, by the reciprocity law and the existence theorem. [Milne, *Class Field Theory*, I, Theorems 1.1 and 1.4, pp. 20–22](https://www.jmilne.org/math/CourseNotes/CFT.pdf). Write $U_n=1+3^n\mathcal O_K$. Then $K^\times=3^{\mathbb Z}\times\mu_8\times U_1$. For $x\in\mathcal O_K$ one has $(1+3^nx)^3\equiv1+3^{n+1}x\pmod{3^{n+2}}$, so cubing induces bijections $U_n/U_{n+1}\to U_{n+1}/U_{n+2}$ and $U_1^3=U_2$. Since cubing is bijective on $\mu_8$,
$$K^\times/K^{\times3}\simeq\mathbb Z/3\times U_1/U_2,\qquad U_1/U_2\simeq\mathcal O_K/3\mathcal O_K=\mathbb F_9\ \text{via}\ 1+3x\mapsto\bar x,$$
of order $3\cdot9=27$. The factor $9=3^{[K:\mathbb Q_3]}$ is the residue-prime factor. In the archive the first branch of `LocalEulerCharAt` reads $27=3\cdot1\cdot3^{\operatorname{locDeg}(w)}$. It is obtained from `top_euler`, which gives $3\cdot1\cdot3^{[K:\mathbb Q_3]}$, by rewriting with part 4 at `CardH1EqCardH0MulCardH2.lean:74`. `GC.locEuler` turns it into $3=1+0+2\cdot1$. In `ExAbove.lean:125–131` the identity is summed over places above $\ell$ and compared with $[F:\mathbb Q]$ through `sum_deg`. For $F=\mathbb Q(i)$ and $\ell=3$ the only place above $3$ is $(3)$, with $\operatorname{locDeg}=2=[F:\mathbb Q]$, so the bound is attained, as $\sum_{v\mid\ell}e_vf_v=[F:\mathbb Q]$ predicts. [Milne, *Algebraic Number Theory*, Theorem 3.34, p. 59](https://www.jmilne.org/math/CourseNotes/ANT.pdf).

Now let $\theta\in G_{\mathbb Q_3}$ act nontrivially on $K$, for instance a lift of Frobenius, so $\theta(j(i))=-j(i)$. Then $j'=\theta\circ j$ is adapted to $A$ and $K_{j'}=\theta(K)=K$, but $j'$ and $j$ differ on $F$. Hence $j'\ne j\circ g$ for every $g\in G_F$, and this change of embedding cannot be absorbed into $D_A$. By part (c) of the corollary, $T_{j'}$ is $T_j$ followed by $\chi\mapsto\chi\circ\operatorname{ad}(\theta^{-1})$ on $\operatorname{Hom}(G_K,\mathbb F_3)$. Reciprocity is natural under $\theta$. By uniqueness in Milne's Theorem 1.1, $x\mapsto\theta^{-1}\operatorname{rec}_K(\theta x)\theta$ is again the reciprocity map of $K$. So the composite corresponds to $\psi\mapsto\psi\circ\theta^{-1}$ on $\operatorname{Hom}(K^\times/K^{\times3},\mathbb F_3)$. The automorphism $\theta$ fixes $3$ and acts on $U_1/U_2=\mathbb F_9$ by $a+b\,j(i)\mapsto a-b\,j(i)$, the Frobenius of $\mathbb F_9$. Its fixed subgroup in $K^\times/K^{\times3}$ has order $3\cdot3=9$, and its $(-1)$-eigenspace has order $3$. So $T_{j'}$ and $T_j$ differ by an involution of $H^1(K,\mathbb F_3)$ with fixed subgroup of order $9$. The Euler formula over $\mathbb Q_3$ gives $|H^1(\mathbb Q_3,\mathbb F_3)|=3\cdot1\cdot3=9$. Restriction from $\mathbb Q_3$ is injective, by inflation–restriction with $H^1(\mathbb Z/2,\mathbb F_3)=0$, and lands in the fixed subgroup. Hence it is an isomorphism onto that subgroup, as the counts require. [Milne, *Class Field Theory*, II, Proposition 1.34, p. 71](https://www.jmilne.org/math/CourseNotes/CFT.pdf). Both transports have image of order $27$.

**Definition.** An *adapted embedding* for $A$ is a ring homomorphism $j\colon\Omega\to\overline{\mathbb Q}_p$ with $A=\{x\in\Omega:|j(x)|\le1\}$. Put $K_j=\mathbb Q_p(j(F))$. The inertia subgroup $I_K$ of $G_K$ is the subgroup generated by $\{\sigma\in G_K:|\sigma x-x|<1\ \text{whenever}\ |x|\le1\}$, as in `inertiaSet` and `inertiaK` (`src/Formalism/GaloisCohomology/StatementLoc.lean:13–15`). By the ultrametric inequality this set is already a subgroup. For a maximal ideal $w\ni p$ of $\mathcal O_F$ write $\operatorname{locDeg}(w)=e(w/p)f(w/p)$ (`src/ReciprocityTheory/Hypotheses/GalCohDefs.lean:132–133`). Let $R$ be a ring and $M$ a discrete $R$-module with a continuous $R$-linear action $\rho$ of $D_A$. Given a group isomorphism $i\colon D_A\to G_K$, the *transported module* $M_i$ is $M$ with $h\in G_K$ acting by $\rho(i^{-1}(h))$. This is `rhoK` in `CardH1EqCardH0MulCardH2.lean:69,84`.

**Lemma 1 (the place below, and adapted embeddings).** [Lean, read]
1. There is exactly one maximal ideal $w$ of $\mathcal O_F$ under $A$, and $p\in w$.
2. Adapted embeddings exist.
3. If $j$ is adapted, then $j(\Omega)$ is dense in $\overline{\mathbb Q}_p$.
4. If $j$ and $j'$ are adapted to $A$, there is exactly one $\theta\in G_{\mathbb Q_p}$ with $j'=\theta\circ j$.

**Proof.** (1) Elements of $\mathcal O_F$ are integral over $\mathbb Z$, so they lie in the integrally closed ring $A$. Let $w$ be the preimage of the maximal ideal of $A$. It is prime, it contains $p$ because $v_A(p)<1$, and it is nonzero. Uniqueness is immediate from the defining equivalence. This is `exists_place_below` in `DecompositionGroupEquivLocalGaloisGroup.lean:18–36`.

(2) Since $\Omega$ is algebraic over $\mathbb Q$, there is a $\mathbb Q$-embedding $j_0\colon\Omega\to\overline{\mathbb Q}_p$. Let $A_0=\{x:|j_0(x)|\le1\}$. For any valuation ring $B$ of $\Omega$ with $v_B(p)<1$, an integer $n$ has $v_B(n)<1$ exactly when $p\mid n$. Otherwise $ap+bn=1$ for integers $a,b$ and the ultrametric inequality gives $v_B(1)<1$. So $A_0$ and $A$ both lie over $p\mathbb Z$. The group $\operatorname{Aut}(\Omega/\mathbb Q)$ acts transitively on the valuation rings of $\Omega$ over $p\mathbb Z$. Hence there is $\sigma$ with $\sigma(A_0)=A$, and $j=j_0\circ\sigma^{-1}$ is adapted to $A$. The conjugation takes place over $\mathbb Q$, not over $F$. The place $w$ is recovered from $A$ and is not prescribed in advance. This is `PlaceBridge.exists_embedding` in `FiniteDimensionalAdjoinRange.lean:36–75`, with `val_int_lt_one_iff` at `:8–28`. Transitivity is `exists_smul_eq_of_isPlaceOver` at `src/ReciprocityTheory/GaloisValuations/Global.lean:340–343`, applied with base field $\mathbb Q$. It reduces to `exists_smul_eq_of_over` at `src/ReciprocityTheory/GaloisValuations/GlobalB.lean:222–236` and Mathlib's conjugacy of primes for profinite invariant extensions.

(3) Let $a\in\overline{\mathbb Q}_p$ have minimal polynomial $f$ over $\mathbb Q_p$ of degree $d$, and let $\delta>0$. Since $\mathbb Q$ is dense in $\mathbb Q_p$, there is a monic $g\in\mathbb Q[X]$ of degree $d$ whose coefficients are so close to those of $f$ that some root $b$ of $g$ satisfies $|a-b|<\delta$, by continuity of roots. The polynomial $g$ splits in $\Omega$, so its roots in $\overline{\mathbb Q}_p$ are images under $j$. This is `denseRange_embedding` at `:77–105`.

(4) The absolute values $x\mapsto|j(x)|$ and $x\mapsto|j'(x)|$ on $\Omega$ have the same unit ball $A$, hence are equivalent. So $|j'(x)|=|j(x)|^c$ for some $c>0$. At $x=p$ both sides equal $|p|_p<1$, so $c=1$ (`norm_eq_of_le_one_iff`, `:107–130`). Give $\Omega$ the norm $|j(\cdot)|$. Then $j(x)\mapsto j'(x)$ is an isometric ring map on the dense subfield $j(\Omega)$ by (3). It extends by uniform continuity to a continuous ring map $\overline{\mathbb Q}_p\to\mathbb C_p$. This map is $\mathbb Q_p$-linear because it fixes the dense subfield $\mathbb Q$. Normality of $\overline{\mathbb Q}_p/\mathbb Q_p$ then gives $\theta\in G_{\mathbb Q_p}$ with $\theta\circ j=j'$ (`exists_algEquiv`, `:132–156`). Two elements of $G_{\mathbb Q_p}$ are isometries, so if they agree on the dense set $j(\Omega)$ they are equal (`algEquiv_ext`, `:161–165`). $\square$

**Theorem 18.3.8 (completion comparison).** Let $A$, $p$ and $w$ be as above, and let $j$ be an adapted embedding. Assume the counting inputs `BallCard`, `DenseSurj`, `KerProp` and `NormCard`, the integrality input `placeProp` and the conjugacy of primes used in Lemma 1(2). The archive proves all of them. The proofs of the four counting inputs are read in [§18.3.9](#1839-counting-the-local-degree-closed-balls-integral-approximation-and-the-power-kernel); the other two are named in the read boundary below.
1. $K_j$ is finite over $\mathbb Q_p$ and contained in the closure of $j(F)$.
2. There is exactly one map $i_j\colon D_A\to G_{K_j}$ with $i_j(g)\circ j=j\circ g$ for all $g$, and it is an isomorphism of topological groups.
3. For $g\in D_A$, $i_j(g)\in I_{K_j}$ if and only if $g\in I_A$.
4. $[K_j:\mathbb Q_p]=\operatorname{locDeg}(w)$.
5. Let $O$ be a commutative ring and $\varepsilon\colon D_A\to O^\times$ a character such that for each $g$, $n$ and $\zeta\in\mu_{p^n}(\Omega)$ there is $a\in\mathbb N$ with $g\zeta=\zeta^a$ and $\varepsilon(g)\equiv a\pmod{p^n}$. Then $\varepsilon\circ i_j^{-1}$ has the same property on $G_{K_j}$ and $\mu_{p^n}(\overline{\mathbb Q}_p)$.
6. Let $j'=\theta\circ j$ be another adapted embedding. Then $K_{j'}=\theta(K_j)$ and $i_{j'}(g)=\theta\,i_j(g)\,\theta^{-1}$. Moreover $\theta\in G_{K_j}$ if and only if $j'$ and $j$ agree on $F$, if and only if $j'=j\circ g_0$ for some $g_0\in D_A$. In that case $g_0=i_j^{-1}(\theta)$ and $i_{j'}(g)=i_j(g_0gg_0^{-1})$. For $\sigma\in G_F$, the embedding $j\circ\sigma^{-1}$ is adapted to $\sigma(A)$, $D_{\sigma(A)}=\sigma D_A\sigma^{-1}$ and $i_{j\circ\sigma^{-1}}(\sigma g\sigma^{-1})=i_j(g)$. Every valuation ring over $w$ has the form $\sigma(A)$.

As $K_j$ is complete, being finite-dimensional over $\mathbb Q_p$, part 1 makes it the closure of $j(F)$. For $x\in\mathcal O_F$ one has $|j(x)|<1$ exactly when $x\in w$. So $K_j$ is a completion of $F$ at $w$, and parts 2–4 identify $D_A$, $I_A$ and the local degree with the corresponding data of the completion. Parts 1–5 are `decEquiv` (`DecompositionGroupEquivLocalGaloisGroup.lean:85–100`), with $j$ hidden in an existential. Part 6 is proved below from Lemma 1 and the uniqueness in part 2. It is not itself a Lean declaration.

**Proof.** [Lean, read] Unless stated otherwise, line numbers refer to `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalAdjoinRange.lean`.

*Step 1 (finiteness and density).* If $b_1,\dots,b_m$ is a $\mathbb Q$-basis of $F$, then $K_j=\mathbb Q_p(j(b_1),\dots,j(b_m))$ is generated by finitely many algebraic elements (`finiteDimensional_adjoin_range`, `:171–187`). The closure $S$ of the subfield $j(F)$ is a closed subfield containing $\mathbb Q$, hence $\mathbb Q_p$. So $K_j\subset S$ (`adjoin_range_subset_closure`, `:190–203`).

*Step 2 (the subgroup $G_K$).* Write $K=K_j$. An element $\tau\in G_{\mathbb Q_p}$ lies in $G_K$ if and only if $\tau(j(x))=j(x)$ for all $x\in F$. The proof is induction over the field generated by $j(F)$ (`mem_GK_iff`, `:213–226`).

*Step 3 (restriction).* Let $\tau\in G_K$ and view $\overline{\mathbb Q}_p$ as an $\Omega$-algebra through $j$. Then $\tau$ is an $F$-algebra map and $\Omega/F$ is normal, so $\tau$ restricts to $g\in\operatorname{Aut}_F(\Omega)$ with $\tau\circ j=j\circ g$. Moreover $g\in D_A$. For $x\in\Omega$,
$$x\in g(A)\iff|j(g^{-1}x)|\le1\iff|\tau^{-1}(j(x))|\le1\iff|j(x)|\le1\iff x\in A.$$
This is `exists_restrict`, `:228–241`.

*Step 4 (a bijective homomorphism $G_K\to D_A$).* Let $r(\tau)$ be the element $g$ of Step 3. It is unique because $j$ is injective, and $r$ is a homomorphism for the same reason (`:250–258`). If $r(\sigma)=r(\tau)$, then $\sigma$ and $\tau$ agree on $j(\Omega)$, so $\sigma=\tau$ by Lemma 1(4) (`:260–261`). For surjectivity let $g\in D_A$. As $g(A)=A$, the embeddings $j$ and $j\circ g$ are adapted to the same ring, so $j\circ g=\theta\circ j$ for some $\theta\in G_{\mathbb Q_p}$ by Lemma 1(4). Since $g$ fixes $F$, $\theta$ fixes $j(F)$, so $\theta\in G_K$ by Step 2. Injectivity of $j$ then gives $r(\theta)=g$ (`:262–273`).

*Step 5 (continuity).* A neighbourhood of $1$ in $D_A$ contains $D_A\cap\operatorname{Gal}(\Omega/L)$ for some finite extension $L/F$. Let $b_1,\dots,b_m$ be an $F$-basis of $L$. Each $j(b_k)$ is algebraic over $\mathbb Q_p$, so its stabilizer in $G_{\mathbb Q_p}$ is open. If $\tau\in G_K$ fixes every $j(b_k)$, then $j(r(\tau)b_k)=\tau(j(b_k))=j(b_k)$, so $r(\tau)$ fixes $L$. Thus $r$ is continuous at $1$, hence continuous (`:274–291`).

*Step 6 (homeomorphism and uniqueness).* $G_K$ is closed in the compact group $G_{\mathbb Q_p}$, hence compact, and $D_A$ is Hausdorff. A continuous bijection from a compact space to a Hausdorff space is a homeomorphism, so $i_j=r^{-1}$ is an isomorphism of topological groups. It satisfies $i_j(g)\circ j=j\circ g$ (`exists_mulEquiv`, `:243–299`). Any map with this property is determined on the dense set $j(\Omega)$, which gives uniqueness. The archive then passes from the fixing subgroup of $K$ in $G_{\mathbb Q_p}$ to $\operatorname{Aut}_K(\overline{\mathbb Q}_p)$ by Mathlib's `IntermediateField.fixingSubgroupEquiv`. This passage is continuous in both directions (`FixingSubgroupEquivBicontinuous.lean:12–48`) and is assembled in `DecGalois.exists_continuousMulEquiv` (`ExistsDecompositionGroupEquivPadicGalois.lean:16–31`).

*Step 7 (inertia).* For $x\in\Omega$, $v_A(x)<1$ if and only if $|j(x)|<1$ (`valuation_lt_one_iff_norm`, `LocalInertiaIffMemPlaceInertia.lean:12–20`). Suppose $\sigma\in G_K$ moves every $x$ with $|x|\le1$ by less than $1$. Then for $y\in A$ we have $|j(i_j^{-1}(\sigma)y-y)|=|\sigma(j(y))-j(y)|<1$, so $i_j^{-1}(\sigma)\in I_A$. Since $i_j(I_A)$ is a subgroup, it contains the subgroup $I_K$ that these $\sigma$ generate. Conversely let $g\in I_A$ and $|x|\le1$. By Lemma 1(3) choose $y\in\Omega$ with $|x-j(y)|<1$. Then $|j(y)|\le1$, so $y\in A$ and $|i_j(g)(j(y))-j(y)|=|j(gy-y)|<1$. Since $i_j(g)$ preserves norms,
$$i_j(g)x-x=i_j(g)(x-j(y))+\bigl(i_j(g)(j(y))-j(y)\bigr)-\bigl(x-j(y)\bigr)$$
has norm less than $1$. This is `inertiaK_iff_mem_Ine` at `LocalInertiaIffMemPlaceInertia.lean:22–65`.

*Step 8 (local degree).* Let $\varphi=j|_F$ and let $\mathcal O_K$ be the closed unit ball of $K$. Each $x\in\mathcal O_F$ has $|\varphi(x)|\le1$ (`placeProp`), and $\psi=\varphi|_{\mathcal O_F}\colon\mathcal O_F\to\mathcal O_K$ is a ring map. Consider $\mathcal O_F\to\mathcal O_K\to\mathcal O_K/p\mathcal O_K$, where $y\in p\mathcal O_K$ if and only if $|y|\le|p|$ (`mem_span_l_iff`, `MemSpanLIff.lean:9–38`). The composite is surjective, since every $y\in\mathcal O_K$ lies within $|p|$ of some $\varphi(x)$ with $x\in\mathcal O_F$ (`DenseSurj`). Its kernel is $w^e$, since $|\varphi(x)|\le|p|$ exactly when $x\in w^{e}$ (`KerProp`). Hence $\mathcal O_F/w^e\simeq\mathcal O_K/p\mathcal O_K$. With $|\mathcal O_F/w^e|=p^{ef}$ (`NormCard`) and $|\mathcal O_K/p\mathcal O_K|=p^{[K:\mathbb Q_p]}$ (`BallCard`), injectivity of $n\mapsto p^n$ gives $[K:\mathbb Q_p]=ef$. This is `locDegOf_of` at `MemSpanLIff.lean:40–71`, applied in `finrank_closure_eq_locDeg` at `DecompositionGroupEquivLocalGaloisGroup.lean:67–83`. The compatibility of adaptedness with $w$ is `norm_lt_one_iff` at `:52–65`. [§18.3.9](#1839-counting-the-local-degree-closed-balls-integral-approximation-and-the-power-kernel) proves the four counting inputs and works through a ramified and an unramified example.

*Step 9 (cyclotomic characters).* Let $h\in G_K$ and $\zeta\in\mu_{p^n}(\overline{\mathbb Q}_p)$. The polynomial $X^{p^n}-1$ splits in $\Omega$, so $\zeta=j(y)$ with $y\in\mu_{p^n}(\Omega)$ (`exists_root_of_unity`, `:38–50`). If $g=i_j^{-1}(h)$ acts on $y$ by $y\mapsto y^a$ with $\varepsilon(g)\equiv a$, then $h(\zeta)=j(gy)=\zeta^a$ (`decEquiv`, `:94–100`).

*Step 10 (change of embedding).* The automorphism $\theta$ is $\mathbb Q_p$-linear, so $\theta(\mathbb Q_p(j(F)))=\mathbb Q_p(j'(F))$. The element $\theta\,i_j(g)\,\theta^{-1}$ fixes $\theta(K_j)=K_{j'}$ and satisfies $\theta\,i_j(g)\,\theta^{-1}\circ j'=\theta\circ j\circ g=j'\circ g$. Uniqueness in part 2 gives $i_{j'}(g)=\theta\,i_j(g)\,\theta^{-1}$. By Step 2, $\theta\in G_{K_j}$ exactly when $\theta\circ j=j$ on $F$. In that case $g_0=i_j^{-1}(\theta)$ satisfies $j\circ g_0=\theta\circ j=j'$. Conversely $j\circ g_0$ agrees with $j$ on $F$ for every $g_0\in G_F$. For $\sigma\in G_F$, $x\in\sigma(A)$ if and only if $|j(\sigma^{-1}x)|\le1$. The identity $i_j(g)\circ j\circ\sigma^{-1}=(j\circ\sigma^{-1})\circ\sigma g\sigma^{-1}$ and uniqueness give the formula for $i_{j\circ\sigma^{-1}}$. Every valuation ring over $w$ is a $G_F$-translate of $A$ by `exists_smul_eq_of_isPlaceOver`. $\square$

**Corollary 18.3.8.1 (transport, restriction, conjugation).** Let $M$ be a discrete $R$-module with continuous action $\rho$ of $D_A$, let $j$ be adapted and write $M_j=M_{i_j}$.

(a) [Lean, read] For $n=0,1,2$, precomposition with $i_j$ gives $R$-linear isomorphisms $H^n(G_{K_j},M_j)\to H^n(D_A,M)$ on continuous cohomology. Write $T_j$ for the inverse isomorphisms.

(b) [Lean, read] Restriction squares are transported. Let $\Gamma,\Gamma'$ be topological groups acting on $N$ by $\pi,\pi'$, let $e\colon\Gamma\to\Gamma'$ be an isomorphism of topological groups with $\pi'\circ e=\pi$, and let $\phi\colon D\to\Gamma$ and $\phi'\colon D'\to\Gamma'$ be continuous homomorphisms. Suppose $e_D\colon D\to D'$ is an isomorphism of topological groups, that is, $e_D$ and $e_D^{-1}$ are both continuous, with $\phi'\circ e_D=e\circ\phi$. Then for $n=1,2$, restriction along $\phi$ after transport along $e$ equals transport along $e_D$ after restriction along $\phi'$.

(c) Let $j'=\theta\circ j$. Then $T_{j'}=\operatorname{ad}(\theta^{-1})^\ast\circ T_j$. Here $\operatorname{ad}(\theta^{-1})^\ast\colon H^n(G_{K_j},M_j)\to H^n(G_{K_{j'}},M_{j'})$ is induced by $h\mapsto\theta^{-1}h\theta$ and the identity of $M$. If $\theta\in G_{K_j}$ and $g_0=i_j^{-1}(\theta)$, then $T_{j'}=u_\ast\circ T_j$ for the module isomorphism $u=\rho(g_0)^{-1}\colon M_j\to M_{j'}$. In particular the orders of $H^n(G_{K_j},M_j)$ do not depend on $j$.

**Proof.** (a) The two cochain maps $c\mapsto c\circ i_j$ and $c\mapsto c\circ i_j^{-1}$ preserve continuity, because $i_j$ is a homeomorphism. They preserve cocycles and coboundaries, because $\rho\circ i_j^{-1}\circ i_j=\rho$. Their composites are the identity already on cochains. In degree $0$ both sides are the same subgroup of $M$. These are `invariants_eq_of_iso`, `equivH0OfIso`, `equivH1OfIso` and `equivH2OfIso` in `src/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean:33–77`, built from the compatible-pair maps $c\mapsto u\circ c\circ\phi$ of `src/ReciprocityTheory/GaloisValuations/SeparatedDvrSecondCohomologyMem.lean:235–266`.

(b) On a cocycle $f$ the two composites are represented by $d\mapsto f(e(\phi(d)))$ and $d\mapsto f(\phi'(e_D(d)))$ in degree one, and by the analogous pairs in degree two. They agree because $\phi'\circ e_D=e\circ\phi$. Continuity of $e$, $e_D$ and their inverses makes precomposition a bijection between continuous cochains; the archive assumes `eG : Γ ≃ₜ* Γ'` and `eD : ∀ i, D i ≃ₜ* D' (eI i)` at `TateShafarevichTransport.lean:46`. These are `res_h1_iso_h1` and `res_h2_iso_h2` in `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TateShafarevichTransport.lean:55–81`, with the module compatibility `local_compat` at `:48–53`. The restriction maps are `resH1` and `resH2` (`SeparatedDvrSecondCohomologyMem.lean:147–169`). The same file applies them to transport Tate–Shafarevich groups (`mem_Sha1_iff_equiv_mem` to `nonempty_sha2_equiv`, `:83–121`).

(c) By part 6 of the theorem, $i_{j'}^{-1}(h)=i_j^{-1}(\theta^{-1}h\theta)$. Hence $T_{j'}(c)=T_j(c)\circ\operatorname{ad}(\theta^{-1})$ on cochains. Now suppose $\theta\in G_{K_j}$. Milne's Proposition 0.15 says that for $\sigma$ in a profinite group $G$, the compatible pair $(\operatorname{ad}(\sigma),\sigma^{-1})$ induces the identity on $H^n(G,M)$. Apply it with $G=G_{K_j}$ and $\sigma=\theta^{-1}$: the class of $c\circ\operatorname{ad}(\theta^{-1})$ equals $u_\ast$ of the class of $c$. For $n=1$ this is the identity
$$c(\theta^{-1}h\theta)-\rho_j(\theta)^{-1}c(h)=\rho_j(\theta^{-1}h\theta)\,m_0-m_0,\qquad m_0=\rho_j(\theta)^{-1}c(\theta),$$
which follows from the cocycle relation, where $\rho_j=\rho\circ i_j^{-1}$. [Paper] [Milne, *Arithmetic Duality Theorems*, Proposition 0.15, p. 11](https://www.jmilne.org/math/Books/ADTnot.pdf). Isomorphisms preserve orders. $\square$

**Remark (the archive needs only orders).** [Lean, read] In `localEulerChar_holds` (`CardH1EqCardH0MulCardH2.lean:62–92`) the call `obtain ⟨K, hK, i0, -, -, hdeg⟩ := decEquiv …` keeps $K$, its finiteness, the isomorphism and, in the branch at $\ell$, the degree equality. The cyclotomic and inertia outputs are discarded. The branch away from $\ell$ uses the residue characteristic as $p$ and also discards the degree. The representation `rhoK` is $\rho\circ i^{-1}$, and its continuity is obtained by composing with the continuous inverse. The Euler formula for `rhoK` is `top_euler` or `card_H1_eq_card_H0_mul_card_H2`. It is rewritten with `hdeg` and carried back by `Nat.card_congr` along the three transport isomorphisms. The conclusion is an equality of natural numbers, and by part (c) of the corollary any two choices give isomorphic groups. So the hidden choice of $j$ in `decEquiv` cannot affect it. The archive proves no independence statement, and the Euler count does not need one. As recorded in §18.3.7, the archive supplies this field through `loceuler_holds := localEulerChar_holds` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LoceulerHolds.lean:8`). `GC.locEuler` takes the resulting `LocalEulerChar` as its third hypothesis (`LocEuler.lean:68–71`), and `ExAbove.lean:97,125–131` evaluates it at the quotients $W/b_v$.

**Remark (comparison with the literature).** [Paper] For a finite Galois extension $L/F$ the classical statement is that the decomposition group $G_w$ maps isomorphically onto $\operatorname{Gal}(L_w/F_v)$ and that $G_{\tau w}=\tau G_w\tau^{-1}$. Milne proves the isomorphism by counting: injectivity gives $(G_w:1)\le[L_w:F_v]$, and summing over the places above $v$ against $[L:F]$ forces equality. [Milne, *Algebraic Number Theory*, Proposition 8.10, p. 139](https://www.jmilne.org/math/CourseNotes/ANT.pdf). The archive argues at the level of the full algebraic closure and does not count. Its inverse map is restriction (Step 3), and surjectivity comes from extending an isometry from a dense subfield, Lemma 1(4). Milne also records the conjugation behaviour of the localization maps. An embedding $F^{\mathrm{sep}}\to F_v^{\mathrm{sep}}$ over $F$ identifies $G_{F_v}$ with a decomposition group. A second embedding differs by $\operatorname{ad}(\sigma)$ for some $\sigma\in G_F$, and Proposition 0.15 makes $H^r(G_F,M)\to H^r(G_{F_v},M)$ independent of the embedding. [Milne, *Arithmetic Duality Theorems*, p. 11](https://www.jmilne.org/math/Books/ADTnot.pdf). In the notation of the corollary, the independence holds once the transported modules are identified through the conjugating element, as $u$ does in part (c), or through the embedding itself, as for $\mu_3$ in the first example. With the identity of $M$ the transports differ, as that example shows. Corollary (b) is the archive's version of the underlying cochain identity.

**Read boundary.** [Open] The [source ledger](../sources/SOURCES.md#chapter-18-1838-completion-comparison) records the archive and literature editions. R3 [Lean, read] covers the bodies of the following declarations.
- `exists_place_below`, `exists_root_of_unity`, `norm_lt_one_iff`, `finrank_closure_eq_locDeg` and `decEquiv` (`DecompositionGroupEquivLocalGaloisGroup.lean:18–100`), with the wrapper `T.decomposition_group_equiv_local_galois_group`.
- `val_int_lt_one_iff`, `norm_l_lt_one`, `exists_embedding`, `denseRange_embedding`, `norm_eq_of_le_one_iff`, `exists_algEquiv`, `norm_algEquiv`, `algEquiv_ext`, `finiteDimensional_adjoin_range`, `adjoin_range_subset_closure`, `mem_GK_iff`, `exists_restrict` and `exists_mulEquiv` (`FiniteDimensionalAdjoinRange.lean:8–299`).
- `DecGalois.exists_continuousMulEquiv`, `fixingSubgroupEquiv_bicontinuous`, `valuation_lt_one_iff_norm` and `inertiaK_iff_mem_Ine`, with the wrappers `T.exists_decompositionGroup_equiv_padicGalois` and `T.localInertia_iff_mem_placeInertia`.
- `mem_span_l_iff` and `locDegOf_of` (`MemSpanLIff.lean:9–71`); `exists_smul_eq_of_isPlaceOver` and the body of `exists_smul_eq_of_over`.
- `invariants_eq_of_iso` and `equivH0OfIso`–`equivH2OfIso`; `local_compat`, `res_h1_iso_h1` and `res_h2_iso_h2`; the definitions `resH1`, `resH2`, `pairH1DecompositionMap` and `compatiblePairH2`.

The proofs of the four counting theorems `ballCard`, `denseSurj`, `kerProp` and `normCard` are read in [§18.3.9](#1839-counting-the-local-degree-closed-balls-integral-approximation-and-the-power-kernel). The following are named inputs whose proofs were not read: `placeProp` and the integral-closure helpers of `exists_smul_eq_of_over` (`primeBelow`, `under_primeBelow`, `primeBelow_smul`, `eq_of_valuation_lt_one_iff`, `isInvariant_intCl`, `continuousSMul_intCl`). The Mathlib lemmas used are checked at the pinned commit by statement only: continuity of roots, the Krull-topology lemmas, invariance of the spectral norm, equivalence of absolute values, the compact-to-Hausdorff lemma and `fixingSubgroupEquiv`. Part 6 of the theorem and Corollary (c) are proved here and are not Lean declarations. The examples use the [Paper] results cited in them. The two-row lemma, the Euler formula, `tate_core`, the cochain comparisons `gcRep`, `gc0`, `gc1`, `gc2`, `gcn`, the Brauer invariants and the Chapter 12 global boundary keep the read levels given in §18.3.7 and Chapter 12.


### 18.3.9 Counting the local degree: closed balls, integral approximation and the power kernel

**Motivation.** Part 4 of Theorem 18.3.8 asserts $[K_j:\mathbb Q_p]=\operatorname{locDeg}(w)=e(w/p)f(w/p)$. Apart from the group isomorphism, it is the only output of `decEquiv` that `localEulerChar_holds` uses. In the branch of `localEulerChar_holds` at places above $\ell$, `top_euler` gives $|H^1|=|H^0|\,|H^2|\,|M|^{[K:\mathbb Q_\ell]}$, as stated in `LocalEulerCharK` (`src/Formalism/GaloisCohomology/LocalTateDualityK.lean:57–61`). The interface `LocalEulerCharAt` asks for the exponent $\operatorname{locDeg}(v)$ instead (`src/ReciprocityTheory/Hypotheses/GalCoh.lean:58`). The rewrite `rw [hdeg v hA] at h` at `src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CardH1EqCardH0MulCardH2.lean:74` bridges the two. In §18.3.8 the degree equality was reduced to four counting statements, `BallCard`, `DenseSurj`, `KerProp` and `NormCard`, together with `placeProp`. This subsection reads the proofs of the four counting statements.

The idea is to count one finite ring in two ways. Let $\varphi=j|_F$ and let $\mathcal O_K=\{y\in K:|y|\le1\}$ be the closed unit ball of $K=K_j$. The map $\varphi$ induces
$$\mathcal O_F/w^{e}\longrightarrow\mathcal O_K/p\,\mathcal O_K .$$
The left side has $p^{ef}$ elements. It has $e$ layers $w^k/w^{k+1}$, and each layer is a copy of the residue field $\mathbb F_{p^f}$. The right side has $p^{[K:\mathbb Q_p]}$ elements, because $\mathcal O_K$ is a free $\mathbb Z_p$-module of rank $[K:\mathbb Q_p]$. If the map is bijective, the exponents agree. The archive never forms the completion of $F$ and never uses the uniqueness of extensions of absolute values. Three points need care. First, $\mathcal O_K$ is divided by $p$, not by its maximal ideal; the residue field of $K$ has only $p^f$ elements. Second, the kernel on the side of $F$ is $w^e$, not $w$. Third, surjectivity is an approximation statement, and its proof passes through a limit in $\overline{\mathbb Q}_p$.

**Setting.** As in the archive, $\overline{\mathbb Q}_p$ is `PadicAlgCl p`, an algebraic closure of $\mathbb Q_p$, and its norm is the spectral norm. If $X^d+a_{d-1}X^{d-1}+\dots+a_0$ is the minimal polynomial of $z$ over $\mathbb Q_p$, then
$$|z|=\max_{0\le n<d}|a_n|^{1/(d-n)}.$$
At the pinned Mathlib commit this formula is the definition of the norm, not a theorem: the norm of `PadicAlgCl p` is `spectralNorm` by `rfl`, and `spectralNorm` is the `spectralValue` of the minimal polynomial. The norm extends $|\cdot|_p$, so $|p|=p^{-1}$, and it is nonarchimedean. Throughout, $F$ is a number field, $\varphi\colon F\to\overline{\mathbb Q}_p$ is a ring homomorphism and $K\subset\overline{\mathbb Q}_p$ is a finite extension of $\mathbb Q_p$ with $\varphi(F)\subseteq K\subseteq\overline{\varphi(F)}$; the bar denotes closure in $\overline{\mathbb Q}_p$. For a maximal ideal $w$ of $\mathcal O_F$ containing $p$ write $e=e(w/p)$, $f=f(w/p)$, and $\operatorname{ord}_w$ for the $w$-adic valuation on $F^\times$. The condition
$$\text{(P)}\qquad|\varphi(x)|\le1\quad\text{and}\quad\bigl(|\varphi(x)|<1\iff x\in w\bigr)\qquad\text{for all }x\in\mathcal O_F$$
says that $w$ is the place of $F$ cut out by $\varphi$.

**First example — a ramified quadratic field.** Let $F=\mathbb Q(i)$ and $p=2$. Choose $\iota\in\overline{\mathbb Q}_2$ with $\iota^2=-1$ and put $\varphi(a+bi)=a+b\iota$. Squares of units of $\mathbb Z_2$ are $1$ modulo $8$, so $-1$ is not a square in $\mathbb Q_2$. Hence $K=\mathbb Q_2(\iota)$ has degree $2$, and $K\subseteq\overline{\varphi(F)}$ because $\mathbb Q$ is dense in $\mathbb Q_2$. In $\mathcal O_F=\mathbb Z[i]$ one has $2=-i(1+i)^2$. So $w=(1+i)$ is the only prime above $2$, with $e=2$, $\mathcal O_F/w=\mathbb F_2$, $f=1$ and $\operatorname{locDeg}(w)=2$. [Paper] [Milne, *Algebraic Number Theory*, p. 59](https://www.jmilne.org/math/CourseNotes/ANT.pdf).

*Norms.* For $a,b\in\mathbb Q_2$ with $b\ne0$, the minimal polynomial of $a+b\iota$ is $X^2-2aX+(a^2+b^2)$, so
$$|a+b\iota|=\max\bigl(|2a|,\ |a^2+b^2|^{1/2}\bigr).$$
For $b=0$ the norm is $|a|$, and the conclusions below hold in that case too. For $x=a+bi\in\mathbb Z[i]$ the formula gives $|\varphi(x)|\le1$. Since $|2a|\le\tfrac12$, we have $|\varphi(x)|<1$ exactly when $a^2+b^2$ is even, that is, when $a\equiv b\pmod 2$, that is, when $x\in w$. So (P) holds.

*The closed ball.* Let $a,b\in\mathbb Q_2$ with $b\ne0$ and $|a+b\iota|\le1$, so $|2a|\le1$ and $|a^2+b^2|\le1$. If $a\in\mathbb Z_2$, then $b^2=(a^2+b^2)-a^2$ is integral and $b\in\mathbb Z_2$. If $a\notin\mathbb Z_2$, then $a=a'/2$ with $a'$ a unit, and $|a^2+b^2|\le1$ forces $b=b'/2$ with $b'$ a unit. But then $a'^2+b'^2\equiv2\pmod 8$, so $|a^2+b^2|=2$, a contradiction. Hence $\mathcal O_K=\mathbb Z_2\oplus\mathbb Z_2\iota$. The quotient $\mathcal O_K/2\mathcal O_K$ consists of the four classes $a+b\iota$ with $a,b\in\{0,1\}$, so it has $p^{[K:\mathbb Q_p]}=2^2$ elements. It is not a field, since $(1+\iota)^2=2\iota\equiv0$. Its quotient by the maximal ideal, the residue field $\mathcal O_K/(1+\iota)=\mathbb F_2$, has only $p^f=2$ elements.

*The kernel.* For $x=a+bi\in\mathbb Z[i]$, the condition $|\varphi(x)|\le|2|=\tfrac12$ means $|a^2+b^2|\le\tfrac14$. Thus $4\mid a^2+b^2$, and since squares are $0$ or $1$ modulo $4$, $a$ and $b$ are even. The kernel of $\mathcal O_F\to\mathcal O_K/2\mathcal O_K$ is therefore $2\mathbb Z[i]=w^2$. The element $1+i$ lies in $w$ but not in the kernel, since $|\varphi(1+i)|=|2|^{1/2}=2^{-1/2}>|2|$. The kernel is $w^e$, not $w$. Correspondingly $|\mathcal O_F/w^2|=4=2^{ef}$, made of two layers $\mathcal O_F/w$ and $w/w^2$ with two elements each, while $|\mathcal O_F/w|=2=p^f$.

*Surjectivity.* We follow the proof of Lemma C below for an element of $\mathcal O_K$ that is not in $\varphi(F)$. Since $-7\equiv1\pmod 8$, there is $s\in\mathbb Z_2$ with $s^2=-7$; replacing $s$ by $-s$ if necessary, $s\equiv5\pmod{16}$. It is a $2$-adic limit and not a rational number. Density of $\varphi(F)$ supplies some $e_0\in F$ with $|s-\varphi(e_0)|<|2|$; one choice is $e_0=7/3$, because $3s-7\equiv8\pmod{16}$ gives $|s-7/3|=|3s-7|=2^{-3}$. The denominator $3$ is prime to $w$. The ideal $I=\{x\in\mathcal O_F:|\varphi(x)|\le|2|\}$ is $2\mathbb Z[i]$ by the kernel computation, and $1=1\cdot3+(-2)$ with $-2\in I$. So the inverse of $3$ modulo $I$ is $t=1$, and the integral approximant is $x=7t=7$. Indeed $\varphi(e_0)-\varphi(7)=\varphi(e_0)\cdot(-2)$ has norm $\tfrac12$, so $|s-7|\le\max(2^{-3},2^{-1})=|2|$. Hence the class of $s$ in $\mathcal O_K/2\mathcal O_K$ is the image of $7$, that is, of $1$.

*The count.* The map $\mathcal O_F\to\mathcal O_K/2\mathcal O_K$ is surjective with kernel $w^2$, so $\mathcal O_F/w^2\simeq\mathcal O_K/2\mathcal O_K$. Both sides have $4$ elements, and $2^{ef}=2^{[K:\mathbb Q_2]}$ gives $[K:\mathbb Q_2]=2=e\cdot f$. If one replaced $w^e$ by $w$, or $2\mathcal O_K$ by the maximal ideal $(1+\iota)$, both sides would have $2=p^f$ elements, and the count would return only $f$.

**Second example — an unramified quadratic field.** Let $F=\mathbb Q(\sqrt5)$, $p=2$ and $\gamma=(1+\sqrt5)/2$. Then $\mathcal O_F=\mathbb Z[\gamma]$ and $\gamma^2=\gamma+1$. [Paper] [Milne, *Algebraic Number Theory*, p. 8 and Example 2.41, p. 39](https://www.jmilne.org/math/CourseNotes/ANT.pdf). The polynomial $X^2-X-1$ has no root in $\mathbb F_2$, so $w=2\mathcal O_F$ is prime and $\mathcal O_F/w\simeq\mathbb F_4$. Thus $e=1$, $f=2$ and $\operatorname{locDeg}(w)=2$ [Milne, *ANT*, Theorem 3.41, pp. 62–63]. Let $g\in\overline{\mathbb Q}_2$ be a root of $X^2-X-1$ and put $\varphi(a+b\gamma)=a+bg$. A root in $\mathbb Q_2$ would lie in $\mathbb Z_2$ and give a root modulo $2$, so $K=\mathbb Q_2(g)$ has degree $2$. As in the first example, $K=\mathbb Q_2\oplus\mathbb Q_2g\subseteq\overline{\varphi(F)}$ because $\mathbb Q$ is dense in $\mathbb Q_2$.

*Norms.* For $b\ne0$ the minimal polynomial of $a+bg$ is $X^2-(2a+b)X+(a^2+ab-b^2)$. The form $a^2+ab-b^2$ is odd whenever $a,b\in\mathbb Z_2$ are not both even. Now let $c,d\in\mathbb Q_2$, not both zero, and let $m=\min(\operatorname{ord}_2c,\operatorname{ord}_2d)$. Then $c^2+cd-d^2$ is $4^m$ times an odd number, and $|2c+d|\le2^{-m}$, so
$$|c+dg|=\max(|c|,|d|).$$
In particular the values of $|\cdot|$ on $K^\times$ are the powers of $2$, and no value lies strictly between $\tfrac12$ and $1$. For $x=a+b\gamma\in\mathbb Z[\gamma]$ we get $|\varphi(x)|\le1$, with $|\varphi(x)|<1$ exactly when $a$ and $b$ are even, that is, when $x\in w$. So (P) holds.

*The closed ball.* By the norm formula, $\mathcal O_K=\mathbb Z_2\oplus\mathbb Z_2 g$, and $\mathcal O_K/2\mathcal O_K=\mathbb F_2[\bar g]\simeq\mathbb F_4$ is a field with $p^{[K:\mathbb Q_p]}=4$ elements. Here the residue field already has $p^{[K:\mathbb Q_p]}$ elements, because $e=1$. The ball is the integral closure of $\mathbb Z_2$, not the ring generated by a chosen square root. Since $\sqrt5=2g-1$, the ring $\mathbb Z_2[\sqrt5]=\mathbb Z_2\oplus2\mathbb Z_2 g$ has index $2$ in $\mathcal O_K$, and $g=(1+\sqrt5)/2$ lies in the ball but not in $\mathbb Z_2[\sqrt5]$. The integrality test for $a+b\sqrt d$ in a quadratic field, $2a\in\mathbb Z$ and $a^2-b^2d\in\mathbb Z$, is the global counterpart of Lemma A(1) below [Milne, *ANT*, p. 8].

*The kernel.* By the norm formula, $|\varphi(x)|\le\tfrac12$ holds exactly when $|\varphi(x)|<1$, that is, when $x\in w$. Here $w^e=w$, and $|\mathcal O_F/w|=4=2^{ef}=2^f$.

*Surjectivity.* A primitive cube root of unity lies in $\mathcal O_K$ but not in $\varphi(F)$, because $F$ is real. Since $-3/5\equiv1\pmod 8$, there is $u\in\mathbb Z_2$ with $u^2=-3/5$; of the two roots $\pm u$, we take the one with $u\equiv3\pmod 8$. Then $(u(2g-1))^2=5u^2=-3$, so
$$\zeta=\frac{-1+u(2g-1)}2=-\frac{1+u}2+u\,g$$
satisfies $\zeta^2+\zeta+1=0$, and its coordinates are in $\mathbb Z_2$. As $3\cdot3\equiv1\pmod 8$, we have $u\equiv1/3\pmod 8$. Density supplies, for instance, $e_0=(\gamma-2)/3$, with
$$|\zeta-\varphi(e_0)|=\max\Bigl(\Bigl|\frac23-\frac{1+u}2\Bigr|,\ \Bigl|u-\frac13\Bigr|\Bigr)=\max\Bigl(2\,|1-3u|,\ |3u-1|\Bigr)\le\tfrac14<|2|.$$
Here $e_0=a/s$ with $a=\gamma-2$ and $s=3\notin w$, and again $1=1\cdot3+(-2)$ with $-2\in I=w$. The integral approximant is $x=\gamma-2$, and $|\zeta-\varphi(\gamma-2)|=\tfrac12$. So $\zeta\equiv g\pmod{2\mathcal O_K}$. This is consistent with the fact that both reduce to roots of $X^2+X+1$ in $\mathbb F_4$; the other root is $\bar g+1$, which corresponds to $u\equiv5\pmod 8$.

*The count.* The map $\mathcal O_F/w\to\mathcal O_K/2\mathcal O_K$ is an isomorphism $\mathbb F_4\simeq\mathbb F_4$, and $[K:\mathbb Q_2]=2=1\cdot2$. Compared with the first example, the same order $4=2^{[K:\mathbb Q_2]}$ splits as $(2^f)^e$ with $(e,f)=(1,2)$ instead of $(2,1)$.

*Layer by layer.* Repeat the approximation. The difference $(\zeta-g)/2=-\frac{1+u}4+\frac{u-1}2\,g$ lies in $\mathcal O_K$. Its coordinates are odd, because $u\equiv59\pmod{64}$, so it is congruent to $\varphi(1+\gamma)$ modulo $2\mathcal O_K$. Hence $\zeta\equiv\varphi(\gamma+2(1+\gamma))=\varphi(2+3\gamma)\pmod{4\mathcal O_K}$. Continuing gives $z_n\in\mathcal O_F$ with $|\zeta-\varphi(z_n)|\le2^{-n}$. No element of $\mathcal O_F$ maps to $\zeta$, so $\zeta$ itself is reached only by a limit of the $z_n$. Corollary 18.3.9.1 makes this precise.

**Definition.** The following are the archive's notions. Unless a path is given, files are in `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/`.
1. For a finite extension $K\subset\overline{\mathbb Q}_p$ of $\mathbb Q_p$, the closed ball $\mathcal O_K=\{y\in K:|y|\le1\}$ is the subring `ball K` (`DenseSurj.lean:8–18`). Multiplicativity and the ultrametric inequality make it a subring.
2. The places of $F$ over $p$ are the maximal ideals $w$ of $\mathcal O_F$ with $p\in w$ (`placesOver`, `src/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:35–36`).
3. The ramification index $e(w/p)$ is `w.asIdeal.ramificationIdx ℤ`. Mathlib defines it as the length of $\mathcal O_{F,(w)}/p\,\mathcal O_{F,(w)}$ over the local ring $\mathcal O_{F,(w)}$, and `ramificationIdx_eq_factors_count` identifies it with the exponent of $w$ in $p\mathcal O_F$. The residue degree $f(w/p)$ is `w.asIdeal.inertiaDeg ℤ`, the degree of the residue field of $w$ over $\mathbb F_p$. The local degree is $\operatorname{locDeg}(w)=e(w/p)f(w/p)$ (`src/ReciprocityTheory/Hypotheses/GalCohDefs.lean:132–133`). The definition `N.locDeg` used in `LocDegOf` has the same body (`src/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean:35–36`).
4. The counting statements are quantified over all primes $p$ (named `l` in the archive), number fields $F$, homomorphisms $\varphi$, finite extensions $K$ and places $w$ over $p$ (`DenseSurj.lean:25–50`):
   - `BallCard`: $|\mathcal O_K/p\mathcal O_K|=p^{[K:\mathbb Q_p]}$.
   - `DenseSurj`: if $\varphi(F)\subseteq K\subseteq\overline{\varphi(F)}$, every $y\in\mathcal O_K$ has some $x\in\mathcal O_F$ with $|y-\varphi(x)|\le|p|$.
   - `KerProp`: if (P) holds, then $|\varphi(x)|\le|p|\iff x\in w^{e(w/p)}$ for every $x\in\mathcal O_F$.
   - `NormCard`: $|\mathcal O_F/w^{e(w/p)}|=p^{\operatorname{locDeg}(w)}$.
   - `LocDegOf`: if $\varphi(F)\subseteq K\subseteq\overline{\varphi(F)}$ and (P) holds, then $[K:\mathbb Q_p]=\operatorname{locDeg}(w)$.

   Cardinalities are `Nat.card`, which is $0$ on infinite types. Every quotient below is shown to be finite.

**Lemma A (the closed ball).** [Lean, read] Let $K\subset\overline{\mathbb Q}_p$ be finite over $\mathbb Q_p$.
1. For $z\in\overline{\mathbb Q}_p$, $|z|\le1$ if and only if $z$ is integral over $\mathbb Z_p$.
2. $\mathcal O_K$ is the integral closure of $\mathbb Z_p$ in $K$.
3. For $y\in\mathcal O_K$, $y\in p\mathcal O_K$ if and only if $|y|\le|p|$.

**Proof.** (1) Let $P=X^d+a_{d-1}X^{d-1}+\dots+a_0$ be the minimal polynomial of $z$ over $\mathbb Q_p$. Each exponent $1/(d-n)$ is positive, so $|z|=\max_n|a_n|^{1/(d-n)}\le1$ exactly when $|a_n|\le1$ for all $n$, that is, when $P\in\mathbb Z_p[X]$. This is the private lemma `spectralValue_le_one_iff_norm_coeff_le_one` in `MemIntegralClosureIffMemBall.lean:23–48`. If $P\in\mathbb Z_p[X]$, then $P$ is a monic integral equation for $z$. Conversely, let $z$ be integral over $\mathbb Z_p$. Since $\mathbb Z_p$ is integrally closed, the minimal polynomial over $\mathbb Q_p$ is the image of the minimal polynomial over $\mathbb Z_p$ (Mathlib `minpoly.isIntegrallyClosed_eq_field_fractions'`). Hence $P\in\mathbb Z_p[X]$. This is `norm_le_one_iff_isIntegral`, `:50–69`.

(2) Integrality of $x\in K$ over $\mathbb Z_p$ can be tested in $\overline{\mathbb Q}_p$, because the inclusion of $K$ is injective. Apply (1) (`mem_integralClosure_iff_mem_ball`, `:71–78`).

(3) If $y=pz$ with $|z|\le1$, then $|y|\le|p|$. If $|y|\le|p|$, then $z=y/p\in K$ has $|z|\le1$. This is `mem_span_l_iff` in `MemSpanLIff.lean:9–38`, read in §18.3.8. $\square$

**Lemma B (counting $\mathcal O_K/p$).** [Lean, read] $|\mathcal O_K/p\mathcal O_K|=p^{[K:\mathbb Q_p]}$.

**Proof.** First a general count (`card_quot_l`, `MemIntegralClosureIffMemBall.lean:80–120`). Let $C$ be a commutative $\mathbb Z_p$-algebra with a $\mathbb Z_p$-basis $b_1,\dots,b_n$. Define $f\colon C\to\mathbb F_p^n$ by sending $x=\sum c_ib_i$ to $(c_i\bmod p)_i$. This map is additive. It is surjective, since a vector of residues is the image of $\sum r_ib_i$, where $0\le r_i<p$ are integer representatives. Its kernel contains $pC$, because $p\sum c_ib_i$ has coordinates $pc_i$. Conversely, if every $c_i$ reduces to $0$, then $c_i\in\ker(\mathbb Z_p\to\mathbb F_p)=p\mathbb Z_p$ (Mathlib `PadicInt.ker_toZMod` and `PadicInt.maximalIdeal_eq_span_p`). Writing $c_i=pd_i$ gives $x=p\sum d_ib_i\in pC$. Hence $C/pC\simeq\mathbb F_p^n$ and $|C/pC|=p^n$.

Now let $C$ be the integral closure of $\mathbb Z_p$ in $K$. By Lemma A(2), $\mathcal O_K$ and $C$ are the same subset of $K$. The identity is a ring isomorphism carrying $p\mathcal O_K$ onto $pC$, so the two quotients have the same order (`ballCard`, `:122–141`, via `Ideal.quotientEquiv`). The ring $\mathbb Z_p$ is a principal ideal domain, $K/\mathbb Q_p$ is finite and separable, and $K$ is torsion-free over $\mathbb Z_p$ (`isTorsionFree_finExt`, `:14–21`). Mathlib's theorems on integral closures then make $C$ a finite free $\mathbb Z_p$-module of rank $[K:\mathbb Q_p]$ (`IsIntegralClosure.finite`, `IsIntegralClosure.module_free` and `IsIntegralClosure.rank`). Apply the count with $n=[K:\mathbb Q_p]$. $\square$

**Lemma C (integral approximation modulo $p$).** [Lean, read] Let $y\in\overline{\varphi(F)}$ with $|y|\le1$. Then there is $x\in\mathcal O_F$ with $|y-\varphi(x)|\le|p|$. In particular `DenseSurj` holds.

**Proof.** The archive proves this as `denseSurj` (`ExistsDen.lean:100–212`). Its statement also contains $K$ and the inclusion $\varphi(F)\subseteq K$; the proof uses only $y\in K\subseteq\overline{\varphi(F)}$.

*Step 1 (integers have norm at most one).* Let $x\in\mathcal O_F$ and $z=\varphi(x)$. Then $z^n+c_{n-1}z^{n-1}+\dots+c_0=0$ for some $n\ge1$ and $c_i\in\mathbb Z$, and $|c_i|\le1$. If $|z|>1$, the ultrametric inequality gives $|z|^n\le\max_i|c_i|\,|z|^i\le|z|^{n-1}<|z|^n$, which is absurd. Hence $|z|\le1$. This is the private lemma `norm_le_one_of_isIntegral_int'` (`:60–98`), used at `:103–104`.

*Step 2 (an approximation from $F$).* Since $y$ lies in the closure of $\varphi(F)$ and $|p|>0$, there is $e_0\in F$ with $|y-\varphi(e_0)|<|p|$ (`Metric.mem_closure_iff`, `:116–117`). Then $|\varphi(e_0)|\le\max(|y|,|\varphi(e_0)-y|)\le1$ (`:118–124`). This is the only step that involves a limit. In general $y\notin\varphi(F)$, and $e_0$ is one term of a sequence in $F$ whose image converges to $y$.

*Step 3 (the place of $\varphi$).* The set $w_\varphi=\{x\in\mathcal O_F:|\varphi(x)|<1\}$ is an ideal, by Step 1 and the ultrametric inequality. It does not contain $1$. It is prime: if $a,b\notin w_\varphi$, then $|\varphi(a)|=|\varphi(b)|=1$ by Step 1, so $|\varphi(ab)|=1$. It contains $p$, so it is nonzero (`:125–162`). By Step 1, $|\varphi(s)|=1$ for every $s\in\mathcal O_F\setminus w_\varphi$.

*Step 4 (a denominator prime to $w_\varphi$).* There are $a,s\in\mathcal O_F$ with $s\notin w_\varphi$ and $e_0s=a$ (`exists_den`, `:7–58`). Write $e_0=a'/d$ with $a',d\in\mathcal O_F$ and $d\ne0$. The localization $R$ of $\mathcal O_F$ at $w_\varphi$ is a discrete valuation ring, so one of $a',d$ divides the other in $R$. Write the quotient as $r/r'$ with $r\in\mathcal O_F$ and $r'\notin w_\varphi$. If $d\cdot r/r'=a'$, then $dr=a'r'$ in $\mathcal O_F$, so $e_0r'=r$; take $(a,s)=(r,r')$. If $a'\cdot r/r'=d$, then $e_0r=r'$. In this case $r\in w_\varphi$ is impossible, since it would give $1=|\varphi(r')|=|\varphi(e_0)|\,|\varphi(r)|<1$. So $r\notin w_\varphi$, and we take $(a,s)=(r',r)$.

*Step 5 (inverting the denominator).* Let $I=\{x\in\mathcal O_F:|\varphi(x)|\le|p|\}$, an ideal by the same estimates (`:164–173`). We claim $s\mathcal O_F+I=\mathcal O_F$ (`:174–188`). Otherwise $s\mathcal O_F+I$ lies in a maximal ideal $m$. For $x\in w_\varphi$ we have $|\varphi(x)|<1$, so $|\varphi(x^n)|<|p|$ for some $n$. Then $x^n\in I\subseteq m$, so $x\in m$. Thus $w_\varphi\subseteq m$. Nonzero primes of $\mathcal O_F$ are maximal, so $w_\varphi=m$, which contradicts $s\in m$ and $s\notin w_\varphi$. Hence $1=ts+u$ with $t\in\mathcal O_F$ and $u\in I$.

*Step 6 (the integral approximant).* Put $x=at\in\mathcal O_F$. Then
$$\varphi(e_0)-\varphi(x)=\varphi(e_0)\bigl(1-\varphi(s)\varphi(t)\bigr)=\varphi(e_0)\varphi(u),$$
which has norm at most $|p|$. Hence $|y-\varphi(x)|\le\max(|y-\varphi(e_0)|,|\varphi(e_0)-\varphi(x)|)\le|p|$ (`:198–212`). $\square$

When $w_\varphi=w$, Lemma D below shows $I=w^e$. The proof of Lemma C does not need this. The precision $|p|$ is the one the count requires, because by Lemma A(3) an approximation within $|p|$ determines the class modulo $p\mathcal O_K$.

**Lemma D (the power kernel).** [Lean, read] Let $w$ be a maximal ideal of $\mathcal O_F$ with $p\in w$, and assume (P). Then, for $x\in\mathcal O_F$, $|\varphi(x)|\le|p|$ if and only if $x\in w^{e}$, where $e=e(w/p)$. This is `kerProp`.

**Proof.** The archive writes the valuation multiplicatively, as `v.valuation` $=\exp(-\operatorname{ord}_w)$; we use $\operatorname{ord}_w$. All line numbers refer to `IsEquivAdicAbvNormAbv.lean`.

*Step 1 (`frac_lemma'`, `:18–54`).* If $u\in F$ and $\operatorname{ord}_w(u)\ge0$, then $u=c/j$ with $c,j\in\mathcal O_F$ and $j\notin w$. Write $u=a/d$ with $d\ne0$ and let $k=\operatorname{ord}_w(d)$. Then $w^k$ divides both $(a)$ and $(d)$. Write $(d)=w^kJ$. The ideal $J$ is not contained in $w$, since otherwise $w^{k+1}\mid(d)$. Choose $j\in J\setminus w$. Then $aj\in w^kJ=(d)$, say $aj=cd$, and $u=a/d=c/j$.

*Step 2 (`le_one_lemma_2`, `:56–94`).* For every $u\in F$, $\operatorname{ord}_w(u)\ge0$ if and only if $|\varphi(u)|\le1$, and $\operatorname{ord}_w(u)>0$ if and only if $|\varphi(u)|<1$. By (P), every $j\in\mathcal O_F\setminus w$ has $|\varphi(j)|=1$. Suppose $\operatorname{ord}_w(u)\ge0$ and write $u=c/j$ as in Step 1. Then $|\varphi(u)|=|\varphi(c)|\le1$. If moreover $\operatorname{ord}_w(u)>0$, then $\operatorname{ord}_w(c)>0$, so $c\in w$ and $|\varphi(u)|<1$. For the converses let $u\ne0$. If $\operatorname{ord}_w(u)<0$, the forward statements applied to $u^{-1}$ give $|\varphi(u)|>1$. If $\operatorname{ord}_w(u)\le0$, they give $|\varphi(u)|\ge1$.

*Step 3 (`intValuation_natCast`, `:106–131`).* $\operatorname{ord}_w(p)=e$. Indeed $w$ lies over $p\mathbb Z$, and the multiplicity of $w$ in the factorization of $p\mathcal O_F$ is the ramification index (Mathlib `Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count`).

*Step 4 (`kerProp`, `:133–150`).* Apply Step 2 to $u=x/p$:
$$|\varphi(x)|\le|p|\iff|\varphi(x/p)|\le1\iff\operatorname{ord}_w(x)\ge\operatorname{ord}_w(p)=e\iff w^e\mid(x)\iff x\in w^e. \qquad\square$$

Step 2 says that $x\mapsto|\varphi(x)|$ and the $w$-adic absolute value define the same closed and open unit balls on $F$. The same file proves the resulting equivalence of absolute values as `isEquiv_adicAbv_normAbv` (`:96–104`), but `kerProp` uses only Step 2. Replacing $p$ by $p^n$ in Step 4 gives $|\varphi(x)|\le|p|^n\iff x\in w^{en}$.

**Lemma E (counting $\mathcal O_F/w^e$).** [Lean, read] For a maximal ideal $w$ of $\mathcal O_F$ with $p\in w$, $|\mathcal O_F/w^{e}|=p^{ef}$. This is `normCard`.

**Proof.** Since $p\in w$ and $p\mathbb Z$ is maximal, $w\cap\mathbb Z=p\mathbb Z$ (`liesOver_of_mem`, `SpanLIsMaximal.lean:15–28`). The absolute norm $N(\mathfrak a)=|\mathcal O_F/\mathfrak a|$ is multiplicative on ideals (Mathlib `Ideal.absNorm`), so $|\mathcal O_F/w^e|=N(w)^e$. The residue field $\mathcal O_F/w$ has dimension $f$ over $\mathbb Z/p$, so $N(w)=p^f$. In Mathlib this is `absNorm_eq_pow_inertiaDeg'_of_liesOver`, with $N(p\mathbb Z)=p$ from `absNorm_span_natCast`; `inertiaDeg'_eq_inertiaDeg` matches the two definitions of $f$. Hence $|\mathcal O_F/w^e|=(p^f)^e=p^{ef}$ (`normCard`, `SpanLIsMaximal.lean:30–41`). $\square$

The multiplicativity of the norm hides the layers of the introduction. Each $w^k/w^{k+1}$ is a one-dimensional $\mathcal O_F/w$-vector space, since no ideal lies strictly between $w^k$ and $w^{k+1}$. Hence each layer has $p^f$ elements. [Paper] [Milne, *Algebraic Number Theory*, proof of Theorem 3.34, pp. 59–60](https://www.jmilne.org/math/CourseNotes/ANT.pdf).

**Theorem 18.3.9 (the local degree by counting).** [Lean, read] Let $F$ be a number field, $p$ a prime, $\varphi\colon F\to\overline{\mathbb Q}_p$ a ring homomorphism and $K\subset\overline{\mathbb Q}_p$ a finite extension of $\mathbb Q_p$ with $\varphi(F)\subseteq K\subseteq\overline{\varphi(F)}$. Let $w$ be a maximal ideal of $\mathcal O_F$ containing $p$ such that (P) holds, and put $e=e(w/p)$ and $f=f(w/p)$.
1. $\varphi$ maps $\mathcal O_F$ into $\mathcal O_K$. The composite $q\colon\mathcal O_F\to\mathcal O_K\to\mathcal O_K/p\mathcal O_K$ is a surjective ring homomorphism with kernel $w^e$.
2. $q$ induces a ring isomorphism $\mathcal O_F/w^e\simeq\mathcal O_K/p\mathcal O_K$. Both sides have $p^{ef}=p^{[K:\mathbb Q_p]}$ elements.
3. $[K:\mathbb Q_p]=e(w/p)f(w/p)=\operatorname{locDeg}(w)$.

In Lean, parts 1–3 are `locDegOf_of` applied to `ballCard`, `denseSurj`, `kerProp` and `normCard` (`MemSpanLIff.lean:40–71`). Its application to an adapted embedding is `finrank_closure_eq_locDeg` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DecompositionGroupEquivLocalGaloisGroup.lean:67–83`), which is part 4 of Theorem 18.3.8.

**Proof.** Line numbers refer to `MemSpanLIff.lean`. By (P), $|\varphi(x)|\le1$ for $x\in\mathcal O_F$, and $\varphi(x)\in K$. So $\psi(x)=\varphi(x)$ defines a ring homomorphism $\psi\colon\mathcal O_F\to\mathcal O_K$, and $q$ is $\psi$ followed by reduction (`:43–49`).

*Surjectivity* (`:50–59`). Every class modulo $p\mathcal O_K$ is represented by some $y\in\mathcal O_K$. Lemma C gives $x\in\mathcal O_F$ with $|\psi(x)-y|\le|p|$. By Lemma A(3), $\psi(x)-y\in p\mathcal O_K$, so $q(x)$ is the class of $y$.

*Kernel* (`:60–65`). $q(x)=0$ means $\psi(x)\in p\mathcal O_K$. By Lemma A(3) this means $|\varphi(x)|\le|p|$, and by Lemma D it means $x\in w^e$.

*Count* (`:66–71`). The first isomorphism theorem gives part 2. Lemma E gives $|\mathcal O_F/w^e|=p^{ef}$ and Lemma B gives $|\mathcal O_K/p\mathcal O_K|=p^{[K:\mathbb Q_p]}$. Since $p\ge2$, the map $n\mapsto p^n$ is injective (`Nat.pow_right_injective`). Hence $[K:\mathbb Q_p]=ef$. $\square$

**The actual arguments.** [Lean, read] In `finrank_closure_eq_locDeg` (`DecompositionGroupEquivLocalGaloisGroup.lean:67–83`), the hypotheses of the theorem are supplied as follows.
- $\varphi$ is $j\circ(F\to\Omega)$ for an adapted embedding $j$ (`:73`).
- $K$ is $\mathbb Q_p(\varphi(F))$. It is finite by `finiteDimensional_adjoin_range` (`:80`); $\varphi(F)\subseteq K$ by `subset_adjoin` (`:81`); and $K\subseteq\overline{\varphi(F)}$ by `adjoin_range_subset_closure` (`:82`). The last holds because the closure of $\varphi(F)$ is a closed subfield containing $\mathbb Q$, hence containing $\mathbb Q_p$ by density of $\mathbb Q$ in $\mathbb Q_p$, hence containing $K$ (Step 1 of the proof of Theorem 18.3.8, `FiniteDimensionalAdjoinRange.lean:171–203`). So the limit in Step 2 of Lemma C ultimately comes from approximating $p$-adic numbers by rationals.
- $w$ is the place $v$ under $A$; $p\in v$ follows from `IsPlaceOver A v`, `norm_lt_one_iff` and $|p|<1$ (`:75–78`).
- In condition (P), the bound $|\varphi(x)|\le1$ is taken from `placeProp` (`:74`, used at `:83`). The equivalence $|\varphi(x)|<1\iff x\in v$ is `norm_lt_one_iff` (`:52–65`) composed with `IsPlaceOver` (`src/Formalism/ConjugateSelfDual/Statement.lean:20–21`).

So the closed ball of the archive is the ring of integers of $K_j$, by Lemma A. The ring $\mathcal O_F$ maps onto its quotient by $p$, by Lemma C, and the kernel of that map is the power $w^{e}$ with $e=$ `v.asIdeal.ramificationIdx ℤ`, by Lemma D. Mathematically, the bound in (P) is Step 1 of Lemma C. The Lean consumer obtains it from `placeProp`, a separate declaration that this subsection does not read at R3. Two further direct callers of `finrank_closure_eq_locDeg`, `UpperTheory.V.Loc.exists_dec` and `UpperTheory.V.Loc.decEmb`, rewrite with it at `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PadicHodgeTheory/TateFin.lean:95` and `DecEmb.lean:114`. They were located but not traced.

**Corollary 18.3.9.1 (layer by layer).** In the setting of Theorem 18.3.9, let $n\ge1$.
1. For $x\in\mathcal O_F$, $|\varphi(x)|\le|p|^n$ if and only if $x\in w^{en}$.
2. The map $\mathcal O_F\to\mathcal O_K/p^n\mathcal O_K$ is surjective with kernel $w^{en}$.
3. For every $y\in\mathcal O_K$ there are $x_0,x_1,\dots\in\mathcal O_F$ such that $z_n=\sum_{k<n}p^kx_k$ satisfies $|y-\varphi(z_n)|\le|p|^n$. In particular $\varphi(\mathcal O_F)$ is dense in $\mathcal O_K$.
4. Let $\widehat{\mathcal O}_w=\varprojlim_m\mathcal O_F/w^m$. For a compatible family of classes $(\xi_m)$ with representatives $z_m$, the limit $\lim\varphi(z_m)$ exists, and $(\xi_m)\mapsto\lim\varphi(z_m)$ is a ring isomorphism $\widehat{\mathcal O}_w\to\mathcal O_K$.

This corollary is proved here from Lemmas A, C and D and Theorem 18.3.9. It is not a Lean declaration, and the archive does not use it. Its classical form is Lemma 7.25 and Proposition 7.26 of Milne [Paper] [Milne, *Algebraic Number Theory*, pp. 116–117](https://www.jmilne.org/math/CourseNotes/ANT.pdf).

**Proof.** (1) This is the last remark after Lemma D: apply Step 2 of that proof to $u=x/p^n$, using $\operatorname{ord}_w(p^n)=en$.

(2) and (3). For $y\in\mathcal O_K$, $y\in p^n\mathcal O_K$ if and only if $|y|\le|p|^n$, as in Lemma A(3). Let $y\in\mathcal O_K$. By Theorem 18.3.9(1) choose $x_0\in\mathcal O_F$ with $y-\varphi(x_0)\in p\mathcal O_K$, and write $y=\varphi(x_0)+py_1$ with $y_1\in\mathcal O_K$. Apply the same step to $y_1$, then to $y_2$, and so on. After $n$ steps,
$$y=\varphi(x_0+px_1+\dots+p^{n-1}x_{n-1})+p^ny_n=\varphi(z_n)+p^ny_n,\qquad y_n\in\mathcal O_K,$$
so $|y-\varphi(z_n)|\le|p|^n$. This proves (3) and the surjectivity in (2), and $\varphi(z_n)\to y$ because $|p|^n\to0$. The kernel in (2) consists of the $x$ with $|\varphi(x)|\le|p|^n$, which is $w^{en}$ by (1).

(4) Since $w^{en}\subseteq w^m$ whenever $en\ge m$, it suffices to treat the indices $m=en$. Let $\xi_n\in\mathcal O_F/w^{en}$ be compatible classes with representatives $z_n$. Compatibility gives $z_{n+1}-z_n\in w^{en}$, so $|\varphi(z_{n+1})-\varphi(z_n)|\le|p|^n$ by (1). Thus $(\varphi(z_n))$ is a Cauchy sequence in $K$. The field $K$ is complete, being finite-dimensional over $\mathbb Q_p$, and $\mathcal O_K$ is closed in $K$. So the limit $y$ exists and lies in $\mathcal O_K$. Changing $z_n$ by an element of $w^{en}$ moves $\varphi(z_n)$ by at most $|p|^n$, by (1), so $y$ does not depend on the representatives. The map is a ring homomorphism, because limits respect sums and products. It is surjective: for $y\in\mathcal O_K$, the partial sums $z_n$ of (3) satisfy $z_{n+1}-z_n=p^nx_n\in p^n\mathcal O_F\subseteq w^{en}$, so their classes are compatible, and $\lim\varphi(z_n)=y$. It is injective: suppose $\lim\varphi(z_m)=0$ and fix $n$. For all large $m\ge n$ we have $|\varphi(z_m)|\le|p|^n$, so $z_m\in w^{en}$ by (1), and therefore $\xi_n=z_m\bmod w^{en}=0$. $\square$

Surjectivity in part 2 holds at each level separately, but the second example shows that no element of $\mathcal O_F$ need map to a given $y\in\mathcal O_K$. Only the limit in part 4 reaches all of $\mathcal O_K$. For the degree, level $n=1$ suffices: the exponent $[K:\mathbb Q_p]$ is already visible in $\mathcal O_K/p\mathcal O_K$. That is the level the archive uses.

**Remark (what is cited from §§18.3.7–18.3.8).** The following results are cited and not reproved. Theorem 18.3.8 supplies $K_j$ and the isomorphism $i_j\colon D_A\to G_{K_j}$ of topological groups. By part 6 of that theorem, another adapted embedding $j'=\theta\circ j$ gives $K_{j'}=\theta(K_j)$. Both fields have degree $\operatorname{locDeg}(w)$, as Theorem 18.3.9 shows for each adapted embedding separately. Corollary 18.3.8.1(a) transports cohomology along $i_j$, and Corollary 18.3.8.1(c) gives the conjugation formula under a change of embedding. Corollary 18.3.8.1(b) transports restriction squares along isomorphisms $e\colon\Gamma\to\Gamma'$ and $e_D\colon D\to D'$ of topological groups. Here both $e$ and $e_D$ must be continuous with continuous inverses, as in the hypotheses `eG : Γ ≃ₜ* Γ'` and `eD : ∀ i, D i ≃ₜ* D' (eI i)` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TateShafarevichTransport.lean:46`. An abstract group isomorphism $e_D$ need not carry continuous cochains to continuous cochains. The Euler formula of §18.3.7 enters through `top_euler`. Through `decEquiv`, the degree equality proved here is consumed only at `CardH1EqCardH0MulCardH2.lean:74`; the second call of `decEquiv`, at `:82`, discards it. At `:74` it turns $|M|^{[K:\mathbb Q_\ell]}$ into $|M|^{\operatorname{locDeg}(v)}$. In `src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/AdjointCoefficients/ExAbove.lean:125–131` the resulting dimension identities are summed over the places above $\ell$ and compared with $[F:\mathbb Q]$ through `sum_deg` (`:12–14`), which gives $\sum_{v\mid\ell}\operatorname{locDeg}(v)\le[F:\mathbb Q]$.

**Remark (comparison with the literature).** [Paper] Milne proves $n=ef$ for a finite separable extension $L$ of a complete discretely valued field $K$ as a corollary of $\sum_ie_if_i=n$, since only one prime lies above $p$ [Milne, *ANT*, Corollary 7.42, p. 124]. The proof of $\sum_ie_if_i=n$ computes $[B/pB:A/p]$ in two ways. One way uses that $B$ is free over $A$. The other uses the Chinese remainder theorem and the layers $P^r/P^{r+1}$, each one-dimensional over $B/P$ [Theorem 3.34, pp. 59–60]. The archive performs the same two counts, on the two sides of $\varphi$. It uses freeness on the side of $K$ (Lemma B), and layers, through the multiplicativity of the absolute norm, on the side of $F$ (Lemma E). The two sides are connected by the isomorphism $\mathcal O_F/w^e\simeq\mathcal O_K/p\mathcal O_K$. Once $\mathcal O_K$ is identified with the completion of the local ring at $w$ (Corollary 18.3.9.1(4)), this isomorphism is the case $n=e$ of Milne's Lemma 7.25 [p. 116]. The classical route also needs that only one prime of $B$ lies over $p$, which Milne deduces from the uniqueness of the extension of $|\cdot|_p$ [Theorem 7.38, p. 123]. The archive needs neither: its norm is the spectral norm by definition, Lemma A(1) identifies the ball with the integral closure, and the count on the side of $K$ uses only freeness. Milne's Remark 7.43 records $p\mathcal O_K=P^e$ [p. 124]. In the archive this fact appears on the side of $F$, as the kernel $w^e$. [Milne, *Algebraic Number Theory*, v3.08](https://www.jmilne.org/math/CourseNotes/ANT.pdf).

**Remark (formal details).** [Lean, read]
- The hypothesis $\varphi(F)\subseteq K$ of `DenseSurj` is introduced at `ExistsDen.lean:101` and never used. The proof rebuilds the place of $\varphi$ (`:125–162`) instead of receiving it. It is the same ideal as `plIdeal` in `NormLeOneOfInteger.lean:24–38`.
- The bound $|\varphi(x)|\le1$ on $\mathcal O_F$ appears twice. Inside `denseSurj` it is the private lemma `norm_le_one_of_isIntegral_int'`, read here. In `finrank_closure_eq_locDeg` it comes from `placeProp`, which is not claimed at R3 here.
- Mathlib at the pinned commit has two definitions of $e$ and $f$. Here `Ideal.ramificationIdx` is the length-based definition and `Ideal.inertiaDeg` the residue-field one. `kerProp` passes from the first to the exponent in the factorization (`intValuation_natCast`). `normCard` passes from `inertiaDeg` to `inertiaDeg'`, the degree $[\mathcal O_F/w:\mathbb Z/p]$.
- Both cardinalities in `locDegOf_of` are computed as positive powers of $p$, so the convention that `Nat.card` is $0$ on infinite types never intervenes. The last step is injectivity of $n\mapsto p^n$ for $p\ge2$.

**Read boundary.** [Open] The [source ledger](../sources/SOURCES.md#chapter-18-1839-local-degree-count) records the archive, Mathlib and literature editions. R3 [Lean, read] covers the bodies of the following declarations in `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/`.
- `ballCard`, `card_quot_l`, `mem_integralClosure_iff_mem_ball`, `norm_le_one_iff_isIntegral`, `spectralValue_le_one_iff_norm_coeff_le_one`, `isTorsionFree_finExt` and `algebraMap_padicInt_injective` (`MemIntegralClosureIffMemBall.lean:9–141`).
- `denseSurj`, `exists_den` and `norm_le_one_of_isIntegral_int'` (`ExistsDen.lean:7–212`).
- `kerProp`, `normAbv`, `frac_lemma'`, `le_one_lemma_2` and `intValuation_natCast` (`IsEquivAdicAbvNormAbv.lean:7–94,106–150`). The unused `isEquiv_adicAbv_normAbv` (`:96–104`) was also read.
- `normCard`, `span_l_isMaximal` and `liesOver_of_mem` (`SpanLIsMaximal.lean:9–41`), and the statements in `DenseSurj.lean:8–50`.

The following keep their §18.3.8 reading and were re-read here only to trace the arguments: `locDegOf_of` and `mem_span_l_iff`; `finrank_closure_eq_locDeg`, `norm_lt_one_iff` and `decEquiv`; `finiteDimensional_adjoin_range`, `adjoin_range_subset_closure` and `norm_l_lt_one`; `localEulerChar_holds`. The declaration `placeProp` (`NormLeOneOfInteger.lean:73–75`) is a named input, and its proof is not claimed at R3. It is not on the production chain of the four counting theorems: none of them refers to it or to the other declarations of its file. `finrank_closure_eq_locDeg` uses it only for the bound in (P). Part 4 of Theorem 18.3.8 therefore remains conditional on `placeProp`, and its Lean dependency cone is not claimed at R3. The Mathlib results used are checked by statement only at the pinned commit. They are the integral-closure theorems, the reduction $\mathbb Z_p\to\mathbb F_p$, minimal polynomials over integrally closed domains, the spectral norm, localizations of Dedekind domains at primes, adic valuations and factorization counts, the absolute norm and residue degrees, and the closure criterion. Corollary 18.3.9.1 is proved here and is not a Lean declaration. The examples use the [Paper] facts cited in them. Every item that §§18.3.7–18.3.8 list as a named input keeps its reading level.

---

## 18.4 Cluster III — Automorphic purity, unitary base change, Siegel–Weil, and $p$-adic Hodge theory

### 18.4.1 Motivation: domain restrictions and period-ring bundles in high-end foundations

Cluster III inspects six heavy foundational `Prop`s from `P18`: Clozel's purity lemma (`ClozelPurity`
and `RegularAlgebraicPurity`), definite unitary base change (`BaseChangeDefiniteUnitary` and
`BaseChangeIsobaric`), the classical and convergent unitary Siegel–Weil formulas (`WeilSiegelFormula`,
`WeilSiegelFormulaUnitary`, and `SiegelWeilUnitaryConvergent`), and Fontaine–Berger's $p$-adic
monodromy theorem (`DeRhamPotSemistable`). Here we encounter **Mode 2 (domain restrictions)** and
**Mode 4 (custom period-ring bundles)** in full force — and check directly at the consumer call sites
that every domain restriction holds on Alpöge's CM host fields!

### 18.4.2 Worked examples: everywhere-unramified CM extensions $E/E^+$ and Siegel–Weil rank ranges

1. **Testing `∀ w, Algebra.IsUnramifiedAt (𝓞 E⁺) w.asIdeal` in `BaseChangeDefiniteUnitary`:**
   Open `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:236` [Lean, read]: the proposition assumes that the quadratic
   CM extension $E / E^+$ is **unramified at every finite prime ideal $w$ of $\mathcal O_{E^+}$**!
   - *Failure on $E = \mathbb Q(i)$ over $E^+ = \mathbb Q$:* At $w = (2) \subset \mathbb Z$,
     $2\mathbb Z[i] = (1 + i)^2$ ramifies ($e_2 = 2$), so `BaseChangeDefiniteUnitary` does **not**
     apply to $U(n)$ attached to $\mathbb Q(i)/\mathbb Q$!
   - *Success on biquadratic and host CM fields:* Take $E^+ = \mathbb Q(\sqrt{21})$ (since
     $21 \equiv 1 \pmod 4$, $d_{E^+} = 21$) and $E = \mathbb Q(\sqrt{-3}, \sqrt{-7}) = E^+(\sqrt{-3})$
     [Expository]. Because $-3 \equiv 1 \pmod 4$ and $-7 \equiv 1 \pmod 4$, $\mathbb Q(\sqrt{-3})/\mathbb Q$
     ramifies **only at $3$** ($e_3 = 2$) and $\mathbb Q(\sqrt{-7})/\mathbb Q$ ramifies **only at $7$**
     ($e_7 = 2$). In the compositum $E/\mathbb Q$, the ramification index at $3$ is $\operatorname{lcm}(2, 1) = 2 = e_3(E^+/\mathbb Q)$,
     the ramification index at $7$ is $\operatorname{lcm}(1, 2) = 2 = e_7(E^+/\mathbb Q)$, and no
     other finite prime ramifies at all! By multiplicativity $e_{\mathfrak P}(E/\mathbb Q) = e_{\mathfrak P}(E/E^+) e_w(E^+/\mathbb Q)$,
     we get **$e_{\mathfrak P}(E/E^+) = 1$ at EVERY finite prime $w$ of $\mathcal O_{E^+}$**! Exactly
     the same mechanism operates on Alpöge's host fields $E \subset \mathbb Q(\zeta_N)$: with
     $q \equiv 3 \pmod 8$ ($-q \equiv 5 \pmod 8$, $d_{\mathbb Q(\sqrt{-q})} = -q$) and $d \equiv 7 \pmod{16}$
     ($-d \equiv 1 \pmod 8$, $d_{\mathbb Q(\sqrt{-d})} = -d$), the subfield $\mathbb Q(\sqrt{-q}, \sqrt{-d})$
     is already everywhere unramified at finite places over $\mathbb Q(\sqrt{q d})$!
2. **Comparing Weil's classical range ($m > 2n$) and Kudla–Rallis's convergent range ($n < m \le 2n$) on definite unitary groups:**
   For a dual pair $(U(A), U(B))$ where $n = \operatorname{rank} A$, $m = \operatorname{rank} B$, and
   $r_B = \operatorname{wittIdx}(B)$ ($r_B = 0$ when $B$ is definite!), Weil's 1965 absolute-convergence
   criterion `[Weil1965]` for the theta-integral average is $m - r_B > n + 1$ for theta integrability
   and **$m > 2n$** (`2 * A.rank < B.rank`, `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean:68`) for absolute convergence
   of the Siegel Eisenstein series at $s_0 = \frac{m - n}{2} > \frac{n}{2}$. When $n < m \le 2n$ — for
   instance $U(2) \times U(3)$ ($n = 2, m = 3$: $2 < 3 \le 4$), or along Alpöge's step-$j$ unitary
   theta lifts where $\operatorname{rank} Y_j$ and $\operatorname{rank} X_{j+1}$ satisfy $n < m \le 2n$ —
   the Eisenstein series no longer converges absolutely at $s_0$, yet when $B$ is anisotropic ($r_B = 0$,
   so $n + r_B = n < m$!), the theta integral **still converges in $L^1$** and matches the
   holomorphically continued Eisenstein value at $s_0$ by Kudla–Rallis's first-term identity
   `[KudlaRallis1994]` (`src/Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18–32`)!

### 18.4.3 Exact Lean definitions and verbatim literature comparison (Cluster III)

**Definition 18.3 (Cluster III `Published` propositions).** [Lean, read]

1. **`GlobalTheory.Published.ClozelPurity` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/ClozelPurity.lean:10–14`, cone `878`) & `RegularAlgebraicPurity` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/RegularAlgebraicPurity.lean:14–18`, cone `1,538`):**
   `ClozelPurity` states that for every `[IsTotallyComplex E]`, $n \ge 1$, and cuspidal automorphic
   representation $\pi$ of $\mathrm{GL}_n(\mathbb A_E)$, `π.IsRegularAlgebraic → ∃ w : ℤ, IsPureOfWeight π w`
   (every archimedean Langlands parameter of $\pi_v$ is pure of weight $w$). `RegularAlgebraicPurity`
   specializes $E$ to `[IsCMField E]` and adds `GKCoh.IsCohomological π`.
2. **`GlobalTheory.Published.BaseChangeDefiniteUnitary` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:235–241`, cone `783`) & `BaseChangeIsobaric` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeIsobaric.lean:40–48`, cone `784`):**
   For every CM field $E$, $n \ge 1$, everywhere-unramified CM extension `hunr : ∀ w : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal`,
   and discrete automorphic representation $\sigma$ of the standard definite unitary group `UA E n := UJ (conjAd E) 1`,
   `BaseChangeDefiniteUnitary` produces an `IsobaricDecomp E n` (`Π` on $\mathrm{GL}_n(\mathbb A_E)$)
   satisfying `IsWeakBaseChange E n σ Π` (conjugate self-duality $\Pi^\vee \cong \Pi^c$ of each summand
   plus unramified Satake parameter agreement off a finite place set $S$), while `BaseChangeIsobaric`
   upgrades unramified local compatibility to **every** prime $p \notin S$ (`SatakeCompatAtPrime`).
3. **`GlobalTheory.Published.WeilSiegelFormula` (`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/WeilSiegelFormula.lean:18–28`, cone `1,599`), `WeilSiegelFormulaUnitary` (`src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean:56–69`, cone `827`), & `SiegelWeilUnitaryConvergent` (`src/Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18–32`, cone `1,803`):**
   Over host datum `D : D7`, `WeilSiegelFormula` (`2 * n < m` and `n + wittIndex(B) < m` on `HermSpace`)
   and `WeilSiegelFormulaUnitary` (`2 * A.rank < B.rank`) equate $\int_{[U(B)]} \Theta_\Phi(g, h)\,dh = \kappa \cdot E(g, s_0, \operatorname{Four}(\Phi))$,
   while `SiegelWeilUnitaryConvergent` extends that exact identity (with holomorphic continuation of
   $E(g, s, \Phi)$ at $s_0 = \frac{B.\mathrm{rank} - A.\mathrm{rank}}{2}$) to the intermediate range
   `0 < A.rank`, **`A.rank < B.rank`**, **`B.rank ≤ 2 * A.rank`**, and **`A.rank + wittIdx B < B.rank`**.
4. **`GlobalTheory.Published.DeRhamPotSemistable` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/DeRhamPotSemistable.lean:13–17`, cone `135`):**
   For every prime $\ell$, finite extension $K / \mathbb Q_\ell$, finite-dimensional $\mathbb Q_\ell$-representation
   $V$, continuous $\rho : G_K \to_* \mathrm{GL}_{\mathbb Q_\ell}(V)$, and tied Fontaine period-ring
   bundle `Nonempty (LocTied l P AI)`, `IsDeRham ρ → IsPotentiallySemistable ρ`.

| Lean `Prop` | Classical source | Word-for-word comparison (hypotheses & conclusion) | Verdict |
|---|---|---|---|
| `ClozelPurity` & `RegularAlgebraicPurity` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/ClozelPurity.lean:10`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/RegularAlgebraicPurity.lean:14`) | Clozel `[Clozel1990, Lemme 4.9]` | Clozel proves purity of $\pi_\infty$ for regular algebraic cuspidal $\pi$ on $\mathrm{GL}_n(\mathbb A_F)$ over **any** number field $F$; the archive restricts to `[IsTotallyComplex E]` / `[IsCMField E]` (where archimedean places are complex, simplifying $\mathrm{GL}_n(\mathbb C)$ Adams–Johnson parameters). | **Special case** (totally complex / CM fields; `[Lean, read]` for `Prop`, upstream cones `878`–`1,538` `[Open]`) |
| `BaseChangeDefiniteUnitary` & `BaseChangeIsobaric` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:235`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeIsobaric.lean:40`) | Rogawski (1990, $n \le 3$); Labesse (2011, general $n$) | Restricts to the standard identity definite form `UA E n` and **everywhere-unramified** $E/E^+$ (`hunr`), which avoids ramified fundamental-lemma / Kottwitz-sign obstructions at finite places of $E^+$! | **Domain-restricted special case** (consumer alignment verified at `src/Development/AutomorphicArithmetic/Foundations/BaseChangeIdentities/Narrow.lean:47` `[Lean, read]`; `15,289`-module proof cone `[Open]`) |
| `WeilSiegelFormula`, `WeilSiegelFormulaUnitary`, & `SiegelWeilUnitaryConvergent` (`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/WeilSiegelFormula.lean:18`, `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean:56`, `src/Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18`) | Weil `[Weil1965]`; Kudla–Rallis `[KudlaRallis1994]`; Ichino (2004) | Splits Weil's $m > 2n$ range from Kudla–Rallis's convergent $n < m \le 2n$ ($n + r_B < m$) range on unitary groups over `D : D7`, matching the exact convergence hypotheses of both papers. | **Special case** (unitary dual pairs over `D7` in convergent ranges; `[Lean, read]` for `Prop`s, upstream cones `[Open]`) |
| `DeRhamPotSemistable` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/DeRhamPotSemistable.lean:13`) | Berger `[Berger2002, Thm. 0.7]`; André (2002), Kedlaya (2004), Mebkhout (2002) | Faithful statement of Fontaine's $p$-adic monodromy conjecture ($\mathrm{de\ Rham} \implies \text{potentially semistable}$) for $\mathrm{GL}_{\mathbb Q_\ell}(V)$, parameterized by `Nonempty (LocTied l P AI)` (verified non-empty via `exists_locPrime_tied` `[Lean]`). | **Faithful** (`[Lean, read]` for `Prop` & $L$-linear scalar-extension proof `:89–132`; upstream proof `[Open]`) |

### 18.4.4 Fidelity lemma and line-by-line `R3` proofs (Cluster III)

**Lemma 18.3 (Consumer domain alignment for unitary base change and $L$-linear scalar extension for `DeRhamPotSemistable`).** [Lean, read]

1. *(Consumer check on `BaseChangeDefiniteUnitary`: `definiteN_of`, `src/Development/AutomorphicArithmetic/Foundations/BaseChangeIdentities/Narrow.lean:47–74`, contrasted with `UnusedSlot72`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`)*
   *At its downstream consumer `definiteN_of`, the everywhere-unramified hypothesis `hunr : ∀ w, Algebra.IsUnramifiedAt (𝓞 E⁺) w.asIdeal` is carried explicitly as part of the narrow host datum and passed directly to `BaseChangeDefiniteUnitary` and `BaseChangeIsobaric`; by contrast, `UnusedSlot72 : Prop := True` is never inspected downstream.*
2. *(Non-vacuity and $L/\mathbb Q_\ell$-linear extension of `DeRhamPotSemistable`: `DeRhamPotSemistable.coeff` and `isPstAt`, `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/DeRhamPotSemistable.lean:89–132`, plus `exists_locPrime_tied`, `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281`)*
   *The period-ring witness `Nonempty (LocTied l P AI)` is unconditionally inhabited for every local place $v \mid \ell$ (`exists_locPrime_tied`), and `DeRhamPotSemistable` over $\mathbb Q_\ell$ implies potential semistability `isPstAt` for arbitrary finite-dimensional $L$-linear Galois representations $\rho : G_E \to_* \mathrm{GL}_L(V)$ (`[FiniteDimensional ℚ_[l] L]`).*

*Proof.*
(1) In `src/Development/AutomorphicArithmetic/Foundations/BaseChangeIdentities/Narrow.lean:47–74`, `definiteN_of` takes hypotheses `hbcd : Published.BaseChangeDefiniteUnitary`
and `hbci : Published.BaseChangeIsobaric` and proves the narrow base-change package `DefiniteN`:
lines `52–54` introduce `hunr : ∀ w : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Algebra.IsUnramifiedAt ...`
from `DefiniteN`'s own signature and feed `hbcd E n hn hunr σ` (`:58`) and `hbci E n hn hunr σ` (`:59`)
directly! Thus the unramified-CM restriction in `BaseChangeDefiniteUnitary` is **not** a hidden gap;
it is an explicit architectural invariant propagated from the host CM tower!

(2) First, `exists_locPrime_tied` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281` `[Lean]`) constructs a concrete
`(P, AI)` with `Nonempty (LocTied l P AI)` for every prime $\ell$, number field $E$, and prime ideal
$v$ above $\ell$, certifying that `DeRhamPotSemistable` is never vacuously satisfied by an empty
`LocTied` type! Second, in `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/DeRhamPotSemistable.lean:89–132` [Lean, read], suppose $L/\mathbb Q_\ell$
is a finite extension (`FiniteDimensional ℚ_[l] L`) and $\rho : G_K \to_* \mathrm{GL}_L(V)$ is de Rham
with $L$-coefficients (`IsDeRhamL`). Restricting scalars from $L$ to $\mathbb Q_\ell$ (`restrictScalars ℚ_[l]`,
`:90–94`) turns $V$ into a finite-dimensional $\mathbb Q_\ell$-vector space (`Module.Finite.trans L V`)
whose underlying $\mathbb Q_\ell$-representation is de Rham (`isDeRham_restrictScalars`), so
`DeRhamPotSemistable` yields potential semistability over $\mathbb Q_\ell$ (`coeff`, `:89`). In
`of_coords` (`:97–111`) and `isPstAt` (`:120–132`), choosing an $L$-basis `b := Module.Basis.ofVectorSpace L V`
identifies entries of $\rho(g)$ in $L^d$ with $\mathbb Q_\ell$-linear coordinates of `restrictScalars ℚ_[l] ρ`,
transferring Fontaine's $(\varphi, N, G_{K'})$-admissibility directly back to $\mathrm{GL}_L(V)$! $\square$

---

## 18.5 Reusable community audit protocol and Masullo's counterpart

### 18.5.1 Five-step checklist for auditing the remaining `[Open]` declarations in `P18`

For number theorists and formalization contributors working through the remaining ~70 unreviewed
propositions in `OpenLiteratureStatements` (see `leanprover-community/riemann-hypothesis` issue `#39`
and `LUMI doc 07` [Community]), our three clusters distill into a fast, foolproof **five-step protocol**
[Expository]:

1. **Unfold the `Prop`, never stop at the wrapper:** Trace through `EveryCharacterOfLiteratureOfVWin.lean`
   and `StandardTheoremStatements/*` until you reach the `def ... : Prop :=` in `PublishedTheorems/`.
2. **Audit logical polarity of every quantifier and side condition:** Use the table of Section 18.1.2:
   does an unfamiliar hypothesis weaken the `Prop` (`hunr` in `BaseChangeDefiniteUnitary`, `2 * r ≠ k`
   in `Kato`) or actually *strengthen* it (`IsAlgPos` in `HeckeLAdicCharacter`)?
3. **Check both a producer and a consumer (`non-vacuity + alignment`):** Verify that every custom
   type (`LocTied`, `RayPair`, `D7`) is inhabited upstream (`exists_locPrime_tied`) and that every
   domain restriction (`IsTotallyComplex`, `IsUnramifiedAt`) is supplied honestly by the downstream
   consumer (`src/Development/AutomorphicArithmetic/Foundations/BaseChangeIdentities/Narrow.lean:47`).
4. **Test small boundary examples where textbook naive statements fail:** Plug in $\mathbb Q(i)/(2+2i)$,
   $\zeta_{\{2\}}(-1) = \frac{1}{12}$ (`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean:223`), $(F = \mathbb Q, \ell = 2)$
   for Poitou–Tate, or $(F = \mathbb Q, E = \mathbb Q(i))$ for ramified CM base change!
5. **Keep statement fidelity separate from proof-cone reading:** A **Faithful** verdict upgrades the
   *statement* match from `[Open]` to `[Lean, read]`; unless you have also read the upstream proof
   cone (`*_of_literature`) to `R3` (as illustrated by the local bridges in Chapter 19), keep the
   upstream *proof body* honestly marked `[Open]`.

### 18.5.2 Masullo's counterpart

How does Masullo's 940-page manuscript handle background literature compared with Alpöge's `P18` layer [Expository]?

- **Appendices A–E (`pp. 537–932`) vs `GlobalTheory.Published.*` (`P18`):** Masullo devotes nearly
  400 pages of appendices (`Appendix A` Algebraic Number Theory, `pp. 537–586`; `Appendix B` Analytic
  Number Theory, `pp. 587–654`; `Appendix C` Locally Convex TVS, `pp. 655–742`; `Appendix D`
  Schwartz–Bruhat Functions, `pp. 743–822`; `Appendix E` Topological Stacks, `pp. 823–932`) to
  stating and proving or citing background results from classical monographs (`[Neukirch1999]`,
  `[Tate1967]`, `[Grothendieck1955]`) [Paper; Masullo pp. 537–932]. Because Masullo works purely on
  $\mathrm{GL}_1(\mathbb A_F)/F^\times$, none of Cluster II or Cluster III (Iwasawa $\mu = 0$, Kato's
  Euler system, Poitou–Tate duality, unitary base change, Siegel–Weil, $p$-adic Hodge theory) appears
  in his manuscript; only Cluster I's $\mathrm{GL}_1$ class field / Hecke $L$-function language has a
  counterpart in his Chapter 3 and Appendix A.
- **How `mccorvie/riemann-masullo` audits statement fidelity in reverse:** Whereas Alpöge's archive
  shipped `sorry`-free proofs whose internal `Published` `Prop`s we audit against literature names,
  the community formalization `mccorvie/riemann-masullo` (`README.md` and `ERRATA.md` [Community])
  works in the opposite direction: digesters translate Masullo's printed statements into Lean 4
  (`v4.36.0`) with page citations, reviewers audit statement fidelity against the PDF, and wherever a
  printed lemma is false as stated (~45 entries in `ERRATA.md`), the project keeps the printed claim
  alongside a Lean disproof and formalizes a repaired statement!

---

## 18.6 Master verdict table and Lean counterpart for this chapter

| # | Declaration (`file:line`) | Cone | Classical benchmark | Statement-fidelity verdict | Upstream proof status | Tag |
|---:|---|---:|---|---|---|---|
| 1 | `GlobalTheory.Published.GlobalArtinReciprocity` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70`) | 9 | Artin `[Artin1927]`, Tate `[Tate1967]`, Neukirch `[Neukirch1999, Thm. VI.6.1]` | **Faithful** (full idèlic Artin map over all number fields; geometric Frobenius on uniformizers) | Wrapper `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8` (cone 1,015) `[Open]` | [Lean, read] |
| 2 | `GlobalTheory.Published.HeckeLAdicCharacter` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:74`; finite-order bridge `:381, 466`) | 9 | Weil (1956), Serre (1968) | **Faithful (slightly stronger)** (`IsAlgPos` requires algebraicity only on $E_+^\times$; the Artin map is existentially quantified; finite-order correspondence: $r\mapsto\chi$ from `IsGlobalArtin` alone, $\chi\mapsto r$ from the `Prop` itself) | Wrapper `:14` (cone 1,015) `[Open]`; finite-order bridge `:381–491` `R3` | [Lean] (`Prop`); [Lean, read] (bridge) |
| 3 | `GlobalTheory.Published.RayClassFieldSt` & `RayClassFieldMaximalSt` (`src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:17,32`) | 686 | Takagi (1920), Neukirch `[Neukirch1999, Thm. VI.6.2]` | **Faithful** (narrow real-place sign condition built into `RayClassGroup 𝔪`) | `RayClassFieldMaximalSt` proved in file with no hypotheses (`rayClassFieldMaximalSt_holds`, `:204–225`, `R3`); `rayClassFieldSt` wrapper `[Open]` | [Lean, read] |
| 4 | `GlobalTheory.Published.ChebotarevDegreeOne` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:12`) | 211 | Chebotarev `[Tschebotareff1926]` | **Safe weakening** (existential infinitude of degree-1 Frobenius primes outside $S$, omitting natural density; implies `dense` `:51`) | Proved in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean:17–64` (cone 289, `R3`; cyclic base `[Open]`) | [Lean, read] |
| 5 | `UpperTheory.V.Published.FerreroWashington` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:7`) | 0 | [FerreroWashington1979] | Uniform bound on the mod-$\ell$ class-group quotient, for $K$ containing $\mu_\ell$ ($\mu_4$ if $\ell=2$); the archive proof discards this premise | Archive theorem at `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104` | [Lean] |
| 6 | `SiegelKlingenDeligneRibet` (`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean:52`) | 283 | [DeligneRibet1980] | Smoothed integrality for modulus $(\ell^n)$, $n\ge1$, with $\ell$-integral values on coprime ideals | Example read in §18.3.2, analytic proof [Open] | [Lean] |
| 7 | `UpperTheory.V.Published.Kato` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/QuotRepMk.lean:65`) | 1,669 | [Kato2004, Thm. 14.2] | All primes, off-center critical twists and stable lattices | Full comparison of local conditions [Open] | [Lean] |
| 8 | `GlobalTheory.Published.PoitouTateNormalised` & `PoitouTateDuality` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNormalised.lean:12`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsPrimitiveRootPow.lean:13`) | 11 | Poitou–Tate `[NeukirchSchmidtWingberg2008, Thm. 8.6.10]`, `[Wiles1995, Prop. 1.6]` | **Special case (`l ≠ 2 ∨ IsTotallyComplex F`)** (avoids real Tate terms at $\ell = 2$; covers all $\ell$ on CM hosts; `Normalized9` pins restriction maps) | `cohDimTwoGlobal` (`:70`) & `greenbergWiles_of_poitouTate` (`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesOfPoitouTate.lean:45`, cone 718) `R3`; upstream proof `[Open]` | [Lean, read] |
| 9 | `GlobalTheory.Published.ClozelPurity` & `RegularAlgebraicPurity` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/ClozelPurity.lean:10`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/RegularAlgebraicPurity.lean:14`) | 878 / 1,538 | Clozel `[Clozel1990, Lemme 4.9]` | **Special case** (restricted from all number fields to `[IsTotallyComplex E]` / `[IsCMField E]`) | Upstream Shimura/archimedean proof cones `[Open]` | [Lean, read] |
| 10 | `GlobalTheory.Published.BaseChangeDefiniteUnitary` & `BaseChangeIsobaric` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:235`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeIsobaric.lean:40`) | 783 / 784 | Rogawski (1990), Labesse (2011) | **Domain-restricted special case** (identity definite form `UA E n` + everywhere-unramified CM extension `hunr`, aligned with `src/Development/AutomorphicArithmetic/Foundations/BaseChangeIdentities/Narrow.lean:47`!) | Consumer `definiteN_of` `R3`; `15,289`-module trace-formula proof cone `[Open]` | [Lean, read] |
| 11 | `GlobalTheory.Published.WeilSiegelFormula`, `WeilSiegelFormulaUnitary`, & `SiegelWeilUnitaryConvergent` (`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/WeilSiegelFormula.lean:18`, `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean:56`, `src/Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18`) | 1,599 / 827 / 1,803 | Weil `[Weil1965]`, Kudla–Rallis `[KudlaRallis1994]` | **Special case** (unitary dual pairs over `D : D7` in Weil's $m > 2n$ and Kudla–Rallis's $n < m \le 2n$, $n + r_B < m$ convergent ranges) | Upstream Siegel–Weil proof cones `[Open]` | [Lean, read] |
| 12 | `GlobalTheory.Published.DeRhamPotSemistable` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/DeRhamPotSemistable.lean:13`; `UnusedSlot72` contrast at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`) | 135 | Berger `[Berger2002, Thm. 0.7]` | **Faithful** (`LocTied` verified inhabited via `exists_locPrime_tied` `[Lean]`; contrasted with fossil `UnusedSlot72 : Prop := True`) | Scalar-extension `coeff`/`isPstAt` (`:89–132`) `R3`; upstream $p$-adic differential-equation proof `[Open]` | [Lean, read] |

**Reading status.** Sections 18.2–18.4 distinguish the statements, their local deductions,
and the upstream proofs. The three corrected Cluster II interfaces carry [Lean]. The
Deligne–Ribet boundary example carries its own [Lean, read] tag.
