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
