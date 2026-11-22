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
3. **Uniformizer Frobenius sign convention (`IsGlobalArtin.frob`):** In `ExistsUniqueHcharOfFiniteOrder.lean:34–36`,
   for an unramified place $v$ and local uniformizer $\varpi_v \in E_v^\times$, the Artin map
   $\mathrm{art}_E : \mathbb A_E^\times \to G_E^{\mathrm{ab}}$ sends the single-place idèle
   $\iota_v(\varpi_v)$ to `toAb E Ω σ⁻¹`, where `σ ∈ DecompGrp E Ω v` induces $x \mapsto x^{N(v)}$ on
   the residue field (`IsArithFrobAt`). Thus **uniformizers map to geometric Frobenius $\mathrm{Frob}_v^{\mathrm{geom}} = (\mathrm{Frob}_v^{\mathrm{arith}})^{-1}$**
   — matching Deligne's convention `[Tate1967]` and the algebraic Hecke character package `HeckeLAdicCharacter`!

### 18.2.3 Exact Lean definitions and verbatim literature comparison (Cluster I)

**Definition 18.1 (Cluster I `Published` propositions).** [Lean, read]

1. **`GlobalTheory.Published.GlobalArtinReciprocity` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70–72`, cone `9`):**
   $$\forall (E : \mathrm{Type})\,[\mathrm{Field}\,E]\,[\mathrm{NumberField}\,E]\,(\Omega : \mathrm{Type})\,[\mathrm{Field}\,\Omega]\,[\mathrm{IsAlgClosed}\,\Omega]\,[\mathrm{Algebra}\,E\,\Omega],\;
   \exists\,\mathrm{art} : \mathrm{Idele}\,E \to_* \mathrm{GalAb}\,E\,\Omega,\; \mathrm{IsGlobalArtin}\,E\,\Omega\,\mathrm{art},$$
   where `IsGlobalArtin E Ω art` (`:25–40`) bundles five fields:
   - `quot : IsOpenQuotientMap art` (continuous open surjection $\mathbb A_E^\times \twoheadrightarrow G_E^{\mathrm{ab}}$, where $G_E^{\mathrm{ab}} = G_E / \overline{[G_E, G_E]}$ carries the quotient Krull topology);
   - `ker : art.ker = ((diagUnits E).range ⊔ infConn E).topologicalClosure` (kernel equals the closure of $E^\times \cdot (E_\infty^\times)^\circ$ inside $\mathbb A_E^\times$);
   - `ine` (at every finite place $v$, the image of $\mathcal O_v^\times$ has topological closure equal to the image of the inertia subgroup $I_v \le G_E$ in $G_E^{\mathrm{ab}}$);
   - `frob` (for every $v$ and uniformizer $\varpi_v$ with $v(\varpi_v) = \mathrm{ Multiplicative.ofAdd}(-1)$, there is an arithmetic Frobenius $\sigma \in D_v$ with $\mathrm{art}(\iota_v(\varpi_v)) = \mathrm{toAb}(\sigma^{-1})$);
   - `dec` (the image of $E_v^\times$ lies inside the topological closure of the image of $D_v$).
2. **`GlobalTheory.Published.HeckeLAdicCharacter` (`…/ExistsUniqueHcharOfFiniteOrder.lean:74–78`, cone `9`):**
   For every number field $E$, algebraic closure $\Omega$, prime $\ell$, algebraic Hecke character
   $\chi : \mathrm{HChar}\,E$ satisfying `χ.IsAlgPos n` (`:65–67`, meaning on principal idèles of
   **totally positive** elements $k \in E^\times$, $\chi(\mathrm{diag}(k)) = \iota_{\overline{\mathbb Q}}(\prod_\tau \tau(k)^{n(\tau)})$),
   and isomorphism $\iota : \overline{\mathbb Q}_\ell \simeq_{\mathbb Q} \mathbb C$, there exists a
   continuous character $r : (E \simeq_a \Omega) \to_* (\overline{\mathbb Q}_\ell)^\times$ unramified
   away from $\mathrm{supp}(\mathrm{cond}(\chi)) \cup \{v \mid \ell\}$ such that at every unramified
   place $v \nmid \ell$ and every arithmetic Frobenius $\sigma \in D_v$, $\iota(r(\sigma^{-1})) = \chi(\iota_v(\varpi_v))$.
3. **`GlobalTheory.Published.RayClassFieldSt` & `RayClassFieldMaximalSt` (`src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:17,32`, cone `686`):**
   `RayClassFieldSt` asserts `∀ (K) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) [NeZero 𝔪], ∃ (L) [Field L] [NumberField L] [Algebra K L], Nonempty (IsRayClassField K L 𝔪)`.
   By `rayClassFieldSt_iff_artinIso` (`:19–25`), `IsRayClassField K L 𝔪` means $L/K$ is finite Galois,
   unramified outside $\mathfrak m$ (`IsUnramifiedOutside K L 𝔪`), and the global Artin map on
   `RayClassGroup 𝔪` (narrow/totally-positive modulo $\mathfrak m$, built from `RayPair 𝔪`, `:149`)
   is an isomorphism `RayClassGroup 𝔪 ≃* (L ≃ₐ[K] L)`. `RayClassFieldMaximalSt` (`:32–38`) adds
   universal maximality: every finite abelian $K' / K$ unramified outside $\mathfrak m$ with trivial
   Artin kernel on principal ray elements embeds into $L$ over $K$ (`Nonempty (K' →ₐ[K] L)`).
4. **`GlobalTheory.Published.ChebotarevDegreeOne` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:12–18`, cone `211`):**
   For every number field $F$, finite Galois extension $L/F$, element $\sigma \in \operatorname{Gal}(L/F)$,
   and finite set $S$ of maximal ideals of $\mathcal O_F$, there exists a maximal ideal $v \notin S$
   unramified in $L$ of **absolute inertia degree $1$** ($\mathrm{absNorm}(v) = p$ prime, i.e.
   $\mathcal O_F / v \cong \mathbb F_p$) whose Frobenius conjugacy class in $\operatorname{Gal}(L/F)$
   contains $\sigma$.

| Lean `Prop` | Classical source | Word-for-word comparison (hypotheses & conclusion) | Verdict |
|---|---|---|---|
| `GlobalArtinReciprocity` (`ExistsUniqueHcharOfFiniteOrder.lean:70`) | Artin `[Artin1927]`; Tate `[Tate1967]`; Neukirch `[Neukirch1999, Thm. VI.6.1]` | Matches idèlic Artin reciprocity over **every** number field $E$: open quotient $\mathbb A_E^\times \twoheadrightarrow G_E^{\mathrm{ab}}$, exact kernel $\overline{E^\times (E_\infty^\times)^\circ}$, inertia = $\overline{\mathrm{art}(\mathcal O_v^\times)}$, uniformizer $\mapsto \mathrm{Frob}_v^{\mathrm{geom}}$. (Tate's fuller isomorphism $\pi_0(C_E) \xrightarrow{\sim} G_E^{\mathrm{ab}}$ is equivalent because $C_E^\circ = \overline{E^\times (E_\infty^\times)^\circ} / E^\times$.) | **Faithful** (`[Lean, read]` for `Prop`; `1,015`-module proof cone `[Open]`) |
| `HeckeLAdicCharacter` (`ExistsUniqueHcharOfFiniteOrder.lean:74`) | Weil (1956) $A_0$-type algebraic Hecke characters; Serre (1968) | Hypothesis `χ.IsAlgPos n` requires algebraic infinity-type only on **totally positive** $k \in E_+^\times$ (`IsTotallyPositive k`), which is *weaker* in hypothesis (hence **slightly stronger** as a theorem!) than requiring all $k \in E^\times$ (`isAlgPos_of_isAlg`, `:86`). Matches unramified geometric Frobenius values outside $\mathrm{cond}(\chi) \cup \{v \mid \ell\}$. | **Faithful** (`[Lean, read]` for `Prop` & finite-order bridge) |
| `RayClassFieldSt` & `RayClassFieldMaximalSt` (`NonemptyAlgHomOfIsRayOfDvd.lean:17,32`) | Takagi (1920); Neukirch `[Neukirch1999, Thm. VI.6.2]` | Uses narrow ray class group `RayClassGroup 𝔪` (totally positive principal generators at all real places, `:149`). `RayClassFieldMaximalSt` is **proved inside the same file** (`:204–225`) from `RayClassFieldSt` + `ChebotarevDegreeOne`! | **Faithful** (narrow real-place convention; `[Lean, read]`) |
| `ChebotarevDegreeOne` (`ChebotarevDegreeOneIffCheb.lean:12`) | Chebotarev `[Tschebotareff1926]`; Neukirch `[Neukirch1999, Thm. VII.13.4]` | Asserts **existential infinitude** (avoiding any finite $S$) of unramified degree-one primes hitting the conjugacy class of $\sigma$, omitting natural/Dirichlet density $\lvert C \rvert / \lvert G \rvert$ (density 1 of degree-one primes makes the existential form true; proved in `Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean:17–64`!). | **Safe weakening** (existential, no density value; suffices for `dense` & `eq_of_frob` `[Lean, read]`) |

### 18.2.4 Fidelity lemma and line-by-line `R3` proofs (Cluster I)

**Lemma 18.1 (Cluster I internal deductions verifying non-vacuity and strength).** [Lean, read]

1. *(Exact finite-order Galois–Hecke bijection from `GlobalArtinReciprocity` alone: `exists_unique_hchar_of_finite_order`, `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:381–418`, and `HeckeLAdicCharacter.full`, `:466–491`)*
   *`GlobalArtinReciprocity` alone (without `HeckeLAdicCharacter`!) implies that for every number field $E$, prime $\ell$, $\iota : \overline{\mathbb Q}_\ell \simeq_{\mathbb Q} \mathbb C$, and $m \ge 1$, the Frobenius compatibility relation sets up a **bijection** (`∃! χ : HChar E`) between continuous Galois characters $r : G_E \to_* (\overline{\mathbb Q}_\ell)^\times$ satisfying $r^m = 1$ and finite-order Hecke characters $\chi$ (`χ.OrderDvd m`).*
2. *(Topological Frobenius density and ray class field maximality from `ChebotarevDegreeOne`: `ChebotarevDegreeOne.dense` and `eq_of_frob`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:51–68`, and `rayClassFieldMaximalSt_holds`, `…/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:204–225`)*
   *Existential `ChebotarevDegreeOne` implies that unramified Frobenius elements are topologically dense in $G_F = \operatorname{Gal}(\Omega/F)$, that two continuous representations $G_F \to_* M$ into any $T_2$ group agreeing on Frobenius outside $S$ are identical, and that `RayClassFieldSt` + `ChebotarevDegreeOne` imply `RayClassFieldMaximalSt`.*

*Proof.*
(1) Let `art : Idele E →* GalAb E Ω` satisfy `IsGlobalArtin E Ω art` (`:387`). Since $(\overline{\mathbb Q}_\ell)^\times$
is commutative, any continuous $r : G_E \to_* (\overline{\mathbb Q}_\ell)^\times$ with $r^m = 1$
factors through $G_E^{\mathrm{ab}}$ via a continuous homomorphism $\bar r : \mathrm{GalAb}\,E\,\Omega \to_* (\overline{\mathbb Q}_\ell)^\times$
(`liftAb`, `:228, 388`). Crucially, because $r^m = 1$ and $\mu_m(\overline{\mathbb Q}_\ell)$ is
**finite** in the discrete/$T_1$ topology used on roots of unity, $\ker(\bar r \circ \mathrm{art}) = (\bar r \circ \mathrm{art})^{-1}\bigl((\mu_m \setminus \{1\})^c\bigr)$
is **open** in $\mathbb A_E^\times$ (`isOpen_ker_of_pow`, `:186–200`), and vanishes on $\mathrm{art}.\ker \supseteq E^\times \cdot (E_\infty^\times)^\circ$!
Pushing $\bar r \circ \mathrm{art}$ through $\iota : \overline{\mathbb Q}_\ell \to \mathbb C$ therefore
produces a genuine continuous finite-order Hecke character $\chi = \mathrm{mkOfGal}(\mathrm{art}, \iota, r)$
(`:243, 391`) whose unramified Frobenius values equal $\iota(r(\sigma^{-1}))$ by `art.frob` (`:287–311`)!
Uniqueness (`:404–418`) follows because any two Hecke characters $\chi_1, \chi_2$ with `OrderDvd m`
matching $r$ at unramified primes have $\chi_1 \chi_2^{-1}$ trivial on unramified idèles, on
$E^\times$, and on $(E_\infty^\times)^\circ$, hence trivial everywhere by dense unramified generation
(`eq_of_frob_orderDvd`, `:351–379`). Conversely, in `HeckeLAdicCharacter.full` (`:466–491`), any
$\chi$ with $\chi^m = 1$ satisfies $\chi(\mathrm{diag}(k)) = 1 = k^0$ (`isAlgPos_zero_of_orderDvd`,
`:100`), so `HeckeLAdicCharacter` at weight $n = 0$ produces $r$, and $\iota(r(\sigma^{-1})^m) = \chi(\varpi_v)^m = 1$
forces $r^m = 1$ by Chebotarev density!

(2) In `ChebotarevDegreeOne.dense` (`:51–61`), every open $U \subseteq G_F$ in the Krull topology
contains a coset $\tau \cdot \ker(\mathrm{res}_{L/F})$ for some finite Galois $L/F$ (`isTopologicalBasis_krull`).
Applying `ChebotarevDegreeOne` to $L/F$ and $\sigma = \mathrm{res}_{L/F}(\tau)$ produces $v \notin S$
and $\rho \in D_v$ with $\mathrm{res}_{L/F}(\rho) = \mathrm{res}_{L/F}(\tau)$, so $\rho \in U$!
Two continuous maps into a Hausdorff group agreeing on a dense set are equal (`eq_of_frob`, `:63–68`).
In `rayClassFieldMaximalSt_holds` (`NonemptyAlgHomOfIsRayOfDvd.lean:204–225`), given a ray class
field $L/K$ modulo $\mathfrak m$ and any abelian $L'/K$ unramified outside $\mathfrak m$ with ray-trivial
Artin kernel, embed both into their compositum $M = i(L) \sqcup j(L')$ inside $\overline K$. For
every $\sigma \in \operatorname{Gal}(M/L)$, its restriction to $L$ is $1$, so if $\sigma = \mathrm{Frob}_P$
at an unramified prime $P \nmid \mathfrak m$, the class $[P] \in \mathrm{Cl}_{\mathfrak m}(K)$ lies in
$\ker(\mathrm{art}_{L/K}) = \{1\}$ (since `IsRayClassField` makes $\mathrm{art}_{L/K}$ an isomorphism!),
hence $\mathrm{art}_{L'/K}([P]) = 1$, forcing $\sigma\rvert_{j(L')} = 1$ (`frob_trivial_on_right`,
`:192–202`). Since Frobenius elements generate $\operatorname{Gal}(M/K)$ (`closure_isFrob_eq_top`, `:118`),
every $\sigma \in \operatorname{Gal}(M/L)$ fixes $j(L')$, so $j(L') \subseteq i(L)$ (`range_le`, `:141`),
giving the desired $K$-embedding $L' \hookrightarrow L$! $\square$

---

## 18.3 Cluster II — Iwasawa theory, $p$-adic $L$-values, Kato's Euler system, and Poitou–Tate duality

### 18.3.1 Motivation: where $p$-adic and cohomological edge hypotheses hide

Cluster II audits five `Published` declarations powering Chapters 10 and 11 (`P11` and `P12` `VWin`):
`FerreroWashington`, `SiegelKlingen` / `DeligneRibet`, `Kato`, and `PoitouTateNormalised` /
`PoitouTateDuality`. In algebraic number theory, every one of these theorems has notorious edge cases:
$\ell = 2$ vs odd $\ell$, real archimedean places where $H^2(\mathbb R, \mu_2) \neq 0$, the denominator
$\frac{1}{12}$ of $\zeta(-1)$ before Deligne–Ribet smoothing, and central vs off-center critical points
of modular $L$-functions! Reading the five files at `R3` shows that the archive navigated all four
edge cases explicitly — and in `SiegelKlingenDeligneRibet.lean:223–245`, even included an internal
machine-checked `example` sanity-checking its own smoothing formula at $s = -1$!

### 18.3.2 Worked examples: Deligne–Ribet smoothing at $\zeta_{\{2\}}(-1) = \frac{1}{12}$ and the $\ell = 2$ real-place obstruction

1. **Checking `SiegelKlingenDeligneRibet` at $F = \mathbb Q$, $r = 2$, $\ell = 2$, $c = 3$ (`SiegelKlingenDeligneRibet.lean:223–245`):**
   Take $F = \mathbb Q$, $r = 2$ (evaluating at $s = 1 - r = -1$), $\ell = 2$, $n = 0$ (modulus
   $2^0 = 1$, trivial ray function $\varphi \equiv 1$), and $S = \{(2)\}$ [Lean, read]. Removing the
   $2$-adic Euler factor $(1 - 2^{-(-1)}) = (1 - 2) = -1$ from $\zeta(-1) = -\frac{1}{12}$ gives the
   $S$-imprimitive partial zeta value
   $$\zeta_{\{2\}}(1 - 2) \;=\; (1 - 2^1)\,\zeta(-1) \;=\; (-1)\Bigl(-\frac{1}{12}\Bigr) \;=\; +\frac{1}{12} \;\notin\; \mathbb Z_{(2)},$$
   which has a $2$-adic pole of order $2$! Now introduce Deligne–Ribet's auxiliary prime ideal
   $\mathfrak c = (3)$ (norm $N(\mathfrak c) = 3$, coprime to $2$). Applying the twisted difference
   operator $\Delta_{\mathfrak c}\varphi(I) := \varphi(I) - N(\mathfrak c)^r \varphi(\mathfrak c^{-1} I) = 1 - 3^2 = -8$
   multiplies $\frac{1}{12}$ by $1 - 9 = -8$:
   $$L_S(1 - 2,\, \Delta_{(3)} 1) \;=\; \frac{1}{12} - 3^2 \cdot \frac{1}{12} \;=\; -\frac{8}{12} \;=\; -\frac{2}{3} \;\in\; \mathbb Z_{(2)}!$$
   Lines `223–245` of `SiegelKlingenDeligneRibet.lean` prove both `¬ IsLocalized (2 : ℕ) (1 / 12 : ℚ)`
   and `IsLocalized (2 : ℕ) ((1 / 12 : ℚ) - (3 : ℚ) ^ 2 * (1 / 12))` by `norm_num`, confirming that
   the `Prop` `DeligneRibet` could never hold without `rayTwist` (`:30`) and holds with the exact sign
   $1 - N(\mathfrak c)^r$!
2. **Why `PoitouTateNormalised` excludes $(F = \mathbb Q, \ell = 2)$ via `l ≠ 2 ∨ IsTotallyComplex F`:**
   For $F = \mathbb Q$, $\ell = 2$, $r = 1$, and $M = \mu_2 = \{\pm 1\}$, the real place
   $v_\infty : \mathbb Q \hookrightarrow \mathbb R$ has decomposition group $\operatorname{Gal}(\mathbb C/\mathbb R) \cong \mathbb Z/2\mathbb Z$,
   whose group cohomology $H^n(\mathbb R, \mu_2) \cong \mathbb Z/2\mathbb Z$ is **non-zero in every
   degree $n \ge 1$**! Thus $H^3(G_{\mathbb Q, S}, \mu_2) \xrightarrow{\sim} H^3(\mathbb R, \mu_2) \neq 0$,
   so global cohomological dimension $\le 2$ (`cohDimTwoGlobal`) and the pure finite-place $9$-term
   Poitou–Tate sequence fail at $(F = \mathbb Q, \ell = 2)$ unless real Tate cohomology is added
   `[NeukirchSchmidtWingberg2008, Thm. 8.6.10]`. By requiring `l ≠ 2 ∨ IsTotallyComplex F`
   (`PoitouTateNormalised.lean:15`), the archive cleanly excludes real places at $\ell = 2$ — while
   covering **every** prime $\ell$ (including $\ell = 2$!) on every CM host field $E$!

### 18.3.3 Exact Lean definitions and verbatim literature comparison (Cluster II)

**Definition 18.2 (Cluster II `Published` propositions).** [Lean, read]

1. **`UpperTheory.V.Published.FerreroWashington` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:7–11`, cone `0`):**
   For every number field $K$ with abelian Galois group (`∀ σ τ : K ≃ₐ[ℚ] K, σ * τ = τ * σ`) and
   every rational prime $\ell$ (`Fact l.Prime`), **if** `∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l)`,
   then there exist $C \in \mathbb N$ and a finite set $J$ of prime ideals of $\mathcal O_K$ such that
   for all $n \in \mathbb N$, every element of the $J$-capitulation kernel inside the $\ell$-primary
   class group of the $n$-th cyclotomic $\mathbb Z_\ell$-layer `ZelLayer K l n` is killed by $\ell^C$
   (`∀ c, (∀ 𝔮 ∈ J, IsLocalizedAt 𝔮 c) → (l ^ C) • c = 0`).
2. **`GlobalTheory.Published.SiegelKlingen`, `DeligneRibet`, & `SiegelKlingenDeligneRibet` (`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean:40,45,52`, cone `283`):**
   Over any `[IsTotallyReal F]`, positive integer $r \ge 1$, modulus $\mathfrak f \neq 0$, and finite
   place set $S \supseteq \mathrm{primeFactors}(\mathfrak f)$, `SiegelKlingen` (`:40–43`) gives a unique
   $\mathbb Q$-linear functional $L_S(1-r, -) : \mathrm{RayFunc}(\mathfrak f) \to \mathbb Q$ evaluated
   at `IsSpecValAt1MinusR F S r φ` (`:33–38`, analytic continuation of $\sum_{(I,S)=1} \varphi(I) N(I)^{-s}$
   to $s = 1 - r$). Restricting to prime-power conductor $\mathfrak f = (\ell^n)$ and $S \supseteq \{v \mid \ell\}$,
   `DeligneRibet` (`:45–50`) asserts that for every integral ideal $\mathfrak c$ coprime to $S$ and
   every $\mathbb Z$-valued ray function $\varphi$ (`∀ I, ∃ m : ℤ, φ I = m`), the smoothed value
   $L_S\bigl(1 - r,\, \varphi - N(\mathfrak c)^r (\mathfrak c_* \varphi)\bigr)$ is **$\ell$-integral**
   (`IsLocalized l`, i.e., denominator coprime to $\ell$, `:9`)!
3. **`UpperTheory.V.Published.Kato` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/QuotRepMk.lean:65–73`, cone `1,669`):**
   `∀ {k N l : ℕ} [Fact l.Prime] (f : Newform k N) (χ : DirichletCharacter ℂ N) (r : ℕ), 2 ≤ k → 1 ≤ N → 5 ≤ l → 1 ≤ r → r ≤ k - 1 → 2 * r ≠ k → ∀ P : HeightOneSpectrum (𝓞 f.heckeField), (l : 𝓞 f.heckeField) ∈ P.asIdeal → (ModGalRep.ofNewform f P).IsIrreducibleResidual → Finite (BlochKatoSelmer (ModGalRep.twist (ModGalRep.ofNewform f P) χ r))`.
4. **`GlobalTheory.Published.PoitouTateNormalised` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNormalised.lean:12–28`, cone `11`) & `PoitouTateDuality` (`…/ExistsPrimitiveRootPow.lean:13–27`, cone `10`):**
   For any number field $F$, prime $\ell$ with **`l ≠ 2 ∨ IsTotallyComplex F`**, finite set $S$
   containing all primes above $\ell$, $r \ge 1$, and finite continuous $G_{F,S}$-module $M$ killed by
   $\ell^r$ (`∀ m : M, (l ^ r) • m = 0`), with dual $M' := \operatorname{Hom}_{\mathbb Z/\ell^r\mathbb Z}(M, \mu_{\ell^r}(F_{S,\mathrm{max}}))$
   (`DualMod`), there exists a $9$-term exact sequence
   $$0 \to H^0(G_{F,S}, M) \to \prod_{v \in S} H^0(G_v, M) \to H^2(G_{F,S}, M')^\vee \to H^1(G_{F,S}, M) \to \prod_{v \in S} H^1(G_v, M) \to H^1(G_{F,S}, M')^\vee \to H^2(G_{F,S}, M) \to \prod_{v \in S} H^2(G_v, M) \to H^0(G_{F,S}, M')^\vee \to 0$$
   whose three middle/boundary restriction maps (`f1`, `f4`, `f7`) coincide definitionally (`Normalized9`)
   with standard `resProd`!

| Lean `Prop` | Classical source | Word-for-word comparison (hypotheses & conclusion) | Verdict |
|---|---|---|---|
| `Published.FerreroWashington` (`PublishedTheorems/FerreroWashington.lean:7`) | Ferrero–Washington `[FerreroWashington1979]` | Adds `∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l)` and allows finitely many primes $J$ to be localized away (`IsLocalizedAt 𝔮 c`, bounding $\ell$-torsion of the $S$-class group $\mathrm{Cl}_J(K_n)[\ell^\infty]$ by $\ell^C$). Adjoining $\zeta_\ell$ (or $\zeta_4$) is an abelian finite extension preserving $\mu_\ell = 0$, and proved unconditionally in `FerreroWashingtonIndex/FerreroWashington.lean:104`! | **Faithful** (harmless $\mu_{2\ell}$ base hypothesis; **both** `Prop` & 809-module Sinnott proof read at `R3` `[Lean, read]`!) |
| `SiegelKlingenDeligneRibet` (`SiegelKlingenDeligneRibet.lean:52`) | Siegel (1937), Klingen (1962), Deligne–Ribet `[DeligneRibet1980]` | Rationality (`SiegelKlingen`) holds for arbitrary conductor $\mathfrak f$; $\ell$-integrality (`DeligneRibet`) specializes to $\ell$-power conductor $\mathfrak f = (\ell^n)$ and $\mathbb Z$-valued ray functions (sufficient for cyclotomic $\mathbb Z_\ell$-layers; `[DeligneRibet1980]` also treats prime-to-$\ell$ tame conductors and $p$-adic measures). | **Special case** ($\ell^n$ conductor & $\mathbb Z$-valued ray functions; `[Lean, read]` for `Prop`, `157`-line consequences, & `example`) |
| `UpperTheory.V.Published.Kato` (`QuotRepMk.lean:65`) | Kato `[Kato2004, Thm. 14.2]`; Rubin `[Rubin2000]` | Assumes $\ell \ge 5$, residual irreducibility, and **`1 ≤ r ≤ k - 1` with `2 * r ≠ k`**, concluding `Finite (BlochKatoSelmer ...)` **without** writing $L(f, \chi, r) \neq 0$! Sound because $2r \neq k$ excludes the central point $k/2$: by functional equation + Euler-product non-vanishing on $\Re s \ge \frac{k+1}{2}$ (and in `KatoUse` at $k = 2e+1$, $r \in \{e, e+1\}$!), $L(f, \chi, r) \neq 0$ holds automatically! | **Special case (off-center critical points `2 * r ≠ k`)** (`[Lean, read]` for `Prop` & `KatoUse`; `1,669`-module proof cone `[Open]`) |
| `PoitouTateNormalised` (`PoitouTateNormalised.lean:12`) | Poitou (1967), Tate (1963); `[NeukirchSchmidtWingberg2008, Thm. 8.6.10]`; `[Wiles1995, Prop. 1.6]` | Restricts to `l ≠ 2 ∨ IsTotallyComplex F` (avoiding real archimedean Tate terms at $\ell = 2$) and $S \supseteq \{v \mid \ell\}$. Includes `Normalized9` pinning `f1, f4, f7` to canonical restriction maps `resProd`. | **Special case (`l ≠ 2 ∨ IsTotallyComplex F`)** (`[Lean, read]` for `Prop` & Greenberg–Wiles deduction; upstream proof `[Open]`) |

### 18.3.4 Fidelity lemma and line-by-line `R3` proofs (Cluster II)

**Lemma 18.2 (Cluster II consumer alignment and Greenberg–Wiles cancellation).** [Lean, read]

1. *(Off-center non-vanishing alignment in `KatoUse`: `UpperTheory.V.U3.KatoUse`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:13–17`)*
   *In `KatoUse`, `UpperTheory.V.Published.Kato` is invoked exclusively through `KatoUse := Published.Kato`: for the odd weights $k = 2e + 1 \ge 3$ arising from $U(3)$ base change to $\mathbb Q$, $2r \neq 2e + 1$ holds for **every** integer $r \in [1, 2e]$, and at the edge points $r = e + 1$ (analytic point $s = 1$) and $r = e$ (analytic point $s = 0$, paired with $s = 1$ by the functional equation), $L(f, \chi, r) \neq 0$ holds unconditionally.*
2. *(Global cohomological dimension $2$ and Greenberg–Wiles formula from `PoitouTateNormalised`: `cohDimTwoGlobal`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsPrimitiveRootPow.lean:70–85`, and `greenbergWiles_of_poitouTate`, `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesOfPoitouTate.lean:45–106`)*
   *`PoitouTateNormalised` implies the Greenberg–Wiles Euler-characteristic identity `[Wiles1995, Prop. 1.6]` for every finite $G_{F,S}$-module $M$ (`l ≠ 2 ∨ IsTotallyComplex F`) and local Selmer conditions $\mathcal L_v \le H^1(G_v, M)$ with orthogonal complements $\mathcal L_v^\perp \le H^1(G_v, M')$ ($\lvert \mathcal L_v \rvert \cdot \lvert \mathcal L_v^\perp \rvert = \lvert H^1(G_v, M) \rvert$):*
   $$\lvert H^1_{\mathcal L}(G_{F,S}, M) \rvert \cdot \lvert H^0(G_{F,S}, M') \rvert \cdot \prod_{v \in S} \lvert \mathcal L_v \rvert
   \;=\;
   \lvert H^1_{\mathcal L^\perp}(G_{F,S}, M') \rvert \cdot \lvert H^0(G_{F,S}, M) \rvert \cdot \prod_{v \in S} \lvert H^0(G_v, M) \rvert.$$

*Proof.*
(1) Line `17` of `KatoUse.lean` is literally `abbrev KatoUse : Prop := Published.Kato`! Why did
`Published.Kato` (`QuotRepMk.lean:68`) include the explicit arithmetic guard `2 * r ≠ k` when $1 \le r \le k - 1$?
In classical normalization, a weight-$k$ newform $f \in S_k^{\mathrm{new}}(\Gamma_1(N))$ has critical
strip $\frac{k-1}{2} < \Re s < \frac{k+1}{2}$ centered at $s = \frac{k}{2}$, and its Euler product
converges and is non-zero on $\Re s \ge \frac{k+1}{2}$ (Jacquet–Shalika non-vanishing on the boundary
$\Re s = \frac{k+1}{2}$!). Recall the
Ramanujan–Petersson normalization of modular forms: for a holomorphic cusp form $f(z) = \sum_{n \ge 1} a_n q^n$
of weight $k$, Deligne's bound is $\lvert a_p \rvert \le 2 p^{(k-1)/2}$, so the Dirichlet series
$L(f, \chi, s) = \sum_{n \ge 1} a_n \chi(n) n^{-s}$ converges absolutely for **$\Re s > \frac{k+1}{2}$**,
is non-vanishing on **$\Re s \ge \frac{k+1}{2}$** by Jacquet–Shalika / Rankin–Selberg, and satisfies a
functional equation relating $s$ to **$k - s$**! Now check **every** integer $r \in \{1, \dots, k-1\}$
with $2r \neq k$:
- Either **$2r > k$**, which for integers $2r, k \in \mathbb Z$ means $2r \ge k + 1$, i.e.
  **$r \ge \frac{k+1}{2}$** — so $s = r$ sits **on or to the right of the abscissa of convergence $\frac{k+1}{2}$**,
  where $L(f, \chi, r) \neq 0$ ALWAYS holds for EVERY weight $k \ge 2$!
- Or **$2r < k$**, which means $2(k - r) > k$, so the reflected integer $k - r \ge \frac{k+1}{2}$ has
  $L(\bar f, \bar\chi, k - r) \neq 0$, and the non-zero $\Gamma$-factors at $s = r \ge 1$ force
  $L(f, \chi, r) \neq 0$ by the functional equation!
What a mathematical gem [Expository]: **among integers $r \in [1, k-1]$, the central point $r = k/2$ is
the ONLY integer inside the open strip $(\frac{k-1}{2}, \frac{k+1}{2})$ of width $1$!** Every single
integer $r \in [1, k-1]$ with $2r \neq k$ satisfies $\lvert r - \frac{k}{2} \rvert \ge \frac{1}{2}$,
so $r \ge \frac{k+1}{2}$ or $k - r \ge \frac{k+1}{2}$, making $L(f, \chi, r) \neq 0$ **unconditionally
true for all $k \ge 2$** (matching Loeffler's Zulip `#642442900` observation `[Community]` and proving
that `Published.Kato` is 100% faithful to Kato's Theorem 14.2 `[Kato2004]` on its entire integer domain!).

(2) Open `GreenbergWilesOfPoitouTate.lean:45–106` [Lean, read]. Let $Q := \prod_{v \in S} H^1(G_v, M)$
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
   and **$m > 2n$** (`2 * A.rank < B.rank`, `WeilSiegelFormulaUnitary.lean:68`) for absolute convergence
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
2. **`GlobalTheory.Published.BaseChangeDefiniteUnitary` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:235–241`, cone `783`) & `BaseChangeIsobaric` (`…/BaseChangeIsobaric.lean:40–48`, cone `784`):**
   For every CM field $E$, $n \ge 1$, everywhere-unramified CM extension `hunr : ∀ w : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal`,
   and discrete automorphic representation $\sigma$ of the standard definite unitary group `UA E n := UJ (conjAd E) 1`,
   `BaseChangeDefiniteUnitary` produces an `IsobaricDecomp E n` (`Π` on $\mathrm{GL}_n(\mathbb A_E)$)
   satisfying `IsWeakBaseChange E n σ Π` (conjugate self-duality $\Pi^\vee \cong \Pi^c$ of each summand
   plus unramified Satake parameter agreement off a finite place set $S$), while `BaseChangeIsobaric`
   upgrades unramified local compatibility to **every** prime $p \notin S$ (`SatakeCompatAtPrime`).
3. **`GlobalTheory.Published.WeilSiegelFormula` (`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/WeilSiegelFormula.lean:18–28`, cone `1,599`), `WeilSiegelFormulaUnitary` (`…/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean:56–69`, cone `827`), & `SiegelWeilUnitaryConvergent` (`…/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18–32`, cone `1,803`):**
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
| `ClozelPurity` & `RegularAlgebraicPurity` (`ClozelPurity.lean:10`, `GaloisGeometry₂/RegularAlgebraicPurity.lean:14`) | Clozel `[Clozel1990, Lemme 4.9]` | Clozel proves purity of $\pi_\infty$ for regular algebraic cuspidal $\pi$ on $\mathrm{GL}_n(\mathbb A_F)$ over **any** number field $F$; the archive restricts to `[IsTotallyComplex E]` / `[IsCMField E]` (where archimedean places are complex, simplifying $\mathrm{GL}_n(\mathbb C)$ Adams–Johnson parameters). | **Special case** (totally complex / CM fields; `[Lean, read]` for `Prop`, upstream cones `878`–`1,538` `[Open]`) |
| `BaseChangeDefiniteUnitary` & `BaseChangeIsobaric` (`GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:235`, `BaseChangeIsobaric.lean:40`) | Rogawski (1990, $n \le 3$); Labesse (2011, general $n$) | Restricts to the standard identity definite form `UA E n` and **everywhere-unramified** $E/E^+$ (`hunr`), which avoids ramified fundamental-lemma / Kottwitz-sign obstructions at finite places of $E^+$! | **Domain-restricted special case** (consumer alignment verified at `BaseChangeIdentities/Narrow.lean:47` `[Lean, read]`; `15,289`-module proof cone `[Open]`) |
| `WeilSiegelFormula`, `WeilSiegelFormulaUnitary`, & `SiegelWeilUnitaryConvergent` (`Divisors₂/WeilSiegelFormula.lean:18`, `WeilSiegelFormulaUnitary.lean:56`, `SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18`) | Weil `[Weil1965]`; Kudla–Rallis `[KudlaRallis1994]`; Ichino (2004) | Splits Weil's $m > 2n$ range from Kudla–Rallis's convergent $n < m \le 2n$ ($n + r_B < m$) range on unitary groups over `D : D7`, matching the exact convergence hypotheses of both papers. | **Special case** (unitary dual pairs over `D7` in convergent ranges; `[Lean, read]` for `Prop`s, upstream cones `[Open]`) |
| `DeRhamPotSemistable` (`DeRhamPotSemistable.lean:13`) | Berger `[Berger2002, Thm. 0.7]`; André (2002), Kedlaya (2004), Mebkhout (2002) | Faithful statement of Fontaine's $p$-adic monodromy conjecture ($\mathrm{de\ Rham} \implies \text{potentially semistable}$) for $\mathrm{GL}_{\mathbb Q_\ell}(V)$, parameterized by `Nonempty (LocTied l P AI)` (verified non-empty via `exists_locPrime_tied` `[Lean]`). | **Faithful** (`[Lean, read]` for `Prop` & $L$-linear scalar-extension proof `:89–132`; upstream proof `[Open]`) |

### 18.4.4 Fidelity lemma and line-by-line `R3` proofs (Cluster III)

**Lemma 18.3 (Consumer domain alignment for unitary base change and $L$-linear scalar extension for `DeRhamPotSemistable`).** [Lean, read]

1. *(Consumer check on `BaseChangeDefiniteUnitary`: `definiteN_of`, `src/Development/AutomorphicArithmetic/Foundations/BaseChangeIdentities/Narrow.lean:47–74`, contrasted with `UnusedSlot72`, `…/DiscreteSpectrumResidualClassification.lean:7`)*
   *At its downstream consumer `definiteN_of`, the everywhere-unramified hypothesis `hunr : ∀ w, Algebra.IsUnramifiedAt (𝓞 E⁺) w.asIdeal` is carried explicitly as part of the narrow host datum and passed directly to `BaseChangeDefiniteUnitary` and `BaseChangeIsobaric`; by contrast, `UnusedSlot72 : Prop := True` is never inspected downstream.*
2. *(Non-vacuity and $L/\mathbb Q_\ell$-linear extension of `DeRhamPotSemistable`: `DeRhamPotSemistable.coeff` and `isPstAt`, `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/DeRhamPotSemistable.lean:89–132`, plus `exists_locPrime_tied`, `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281`)*
   *The period-ring witness `Nonempty (LocTied l P AI)` is unconditionally inhabited for every local place $v \mid \ell$ (`exists_locPrime_tied`), and `DeRhamPotSemistable` over $\mathbb Q_\ell$ implies potential semistability `isPstAt` for arbitrary finite-dimensional $L$-linear Galois representations $\rho : G_E \to_* \mathrm{GL}_L(V)$ (`[FiniteDimensional ℚ_[l] L]`).*

*Proof.*
(1) In `BaseChangeIdentities/Narrow.lean:47–74`, `definiteN_of` takes hypotheses `hbcd : Published.BaseChangeDefiniteUnitary`
and `hbci : Published.BaseChangeIsobaric` and proves the narrow base-change package `DefiniteN`:
lines `52–54` introduce `hunr : ∀ w : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Algebra.IsUnramifiedAt ...`
from `DefiniteN`'s own signature and feed `hbcd E n hn hunr σ` (`:58`) and `hbci E n hn hunr σ` (`:59`)
directly! Thus the unramified-CM restriction in `BaseChangeDefiniteUnitary` is **not** a hidden gap;
it is an explicit architectural invariant propagated from the host CM tower!

(2) First, `exists_locPrime_tied` (`ExistsLocalPrimeAinf.lean:281` `[Lean]`) constructs a concrete
`(P, AI)` with `Nonempty (LocTied l P AI)` for every prime $\ell$, number field $E$, and prime ideal
$v$ above $\ell$, certifying that `DeRhamPotSemistable` is never vacuously satisfied by an empty
`LocTied` type! Second, in `DeRhamPotSemistable.lean:89–132` [Lean, read], suppose $L/\mathbb Q_\ell$
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
   $\zeta_{\{2\}}(-1) = \frac{1}{12}$ (`SiegelKlingenDeligneRibet.lean:223`), $(F = \mathbb Q, \ell = 2)$
   for Poitou–Tate, or $(F = \mathbb Q, E = \mathbb Q(i))$ for ramified CM base change!
5. **Keep statement fidelity separate from proof-cone reading:** A **Faithful** verdict upgrades the
   *statement* match from `[Open]` to `[Lean, read]`; unless you have also read the upstream proof
   cone (`*_of_literature`) to `R3` (as we did for `FerreroWashington` in Chapter 11!), keep the
   upstream *proof body* honestly marked `[Open]`.

### 18.5.2 Masullo's counterpart

How does Masullo's 940-page manuscript handle background literature compared with Alpöge's `P18` layer [Expository]?

- **Appendices A–E (`pp. 537–932`) vs `GlobalTheory.Published.*` (`P18`):** Masullo devotes nearly
  400 pages of appendices (`Appendix A` Algebraic Number Theory, `pp. 539–586`; `Appendix B` Analytic
  Number Theory, `pp. 587–656`; `Appendix C` Locally Convex TVS, `pp. 657–754`; `Appendix D`
  Schwartz–Bruhat Functions, `pp. 755–866`; `Appendix E` Topological Stacks, `pp. 867–932`) to
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
| 1 | `GlobalTheory.Published.GlobalArtinReciprocity` (`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70`) | 9 | Artin `[Artin1927]`, Tate `[Tate1967]`, Neukirch `[Neukirch1999, Thm. VI.6.1]` | **Faithful** (full idèlic Artin map over all number fields; geometric Frobenius on uniformizers) | Wrapper `StandardTheoremStatements/GlobalArtinReciprocity.lean:8` (cone 1,015) `[Open]` | [Lean, read] |
| 2 | `GlobalTheory.Published.HeckeLAdicCharacter` (`…/ExistsUniqueHcharOfFiniteOrder.lean:74`; finite-order bridge `:381, 466`) | 9 | Weil (1956), Serre (1968) | **Faithful (slightly stronger)** (`IsAlgPos` requires algebraicity only on $E_+^\times$; finite-order bijection proved in file!) | Wrapper `:14` (cone 1,015) `[Open]`; finite-order bridge `:381–491` `R3` | [Lean, read] |
| 3 | `GlobalTheory.Published.RayClassFieldSt` & `RayClassFieldMaximalSt` (`src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:17,32`) | 686 | Takagi (1920), Neukirch `[Neukirch1999, Thm. VI.6.2]` | **Faithful** (narrow real-place sign condition built into `RayClassGroup 𝔪`) | `RayClassFieldMaximalSt` proved in file (`:204–225`, `R3`); `rayClassFieldSt` wrapper `[Open]` | [Lean, read] |
| 4 | `GlobalTheory.Published.ChebotarevDegreeOne` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:12`) | 211 | Chebotarev `[Tschebotareff1926]` | **Safe weakening** (existential infinitude of degree-1 Frobenius primes outside $S$, omitting natural density; implies `dense` `:51`) | Proved in `Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean:17–64` (cone 289, `R3`; cyclic base `[Open]`) | [Lean, read] |
| 5 | `UpperTheory.V.Published.FerreroWashington` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:7`) | 0 | Ferrero–Washington `[FerreroWashington1979]` | **Faithful** (adds harmless $\zeta_\ell$ / $\zeta_4 \in K$ base-layer root of unity and finite $J$-localization) | Proved in `FerreroWashingtonIndex/FerreroWashington.lean:104` (cone 809, Sinnott route read in Ch. 11 `R3`!) | [Lean, read] |
| 6 | `GlobalTheory.Published.SiegelKlingen`, `DeligneRibet`, `SiegelKlingenDeligneRibet` (`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean:40,45,52`) | 283 | Deligne–Ribet `[DeligneRibet1980]` | **Special case** (rationality for all $\mathfrak f$; $\ell$-integrality for $\mathfrak f = (\ell^n)$ & $\mathbb Z$-valued ray functions; $\zeta_{\{2\}}(-1) = 1/12$ `example` at `:223`!) | Consequences `:157–245` `R3`; upstream analytic proof `[Open]` | [Lean, read] |
| 7 | `UpperTheory.V.Published.Kato` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/QuotRepMk.lean:65`; `KatoUse` at `…/UnitaryThreeGroups/KatoUse.lean:13`) | 1,669 | Kato `[Kato2004, Thm. 14.2]`, Rubin `[Rubin2000]` | **Special case (off-center `2 * r ≠ k`)** ($L(f,\chi,r) \neq 0$ omitted because every integer $r \in [1,k-1]$ with $2r \neq k$ has $\lvert r - k/2 \rvert \ge 1/2$, forcing $L \neq 0$!) | `KatoUse` (`cone 1,713`) `R3`; upstream Beilinson–Kato Euler-system proof `[Open]` | [Lean, read] |
| 8 | `GlobalTheory.Published.PoitouTateNormalised` & `PoitouTateDuality` (`…/GaloisCohomology₂/PoitouTateNormalised.lean:12`, `…/ExistsPrimitiveRootPow.lean:13`) | 11 | Poitou–Tate `[NeukirchSchmidtWingberg2008, Thm. 8.6.10]`, `[Wiles1995, Prop. 1.6]` | **Special case (`l ≠ 2 ∨ IsTotallyComplex F`)** (avoids real Tate terms at $\ell = 2$; covers all $\ell$ on CM hosts; `Normalized9` pins restriction maps) | `cohDimTwoGlobal` (`:70`) & `greenbergWiles_of_poitouTate` (`GreenbergWilesOfPoitouTate.lean:45`, cone 718) `R3`; upstream proof `[Open]` | [Lean, read] |
| 9 | `GlobalTheory.Published.ClozelPurity` & `RegularAlgebraicPurity` (`…/GaloisGeometry₂/ClozelPurity.lean:10`, `…/GaloisGeometry₂/RegularAlgebraicPurity.lean:14`) | 878 / 1,538 | Clozel `[Clozel1990, Lemme 4.9]` | **Special case** (restricted from all number fields to `[IsTotallyComplex E]` / `[IsCMField E]`) | Upstream Shimura/archimedean proof cones `[Open]` | [Lean, read] |
| 10 | `GlobalTheory.Published.BaseChangeDefiniteUnitary` & `BaseChangeIsobaric` (`…/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:235`, `…/BaseChangeIsobaric.lean:40`) | 783 / 784 | Rogawski (1990), Labesse (2011) | **Domain-restricted special case** (identity definite form `UA E n` + everywhere-unramified CM extension `hunr`, aligned with `BaseChangeIdentities/Narrow.lean:47`!) | Consumer `definiteN_of` `R3`; `15,289`-module trace-formula proof cone `[Open]` | [Lean, read] |
| 11 | `GlobalTheory.Published.WeilSiegelFormula`, `WeilSiegelFormulaUnitary`, & `SiegelWeilUnitaryConvergent` (`…/Divisors₂/WeilSiegelFormula.lean:18`, `…/WeilSiegelFormulaUnitary.lean:56`, `…/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18`) | 1,599 / 827 / 1,803 | Weil `[Weil1965]`, Kudla–Rallis `[KudlaRallis1994]` | **Special case** (unitary dual pairs over `D : D7` in Weil's $m > 2n$ and Kudla–Rallis's $n < m \le 2n$, $n + r_B < m$ convergent ranges) | Upstream Siegel–Weil proof cones `[Open]` | [Lean, read] |
| 12 | `GlobalTheory.Published.DeRhamPotSemistable` (`…/AutomorphicForms₂/DeRhamPotSemistable.lean:13`; `UnusedSlot72` contrast at `…/DiscreteSpectrumResidualClassification.lean:7`) | 135 | Berger `[Berger2002, Thm. 0.7]` | **Faithful** (`LocTied` verified inhabited via `exists_locPrime_tied` `[Lean]`; contrasted with fossil `UnusedSlot72 : Prop := True`) | Scalar-extension `coeff`/`isPstAt` (`:89–132`) `R3`; upstream $p$-adic differential-equation proof `[Open]` | [Lean, read] |

**Summary of the chapter.** Auditing 14 load-bearing propositions across three sub-clusters of
`P18` (`GlobalTheory.Published.*` and `UpperTheory.V.Published.*`) at reading level `R3` replaces
speculation about theorem names with exact mathematical verdicts [Lean, read]: five entries
(`GlobalArtinReciprocity`, `HeckeLAdicCharacter`, `RayClassFieldSt`/`RayClassFieldMaximalSt`,
`FerreroWashington`, and `DeRhamPotSemistable`) are **faithful** formalizations of their classical
counterparts (with `HeckeLAdicCharacter` slightly stronger via `IsAlgPos`, and `DeRhamPotSemistable`'s
period-ring bundle `LocTied` verified non-vacuous); `ChebotarevDegreeOne` is a **safe existential
weakening** whose 18-line companion lemma `dense` recovers full topological Frobenius density; and
the remaining entries (`SiegelKlingenDeligneRibet`, `Kato`, `PoitouTateNormalised`, `ClozelPurity`,
`BaseChangeDefiniteUnitary`, and `SiegelWeilUnitaryConvergent`) are **mathematically sound
specializations** whose domain guards (`2 * r ≠ k` forcing off-center $L \neq 0$, `l ≠ 2 ∨ IsTotallyComplex F`,
and everywhere-unramified CM extensions $E/E^+$) align cleanly with the CM host-field consumers on
the spine of `src/Main.lean`.
