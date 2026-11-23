# Trace of the two "squeeze" inequalities after `setDiv` installs `hExpl6`

Archive: `RH-lean-archive/lean/src` (read-only; nothing was built). All paths below are relative to `src/`.
Legend: **[read]** means I read the source at the cited lines. **[inferred]** means I worked it out from names or signatures without reading the proof.

## 0. Summary verdict

| Inequality | Where it is stated | Where it is discharged | Verdict |
|---|---|---|---|
| (L) lower: `htMap(Bk u) ≤ div.h u` (only when `Bk u ≠ 0`) | `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:128-131` (`WordFacts`); `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:81-82` (`LinkDIV_at`) | `src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:193-207` (`divClausesR_of`, clause 2) through `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:161-170` | **Substantive in form, and not rfl.** It is a sum over places of log operator-norm bounds along a column chain (`height_chain_atR`), together with an eigenvalue input `eig6`. **Conditional caveat:** the statement is guarded by `Bk u ≠ 0`. If `Bk u = 0`, the proof is a trivial constant witness (lines 196-201). |
| (U) upper: `muDual + div.h u − Fo ≤ MAIN u + error` | `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:132-133`; `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:83-85` | `src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:208-245` (clause 3), then `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:131-` (`RecNums.divIneq`), then `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:261-` (`rhs_le_record`) | **Substantive in form, and not rfl.** It combines a μ bound (`boundsMu`), a passage inequality, `L3main`, and a long numeric record inequality (`divIneqRecord`). The two sides are different expressions: `R.hu` against `R.rhs`. |

On the claim that the squeeze "compares a quantity with itself and holds by reflexivity": I found no step where either inequality is closed by `rfl` or `le_rfl` on identical sides.

The only definitional identification is `div.h u = hExpl6 …` (setDiv / `Fm.h_eq`). It is then matched against the record height through `hTie_of` (`src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:341-345`), which is a rewriting proof: `R.hu − meanLog κ = hExpl6`. This identification is real, and it does mean that `h` is not an independent geometric quantity. However, both inequalities still need their own proofs from separately supplied inputs (`DivInputs0R`). Whether those inputs are non-degenerate on the live route is the real open question (§4).

## 1. Where `h = hExpl6` enters [read]

- `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean:25-30`: `setDiv` overwrites `div.h := h`.
- `src/Formalism/LocalRingCardinality/KernelPlaceMeanBound.lean:25-27`:
  ```lean
  def hExpl6 (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
    SZbP D L C u + (∑ j ∈ SizeData₂.lifts D, kernelPlaceMeanBound D L C u j) - (∑ j ∈ SizeData₂.lifts D, L6lo D L C j) -
      meanE D (fun e => Real.log (X.kapR e))
  ```
- `src/Formalism/SharpRestriction/InertJacobiLevels/AsmIface.lean:163`: the family field `h_eq : ∀ u, D.div.h u = DV.hExpl6 D L X C.Csz u`. This is used at `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:687` (`hhx := Fm.h_eq x hx1 i`).
- `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:341-345`, the bridge from the record height `R.hu` to `div.h`:
  ```lean
  theorem hTie_of ... (hnum : hu = SZbP D L Csz u + (∑ j ∈ …, kernelPlaceMeanBound …) - ∑ j ∈ …, L6lo D L Csz j)
      (hh : D.div.h u = hExpl6 D L Z Csz u) : hu - Formalism.DivisionValues.meanLog κ = D.div.h u := by
    rw [hh, hExpl6, meanE, meanEmb_eq_meanLog κ (fun e => Real.log (Z.kapR e)) (fun σ => by rw [hk σ]), hnum]
  ```
  The record height `R.hu` (`src/Formalism/LocalToGlobal/Divisibility/Inputs.lean:188-198`) is `hA + Σ_j (hB j − hX j)`. These terms are explicit sums of `ph(ν)`, `logHook`, `aT·logT`, and constants·`La`. `hExpl6` is that same formula, transported through `hnum_of_numRecTieH`. So **h is a formula in row/record sizes, not an independent geometric height.** This confirms Nielsen's premise.

## 2. The statements [read]

`src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:128-133`:
```lean
def WordFacts {D : D7} (L : SizeData₂ D) (C Cabs : ℝ) (u : D.what₂.Word) : Prop :=
  (D.div.Nu u).L.map ((D.div.Bk u).restrictScalars (𝓞 D.what₂.LL)) ≤ D.div.cc ∧
  (D.div.Bk u ≠ 0 → Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) ≤
    D.div.h u) ∧
  D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u +
    C * (D.host.TT.card : ℝ) * L.sc.a * L.La + C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)
```
These become fields 6 and 7 of `LinkDIV_at` (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:78-91`), through `linkDIV_at_words` (`src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:327-334`):
`… fun u hu => (hW u).2.1 hu, fun u => (hW u).2.2, …`.

The chain is: `linkDIVt_of_rowsF` (`src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:649-693`), then `DivisionPackageFace.wordFacts` (`:633-640`), then `wordFacts_of_face` → `wordFacts_of_clauses` → `wordFacts_of` (`:135-235`).

`wordFacts_of` (`:135-153`) is pure transport. It rewrites the clause-level facts `c2 : B ≠ 0 → ht ≤ hu − kap` and `c3 : muC − kap + hu − Fo2 ≤ rhs` along `tH : hu − kap = div.h u` and `tR : rhs ≤ MAIN + …`. All the content is therefore in `DivClausesR` (`src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:111-123`) and in `rhs_le_record`.

## 3. The discharges

### 3.1 Lower bound (L) [read]

`src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:184-207` (`divClausesR_of`, clause 2):
```lean
by_cases hne : P.cols.col.B u = 0
· refine exists_cu _ (fun _ => R.hu - meanLog P.cols.κ) _ hX (fun v => Or.inl ?_) (le_of_eq ?_)
  · rw [hne]; simp [Formalism.HN.opNormAt]
  …
· have nK := nK_of_cb I.cb (fun j v => …) I.nKcb
  obtain ⟨Hv, Hm⟩ := height_chain_atR wf1 P.cols u hne I.X0 I.base_matrix_det_unit I.ch I.hn.hPn I.hn.sz I.nP nK
  have h1 := I.hn.le_hu (∑ j, N.l6 j) I.eig6
  refine exists_cu _ (fun v => I.hn.hPn + … - Real.log (P.cols.κ v) - minOver …) _ hX (fun v => Or.inr (Hv v)) ?_
  linarith [Hm, h1]
```
The clause is then turned into `htMap ≤ h − k` by `htMap_le_of_bound` (`src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:161-170`), which uses a per-place `log_le_log` and a mean.

**Estimates used (case `B ≠ 0`):**
- `height_chain_atR` (`src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:125-`) [statement read, proof not read]: a factorisation of `B` through a chain of matrices `ch.Kj`. It bounds `log ‖B‖_v²` by `hP + Σ hK − log κ_v − minOver(Σ log λ)`.
- Inputs from `DivInputs0R` (`:26-60`): `nP` (op-norm of the last chain map ≤ `exp hPn`), `nKcb` (log of chain-block squares ≤ Σ sizes), `eig6 : Σ R.hX j ≤ Σ N.l6 j` (eigenvalue lower bound), `base_matrix_det_unit`, and `Xc_unit`.

**Classification:** substantive in form. These are explicit operator norms at infinite places and eigenvalue sums. It is not `rfl`.

**Degeneracy risk:** the clause is vacuous when `Bk u = 0`. `Bk` comes from `P.cols.col.B` through `hBk`. That is the column data's own pairing, which Nielsen calls "the row data's own period pairing". I did not find any lemma proving `Bk u ≠ 0` on the live route; a grep for `*Bk*ne_zero*` found nothing. Downstream, `frameReal_at_of` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean:679-689`) takes `hht` in the same guarded form, so the guard is never discharged there either. **Open:** whether `Bk = 0` on the live data. If it is, (L) carries no information.

### 3.2 Upper bound (U) [read]

`src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:208-245` (clause 3) proves `P.cols.muCC − meanLog κ + R.hu − 2·FoOfR P ≤ R.rhs` from:
- `hB := P.base.boundsMu … I.Sy … I.bi I.bLG I.biv I.borderedMinorImage I.twisted_third_sum_le`. This is a valuation-based μ bound over finite places `y ∈ Sy` (local bases `eb`, `vw`, `lw`, ramification `ramw`).
- `hp := (P.extra.passage de0 de3 _ P.extra.fun0).2`. This is a passage inequality between the column μ and the base μ.
- `I.L3main`, `I.errB`, `I.Qb`, `I.la_le`, and `I.constant_ge_twenty_eight`.
- The closing step: `exact R.divIneq _ mu0 (FoOfR P) _ _ hC hM hpass I.errB`.

`RecNums.divIneq` (`src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:131-`) reduces to `Formalism.DivisionValues.divIneqRecord` with about 35 record facts (`R.p1 … R.p33`, `weight_height_sum_le`, `weight_sum_eq`, `hu_eq`). Three side goals inside it are closed by `le_refl`/`le_refl _` (lines ~150-153), namely `(fun _ => le_refl _)` and `(le_refl _)`. These are bookkeeping instances in which a parameter of the general lemma is chosen equal to the record value. They are not the main inequality.

`rhs_le_record` (`src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:261-290`) proves `R.rhs ≤ MAIN u + C·… + C·…`. It uses `mainT = MAIN` (`numRecTie_ofRecord`, `:302-`, with `hM` from `ofRecord_mainT`, `src/Formalism/LocalToGlobal/Divisibility/NumbersLemmas.lean:846`) and absorbs constants (`50·C0+10 ≤ C`, `60·ce ≤ C`, `x^eps ≤ x^(Cabs·eps)`).

**The two sides really differ.** `R.hu = hA + Σ(hB − hX)` (`src/Formalism/LocalToGlobal/Divisibility/Inputs.lean:198`), while
```lean
def rhs : ℝ :=
  (∑ t ∈ R.TT, (R.m * (ph (R.aT t) - R.aT t * R.logOm) - R.aT t * R.logT)) +
    ((50 * R.C0 + 10) * ((R.TT.card : ℝ) * R.a * R.La) +
      60 * R.ce * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc))))
```
(`src/Formalism/LocalToGlobal/Divisibility/Inputs.lean:200-203`). The inequality `hu + μ − 2Fo ≤ rhs` is a non-trivial arithmetic statement relating hook/`ph(ν)` sums to `ph(aT)` sums. It is not of the form `a ≤ a`.

**Classification:** substantive in form: valuations, a passage inequality, and a combinatorial record inequality. It is not `rfl`.

**Caveat (inferred, consistent with Nielsen §7):** both sides are built from one source of data, the row/record numbers. So (U) is a constraint *among row-side quantities*, not a comparison between an independent geometric height and the main term. "Not reflexive" does not imply "carries the intended geometric content".

## 4. Is either inequality fed by a degenerate hypothesis?

- `anyGeometry` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:19`) enters at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44-52` as the `geoCl anyGeometry` argument to `open_and_linked_of_stronger_extension_alt`, `rowFun_at_gridA_alt` (`hCF0`), and `linked_bundles_l3_of_open_alt` [read]. **I did not trace** how `geoCl anyGeometry` reaches `DivInputs0R` / `DivisionPackageColumns` (`inp`, `brTied`, `hNu`, `hBk`) [open]. If the column data `Pk.core.cols` (which supplies `B`, `XE`, `κ`, `muCC`) is built from the geometry argument, then the inputs to (L) and (U) could inherit the degeneracy.
- `BridgeRowsT/F.pkg` (`src/Formalism/LocalToGlobal/Divisibility/RecBridgeTied.lean:168-`, `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:643`) is itself conditional: `DIVinN Fm → ∃ … Nonempty (DivisionPackage…)`. It is supplied on the live route by `DivisionKernelConstantBounds → BridgeRowsT` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:180`) and by `src/Formalism/LocalToGlobal/ClassOfRecordOfChoice.lean:200`. I did not read either [open].
- `LinkDIVt := LinkEta → DIVinN → LinkDIV` (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:94-95`). In `topDesWin` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean:28`), `DIVinN` is supplied by `divinN_of_hypV Fm h0 (hV …) aN aZ` [read call site, not proof].
- I found no instance of `True`, an empty type, or a zero map inside the `divClausesR_of` / `wordFacts_of*` / `rhs_le_record` proofs themselves [read]. The only vacuity mechanism I identified locally is the `Bk u ≠ 0` guard on (L).

## 5. Does the final contradiction use the inequalities?

[read] The consumers of `LinkDIV` on the `topDesWin` route are as follows:
- **(L) field 6:** `frameRealF_of` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean:716`) does `obtain ⟨hOne, -, -, -, hRR, hht, -⟩ := lD x e0 i` and passes `hht` to `frameReal_at_of`, which places it into `FrameReal_at` (`:687-689`). That flows into `FrameF`, which is the `hFr` argument of `linkGLOBAL_of` (`src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:858`) and of `linkCore` (`src/Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean:39`).
- **(U) field 7:** `linkCore` (`src/Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean:139, 168-170`) does `have h := (hDu u0).2.2.2.2.2.2.1 u`, and `M.data_DIV` (`src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:580-592`) turns it into `(M.data …).DIV C`. That is used in `L2`, part of building `ChainTied` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97-`). According to Nielsen §7, `zeroFreeOn_of_tiedWin_cyc` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean:90`) turns `ChainTied` into a Chebyshev-type window inequality and then into the zero-free region.
- Other fields of `LinkDIV` are also consumed: field 3 by `muZero_of_linkDIV`, fields 4 and 5 by `latF`/RR rank, and field 2 by `trF_sbF_of_linkDIV`.

So both inequalities are **consumed** (they are not dead code) on the route into `ChainTied`. **I did not verify** that `zeroFreeOn_of_tiedWin_cyc` actually uses the `DIV` / `FrameReal` components, as opposed to only carrying them along. I could not locate the `LChain.SizeData₂ Dd C Xpp` definition that bundles them [open].

## 6. Open items

1. Is `Bk u ≠ 0` ever established on the live route? If `Bk = 0`, (L) is vacuous.
2. How does `geoCl anyGeometry` (and the `rfl`-copied lattices of Nielsen §6) reach `DivInputs0R` (`nP`, `nKcb`, `eig6`, `bi`, `biv`, `L3main`, …)? Are those inputs proved substantively or from copied data?
3. Read the proofs of `height_chain_atR`, `boundsMu`, `extra.passage`, and `divIneqRecord` (only statements and call sites were read).
4. Read `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:180` and `src/Formalism/LocalToGlobal/ClassOfRecordOfChoice.lean:200` (the `BridgeRowsT` producers) and `divinN_of_hypV`.
5. Follow `ChainTied` into `zeroFreeOn_of_tiedWin_cyc` to confirm that the `DIV` and `FrameReal` data are actually used in the final inequality.
6. Harry Tong's reachability findings (`anyGeometry`, `divXFl`, `geoDegenerate`) show reachability, not that these inputs are used by (L) or (U). That link remains unproven by this trace.


## Addendum (parent check)

`exists_divStage` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsDivStage.lean:334`) sets `Bk := fun _ => 0`, `h := fun _ => 0` (l. 347-348). `setDiv` overwrites `h` only. Live-route membership not yet checked.
