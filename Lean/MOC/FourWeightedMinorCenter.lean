import MOC.ContactCensus
import MOC.FourMinorTransport
import MOC.FourQuaternionMinor
import MOC.PlaneHullEdges
import MOC.WeightedMinor
import Mathlib.Data.Fintype.Powerset

/-! Exact order-four inclusion for the center of the weighted-minor
neighborhood. The edge data use the finite spectral lists directly. -/

open BigOperators Finset Matrix

namespace MOC

private abbrev CenterPoint := ℚ × ℚ

private def centerPointAdd (x y : CenterPoint) : CenterPoint :=
  (x.1 + y.1, x.2 + y.2)

private def centerPointSub (x y : CenterPoint) : CenterPoint :=
  (x.1 - y.1, x.2 - y.2)

private def centerPointMul (x y : CenterPoint) : CenterPoint :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

private def centerPointCross (x y : CenterPoint) : ℚ :=
  x.1 * y.2 - x.2 * y.1

private def centerLeft : Fin 4 → CenterPoint :=
  ![(0, 0), (-1/5, 4/15), (-1/10, 2/15), (177/793, -66/793)]

private def centerRight : Fin 4 → CenterPoint :=
  ![(1/2, 0), (1, 0), (-1/5, -2/5), (-232/1345, -344/1345)]

private noncomputable def centerPointToComplex (x : CenterPoint) : ℂ := ⟨x.1, x.2⟩

noncomputable def fourWeightedMinorCenterLeft : Fin 4 → ℂ :=
  fun i => centerPointToComplex (centerLeft i)

noncomputable def fourWeightedMinorCenterRight : Fin 4 → ℂ :=
  fun i => centerPointToComplex (centerRight i)

private theorem centerPointToComplex_add (x y : CenterPoint) :
    centerPointToComplex (centerPointAdd x y) =
      centerPointToComplex x + centerPointToComplex y := by
  ext <;> simp [centerPointToComplex, centerPointAdd]

private theorem centerPointToComplex_mul (x y : CenterPoint) :
    centerPointToComplex (centerPointMul x y) =
      centerPointToComplex x * centerPointToComplex y := by
  ext <;> simp [centerPointToComplex, centerPointMul, Complex.mul_re, Complex.mul_im]

private theorem centerPointToComplex_sub (x y : CenterPoint) :
    centerPointToComplex (centerPointSub x y) =
      centerPointToComplex x - centerPointToComplex y := by
  ext <;> simp [centerPointToComplex, centerPointSub]

private theorem centerPointCross_cast (x y : CenterPoint) :
    (centerPointCross x y : ℝ) = planeCross (centerPointToComplex x) (centerPointToComplex y) := by
  simp [centerPointCross, centerPointToComplex, planeCross]

private def centerVertex (p : Fin 24) : CenterPoint :=
  let a (j : Fin 4) := centerPointAdd (centerLeft j) (centerRight (fourPerm p j))
  centerPointMul (centerPointMul (centerPointMul (a 0) (a 1)) (a 2)) (a 3)

private theorem centerVertex_toComplex (p : Fin 24) :
    centerPointToComplex (centerVertex p) =
      matchingProduct fourWeightedMinorCenterLeft fourWeightedMinorCenterRight (fourPerm p).symm := by
  rw [matchingProduct_inverse, Fin.prod_univ_four]
  simp only [centerVertex, centerPointToComplex_mul, centerPointToComplex_add,
    fourWeightedMinorCenterLeft, fourWeightedMinorCenterRight] <;> ring

private def centerPolygon : Fin 9 → Fin 24 := ![0, 6, 18, 12, 11, 17, 4, 10, 2]
private def centerPrev : Fin 9 → Fin 9 := ![8, 0, 1, 2, 3, 4, 5, 6, 7]
private def centerNext : Fin 9 → Fin 9 := ![1, 2, 3, 4, 5, 6, 7, 8, 0]

private def centerHullVertex (i : Fin 9) : CenterPoint := centerVertex (centerPolygon i)

private def centerGap (i : Fin 9) (p : Fin 24) : ℚ :=
  centerPointCross (centerPointSub (centerHullVertex (centerNext i)) (centerHullVertex i))
    (centerPointSub (centerVertex p) (centerHullVertex i))

private def centerScale : Fin 9 → ℚ :=
  ![17278677000, 17278677000, 5759559000, 8639338500, 17278677000,
    5759559000, 8639338500, 5759559000, 5759559000]

private inductive CenterCostTerm where
  | ordinary (rows columns : Finset (Fin 4)) (coefficient : ℚ)
  | weighted (rows columns : Fin 24) (transposed : Bool) (tau coefficient : ℚ)

private structure CenterMinorTerm where
  rows : Finset (Fin 4)
  columns : Finset (Fin 4)
  coefficient : ℚ

private def centerCanonicalRows : Fin 5 → Finset (Fin 4) :=
  ![{1}, {2}, {2, 3}, {1, 2}, {1, 3}]

private def centerCanonicalColumns : Fin 5 → Finset (Fin 4) :=
  ![{2}, {1}, {2, 3}, {1, 2}, {0, 2}]

private def centerExpandTerm (t : CenterCostTerm) (k : Fin 5) : CenterMinorTerm :=
  match t with
  | .ordinary I J c => ⟨I, J, if k = 0 then c else 0⟩
  | .weighted r c tr τ w =>
    let I := (centerCanonicalRows k).map (fourPerm r).toEmbedding
    let J := (centerCanonicalColumns k).map (fourPerm c).toEmbedding
    let v := w * (![1, 1, 1 + τ, 1 + τ⁻¹, -1] : Fin 5 → ℚ) k
    if tr then ⟨J, I, v⟩ else ⟨I, J, v⟩

-- Exact edge certificates recovered from the local fixture bundle.
private def centerTerms : Fin 9 → Fin 12 → CenterCostTerm :=
  ![
    ![.ordinary {0, 1} {2, 3} 12353204,
      .ordinary {0} {2} 1754326,
      .ordinary {3} {0} 10280790,
      .ordinary {1} {3} 10280790,
      .ordinary {3} {1} 3759270,
      .ordinary {0, 3} {0, 1} 35975515,
      .ordinary {2} {1} 1754326,
      .ordinary {0, 1} {0, 2} 125309,
      .ordinary {1} {2} 3759270,
      .ordinary {0, 3} {0, 2} 2742704,
      .ordinary {0, 2} {0, 3} 1016566,
      .ordinary {0} {0} 0],
    ![.ordinary {0, 1} {2, 3} 7287072,
      .ordinary {3} {0} 12743296,
      .ordinary {1} {3} 12743296,
      .ordinary {3} {1} 6014832,
      .ordinary {0, 3} {0, 1} 18406793,
      .ordinary {0, 1} {0, 2} 375927,
      .ordinary {1} {2} 6014832,
      .ordinary {0, 3} {0, 2} 2069092,
      .ordinary {0, 2} {0, 3} 437088,
      .ordinary {2} {3} 1754326,
      .ordinary {0} {0} 1754326,
      .ordinary {0} {0} 0],
    ![.ordinary {0, 1} {2, 3} 1469536,
      .ordinary {3} {0} 3942144,
      .ordinary {1} {3} 3942144,
      .ordinary {3} {1} 2004944,
      .ordinary {0, 3} {0, 1} 3878866,
      .ordinary {1} {2} 2004944,
      .ordinary {0, 3} {0, 2} 417745,
      .ordinary {0, 2} {0, 3} 208800,
      .ordinary {2} {3} 626545,
      .ordinary {0, 1} {0, 1} 125309,
      .ordinary {0} {0} 626545,
      .ordinary {0} {0} 0],
    ![.ordinary {0, 1} {2, 3} 78174203,
      .ordinary {0, 2} {2, 3} 83468699,
      .ordinary {0, 3} {1, 2} 2920677,
      .ordinary {0, 2} {0, 1} 83468699,
      .ordinary {0, 3} {0, 2} 811449,
      .ordinary {3} {2} 17644731,
      .ordinary {2} {3} 5886159,
      .ordinary {0, 2} {0, 2} 1903995,
      .ordinary {0, 3} {0, 3} 4824672,
      .ordinary {1} {1} 15740736,
      .ordinary {0, 1} {0, 1} 39403460,
      .ordinary {0} {0} 3982164],
    ![.ordinary {0} {3} 11396200,
      .ordinary {0, 3} {2, 3} 15025384,
      .ordinary {2} {0} 30266405,
      .ordinary {0, 2} {1, 3} 2159325,
      .ordinary {1} {0} 91386365,
      .ordinary {0, 2} {0, 1} 7507845,
      .ordinary {1} {2} 13448760,
      .ordinary {3} {2} 32029275,
      .ordinary {0, 3} {0, 3} 3262120,
      .ordinary {3} {3} 51559555,
      .ordinary {1} {1} 55145205,
      .ordinary {0} {0} 15608085],
    ![.ordinary {0, 3} {2, 3} 21749679,
      .ordinary {0, 2} {1, 3} 2504690,
      .ordinary {0, 3} {1, 3} 1243055,
      .ordinary {1} {0} 7289825,
      .ordinary {0} {1} 2101250,
      .ordinary {0, 3} {0, 1} 14179235,
      .ordinary {0, 2} {0, 3} 5207155,
      .ordinary {0, 2} {0, 2} 2504690,
      .ordinary {2} {2} 2101250,
      .ordinary {3} {3} 7289825,
      .ordinary {0, 1} {0, 1} 5426975,
      .ordinary {0} {0} 0],
    ![.ordinary {0, 1} {2, 3} 1891680,
      .ordinary {0, 3} {2, 3} 5677504,
      .ordinary {0, 2} {1, 3} 528960,
      .ordinary {0, 2} {1, 2} 1260195,
      .ordinary {0, 3} {1, 3} 682080,
      .ordinary {1} {0} 835200,
      .ordinary {0, 3} {0, 1} 9220840,
      .ordinary {0, 2} {0, 2} 528960,
      .ordinary {3} {3} 835200,
      .ordinary {0, 1} {0, 1} 1517280,
      .ordinary {0} {0} 0,
      .ordinary {0} {0} 0],
    ![.ordinary {0, 3} {2, 3} (244769152 / 91),
      .ordinary {0, 2} {1, 2} 253935,
      .ordinary {0, 3} {0, 1} (201902710 / 91),
      .weighted 16 15 true 16 (644417600 / 6279),
      .weighted 13 14 false 16 (401280160 / 6279),
      .weighted 3 12 false 16 (3090480 / 91),
      .weighted 0 19 true 16 (36811200 / 91),
      .weighted 12 11 true 16 (98513680 / 6279),
      .weighted 6 17 false 16 118320,
      .weighted 6 17 true 16 (341651120 / 6279),
      .ordinary {0} {0} 0,
      .ordinary {0} {0} 0],
    ![.ordinary {0, 1} {2, 3} 6079200,
      .ordinary {0, 1} {1, 3} (54726248 / 153),
      .ordinary {3} {0} (53891512 / 153),
      .ordinary {1} {3} (53891512 / 153),
      .weighted 7 15 true 16 (43758767 / 306),
      .weighted 0 19 true 8 (7224712 / 9),
      .weighted 0 19 true 16 (13969793 / 18),
      .ordinary {0} {0} 0,
      .ordinary {0} {0} 0,
      .ordinary {0} {0} 0,
      .ordinary {0} {0} 0,
      .ordinary {0} {0} 0]]

private def centerCostTermValid : CenterCostTerm → Prop
  | .ordinary _ _ w => 0 ≤ w
  | .weighted _ _ _ τ w => 0 < τ ∧ 0 ≤ w

private instance (t : CenterCostTerm) : Decidable (centerCostTermValid t) := by
  cases t <;> unfold centerCostTermValid <;> infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem centerTerms_valid : ∀ (e : Fin 9) (k : Fin 12),
    centerCostTermValid (centerTerms e k) := by
  decide +kernel

private abbrev CenterEdgeTerm := Fin 12 × Fin 5

private def centerEdgeTerm (e : Fin 9) (k : CenterEdgeTerm) : CenterMinorTerm :=
  centerExpandTerm (centerTerms e k.1) k.2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem centerGap_certificate : ∀ (e : Fin 9) (p : Fin 24),
    centerScale e * centerGap e p = ∑ k : CenterEdgeTerm,
      let t := centerEdgeTerm e k
      if t.columns.map (fourPerm p).symm.toEmbedding = t.rows then t.coefficient else 0 := by
  decide +kernel

private theorem centerScale_pos : ∀ e : Fin 9, 0 < centerScale e := by
  decide +kernel

private theorem centerTurn_pos : ∀ e : Fin 9,
    0 < centerPointCross (centerPointSub (centerHullVertex e) (centerHullVertex (centerPrev e)))
      (centerPointSub (centerHullVertex (centerNext e)) (centerHullVertex e)) := by
  decide +kernel

private def centerSeparatorValue {R : Type*} [AddGroup R] (v : Fin 24 → R) : R :=
  v 10 - v 4 + v 0 + v 1 + v 2 + v 7 + v 8 + v 13 + v 19

private def centerIndicator {R : Type*} [Zero R] [One R] (I J : Finset (Fin 4))
    (p : Fin 24) : R :=
  if J.map (fourPerm p).symm.toEmbedding = I then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem centerSeparator_indicator : ∀ I J : Finset (Fin 4),
    0 ≤ centerSeparatorValue (centerIndicator (R := ℚ) I J) := by
  decide +kernel

private theorem centerSeparator_gap : centerSeparatorValue (centerGap 8) < 0 := by
  decide +kernel

noncomputable section

private def centerCompensated (τ : ℝ) (m : Finset (Fin 4) → Finset (Fin 4) → ℝ) : ℝ :=
  m {1} {2} + m {2} {1} + (1 + τ) * m {2, 3} {2, 3} +
    (1 + τ⁻¹) * m {1, 2} {1, 2} - m {1, 3} {0, 2}

private theorem centerCompensated_orthogonal (τ : ℝ) (hτ : 0 < τ)
    (O : Matrix.orthogonalGroup (Fin 4) ℝ) :
    0 ≤ centerCompensated τ (subsetMinorSq (Complex.ofRealHom.mapMatrix O.val)) := by
  obtain ⟨q, r, hq, hr, hs, hd⟩ := exists_quaternionRotation_same_squaredMinors O
  let U := Complex.ofRealHom.mapMatrix O.val
  let x := subsetMinorSq U {2, 3} {2, 3}
  let y := subsetMinorSq U {1, 2} {1, 2}
  have hx : 0 ≤ x := subsetMinorSq_nonneg U _ _
  have hy : 0 ≤ y := subsetMinorSq_nonneg U _ _
  have h0 := mixed_quaternion_rotation_weighted q r
    (by simpa only [Fin.sum_univ_four] using hq) (by simpa only [Fin.sum_univ_four] using hr)
  dsimp only at h0
  rw [← hs 1 2, ← hs 2 1,
    ← hd 2 3 2 3 (by decide) (by decide),
    ← hd 1 2 1 2 (by decide) (by decide),
    ← hd 1 3 0 2 (by decide) (by decide)] at h0
  change 0 ≤ subsetMinorSq U {1} {2} + subsetMinorSq U {2} {1} + x -
    subsetMinorSq U {1, 3} {0, 2} + y + 2 * Real.sqrt (x * y) at h0
  have hA : 0 ≤ τ * x := mul_nonneg hτ.le hx
  have hB : 0 ≤ τ⁻¹ * y := mul_nonneg (inv_nonneg.mpr hτ.le) hy
  have hprod : (τ * x) * (τ⁻¹ * y) = x * y := by
    calc
      _ = (τ * τ⁻¹) * (x * y) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hτ.ne', one_mul]
  have hroot : Real.sqrt (τ * x) * Real.sqrt (τ⁻¹ * y) = Real.sqrt (x * y) := by
    rw [← Real.sqrt_mul hA, hprod]
  have hbudget : 2 * Real.sqrt (x * y) ≤ τ * x + τ⁻¹ * y := by
    nlinarith only [sq_nonneg (Real.sqrt (τ * x) - Real.sqrt (τ⁻¹ * y)),
      Real.sq_sqrt hA, Real.sq_sqrt hB, hroot]
  change 0 ≤ subsetMinorSq U {1} {2} + subsetMinorSq U {2} {1} +
    (1 + τ) * x + (1 + τ⁻¹) * y - subsetMinorSq U {1, 3} {0, 2}
  simp only [add_mul, one_mul]
  linarith only [h0, hbudget]

private theorem centerCompensated_unitary (τ : ℝ) (hτ : 0 < τ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ centerCompensated τ (subsetMinorSq U) := by
  obtain ⟨κ, inst, w, O, hw, _, hm⟩ := four_minor_mixture U hU
  letI : Fintype κ := inst
  let m (k : κ) := subsetMinorSq (Complex.ofRealHom.mapMatrix (O k).val)
  let L : (Finset (Fin 4) → Finset (Fin 4) → ℝ) →ₗ[ℝ] ℝ where
    toFun := centerCompensated τ
    map_add' v z := by
      simp only [centerCompensated, Pi.add_apply]
      ring
    map_smul' c v := by
      change centerCompensated τ (c • v) = c * centerCompensated τ v
      simp only [centerCompensated, Pi.smul_apply, smul_eq_mul]
      ring
  have htable : subsetMinorSq U = ∑ k, w k • m k := by
    funext I J
    simpa only [m, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hm I J
  change 0 ≤ L (subsetMinorSq U)
  rw [htable, map_sum]
  apply Finset.sum_nonneg
  intro k _
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg (hw k) (centerCompensated_orthogonal τ hτ (O k))

private theorem centerUnitary_transpose (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    IsUnitary Uᵀ := by
  have ht : (Uᵀ)ᴴ = (Uᴴ)ᵀ := by ext i j; rfl
  constructor
  · rw [ht, ← Matrix.transpose_mul, hU.2, Matrix.transpose_one]
  · rw [ht, ← Matrix.transpose_mul, hU.1, Matrix.transpose_one]

private theorem centerMinor_transpose (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (I J : Finset (Fin 4)) :
    subsetMinorSq Uᵀ I J = subsetMinorSq U J I := by
  by_cases hcard : I.card = J.card
  · let f : I ≃ J := Fintype.equivOfCardEq (by simpa using hcard)
    rw [subsetMinorSq_eq_normSq_det_submatrix Uᵀ (centerUnitary_transpose U hU) I J
      (Equiv.refl I) f, subsetMinorSq_eq_normSq_det_submatrix U hU J I f (Equiv.refl I)]
    let N := U.submatrix (Subtype.val ∘ f) (Subtype.val ∘ Equiv.refl I)
    change Complex.normSq (Nᵀ).det = Complex.normSq N.det
    rw [Matrix.det_transpose]
  · simp only [subsetMinorSq, dif_neg hcard, dif_neg (Ne.symm hcard)]

private def centerTransformMixer (U : Matrix (Fin 4) (Fin 4) ℂ)
    (r c : Fin 24) (tr : Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  (if tr then Uᵀ else U).submatrix (fourPerm r) (fourPerm c)

private theorem centerTransformMixer_unitary (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (r c : Fin 24) (tr : Bool) : IsUnitary (centerTransformMixer U r c tr) := by
  cases tr
  · exact unitary_reindex (fourPerm r) (fourPerm c) hU
  · exact unitary_reindex (fourPerm r) (fourPerm c) (centerUnitary_transpose U hU)

private theorem centerWeightedMinor_transform (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (r c : Fin 24) (tr : Bool) (τ w : ℚ) (k : Fin 5) :
    let t := centerExpandTerm (.weighted r c tr τ w) k
    subsetMinorSq (centerTransformMixer U r c tr) (centerCanonicalRows k) (centerCanonicalColumns k) =
      subsetMinorSq U t.rows t.columns := by
  cases tr
  · exact squared_minor_reindex (fourPerm r) (fourPerm c) U hU _ _
  · change subsetMinorSq (Uᵀ.submatrix (fourPerm r) (fourPerm c))
      (centerCanonicalRows k) (centerCanonicalColumns k) =
        subsetMinorSq U ((centerCanonicalColumns k).map (fourPerm c).toEmbedding)
          ((centerCanonicalRows k).map (fourPerm r).toEmbedding)
    rw [squared_minor_reindex (fourPerm r) (fourPerm c) Uᵀ (centerUnitary_transpose U hU),
      centerMinor_transpose U hU]

private theorem centerTerm_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (t : CenterCostTerm) (ht : centerCostTermValid t) :
    0 ≤ ∑ k : Fin 5, let v := centerExpandTerm t k
      (v.coefficient : ℝ) * subsetMinorSq U v.rows v.columns := by
  cases t with
  | ordinary I J w =>
    have hw : 0 ≤ (w : ℝ) := by exact_mod_cast (show 0 ≤ w from ht)
    simpa [centerExpandTerm, Fin.sum_univ_succ] using mul_nonneg hw (subsetMinorSq_nonneg U I J)
  | weighted r c tr τ w =>
    obtain ⟨hτ, hw⟩ := (show 0 < τ ∧ 0 ≤ w from ht)
    have hτ' : 0 < (τ : ℝ) := by exact_mod_cast hτ
    have hw' : 0 ≤ (w : ℝ) := by exact_mod_cast hw
    let V := centerTransformMixer U r c tr
    let v (k : Fin 5) := centerExpandTerm (.weighted r c tr τ w) k
    let b : Fin 5 → ℚ := ![1, 1, 1 + τ, 1 + τ⁻¹, -1]
    have hb (k : Fin 5) : (v k).coefficient = w * b k := by
      cases tr <;> rfl
    have hm (k : Fin 5) : subsetMinorSq U (v k).rows (v k).columns =
        subsetMinorSq V (centerCanonicalRows k) (centerCanonicalColumns k) :=
      (centerWeightedMinor_transform U hU r c tr τ w k).symm
    have he : (∑ k : Fin 5, ((v k).coefficient : ℝ) *
        subsetMinorSq U (v k).rows (v k).columns) =
          (w : ℝ) * centerCompensated (τ : ℝ) (subsetMinorSq V) := by
      simp_rw [hb, Rat.cast_mul, hm, mul_assoc]
      rw [← Finset.mul_sum]
      norm_num [b, centerCompensated, centerCanonicalRows, centerCanonicalColumns,
        Fin.sum_univ_succ, Rat.cast_inv, Rat.cast_add] <;> ring
    change 0 ≤ ∑ k : Fin 5, ((v k).coefficient : ℝ) * subsetMinorSq U (v k).rows (v k).columns
    rw [he]
    exact mul_nonneg hw' (centerCompensated_unitary τ hτ' V (centerTransformMixer_unitary U hU r c tr))

private def centerHull (i : Fin 9) : ℂ := centerPointToComplex (centerHullVertex i)

private theorem centerHull_turn (e : Fin 9) :
    0 < planeCross (centerHull e - centerHull (centerPrev e))
      (centerHull (centerNext e) - centerHull e) := by
  have h := (Rat.cast_pos (K := ℝ)).mpr (centerTurn_pos e)
  simpa only [centerHull, centerPointCross_cast, centerPointToComplex_sub] using h

private theorem centerAllMixer_edges (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (e : Fin 9) :
    0 ≤ planeCross (centerHull (centerNext e) - centerHull e)
      (determinantValue fourWeightedMinorCenterLeft fourWeightedMinorCenterRight U - centerHull e) := by
  let a := fourWeightedMinorCenterLeft
  let b := fourWeightedMinorCenterRight
  let l := centerHull e
  let r := centerHull (centerNext e)
  let η : ℂ := ⟨-(r - l).im, -(r - l).re⟩
  let S : ℝ := centerScale e
  have hS : 0 < S := (Rat.cast_pos (K := ℝ)).mpr (centerScale_pos e)
  let I (k : CenterEdgeTerm) := (centerEdgeTerm e k).rows
  let J (k : CenterEdgeTerm) := (centerEdgeTerm e k).columns
  let w (k : CenterEdgeTerm) := ((centerEdgeTerm e k).coefficient : ℝ) / S
  have hdecomp (σ : FourPerm) : (η * matchingProduct a b σ).re - (η * l).re =
      ∑ k, if (J k).map σ.toEmbedding = I k then w k else 0 := by
    obtain ⟨p, hp⟩ := fourPerm_surjective σ.symm
    have hσ : (fourPerm p).symm = σ := by rw [hp, Equiv.symm_symm]
    have hcast := congrArg (Rat.castHom ℝ) (centerGap_certificate e p)
    simp only [map_mul, map_sum, apply_ite, map_zero] at hcast
    change S * (centerGap e p : ℝ) =
      ∑ k, if (J k).map (fourPerm p).symm.toEmbedding = I k
        then ((centerEdgeTerm e k).coefficient : ℝ) else 0 at hcast
    rw [hσ] at hcast
    have hcastGap : (centerGap e p : ℝ) =
        (η * matchingProduct a b σ).re - (η * l).re := by
      simp only [centerGap, centerPointCross_cast, centerPointToComplex_sub, ← centerHull,
        centerVertex_toComplex, hσ]
      exact planeCross_edge_direction l r (matchingProduct a b σ)
    rw [hcastGap, mul_comm S] at hcast
    have he := (eq_div_iff (ne_of_gt hS)).mpr hcast
    rw [he, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp only [w, zero_div]
  have hgap := gap_eq_minor_decomposition a b η (η * l).re U hU I J w hdecomp
  change 0 ≤ planeCross (r - l) (determinantValue a b U - l)
  rw [planeCross_edge_direction l r, hgap, Fintype.sum_prod_type]
  apply Finset.sum_nonneg
  intro j _
  have he : (∑ k : Fin 5, w (j, k) * subsetMinorSq U (I (j, k)) (J (j, k))) =
      (∑ k : Fin 5, ((centerExpandTerm (centerTerms e j) k).coefficient : ℝ) *
        subsetMinorSq U (centerExpandTerm (centerTerms e j) k).rows
          (centerExpandTerm (centerTerms e j) k).columns) / S := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [w, I, J, centerEdgeTerm, div_mul_eq_mul_div]
  rw [he]
  exact div_nonneg (centerTerm_nonneg U hU (centerTerms e j) (centerTerms_valid e j)) hS.le

/-- The exact center of the weighted-minor neighborhood satisfies the full
order-four determinant inclusion for every complex unitary mixer. -/
theorem holds_fourWeightedMinorCenter (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds fourWeightedMinorCenterLeft fourWeightedMinorCenterRight U := by
  have hm := mem_planeHull_of_edges centerHull centerPrev centerNext
    (determinantValue fourWeightedMinorCenterLeft fourWeightedMinorCenterRight U)
    (by decide +kernel) centerHull_turn (centerAllMixer_edges U hU)
  unfold Holds
  apply convexHull_mono ?_ hm
  rintro _ ⟨e, rfl⟩
  refine ⟨(fourPerm (centerPolygon e)).symm, ?_⟩
  exact (centerVertex_toComplex (centerPolygon e)).symm

/-- The signed area gap for the edge from matching label 2 to label 0. -/
def fourWeightedMinorCenterFinalGap (p : Fin 24) : ℝ := (centerGap 8 p : ℝ)

theorem fourWeightedMinorCenterFinalGap_eq (p : Fin 24) :
    let P (j : Fin 24) := matchingProduct fourWeightedMinorCenterLeft
      fourWeightedMinorCenterRight (fourPerm j).symm
    fourWeightedMinorCenterFinalGap p = planeCross (P 0 - P 2) (P p - P 2) := by
  have hl : centerHullVertex 8 = centerVertex 2 := rfl
  have hr : centerHullVertex (centerNext 8) = centerVertex 0 := rfl
  simp only [fourWeightedMinorCenterFinalGap, centerGap, hl, hr, centerPointCross_cast,
    centerPointToComplex_sub, centerVertex_toComplex]

private def centerSeparator : (Fin 24 → ℝ) →ₗ[ℝ] ℝ where
  toFun := centerSeparatorValue
  map_add' f g := by
    simp only [centerSeparatorValue, Pi.add_apply] <;> ring
  map_smul' c f := by
    change centerSeparatorValue (c • f) = c * centerSeparatorValue f
    simp only [centerSeparatorValue, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The final edge of the center hull has no nonnegative decomposition into
ordinary subset-image indicators, of any subset size. -/
theorem fourWeightedMinorCenter_no_ordinary_certificate {κ : Type*} [Fintype κ]
    (I J : κ → Finset (Fin 4)) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ¬ ∀ p : Fin 24, fourWeightedMinorCenterFinalGap p =
      ∑ k, if (J k).map (fourPerm p).symm.toEmbedding = I k then w k else 0 := by
  intro h
  let v (k : κ) := centerIndicator (R := ℝ) (I k) (J k)
  have hv (k : κ) : 0 ≤ centerSeparator (v k) := by
    have hc := (Rat.cast_nonneg (K := ℝ)).mpr (centerSeparator_indicator (I k) (J k))
    change 0 ≤ centerSeparatorValue (centerIndicator (R := ℝ) (I k) (J k))
    simpa only [centerSeparatorValue,
      centerIndicator, Rat.cast_sub, Rat.cast_add, apply_ite, Rat.cast_zero, Rat.cast_one] using hc
  have hg : centerSeparator fourWeightedMinorCenterFinalGap < 0 := by
    have hc := (Rat.cast_lt_zero (K := ℝ)).mpr centerSeparator_gap
    change centerSeparatorValue fourWeightedMinorCenterFinalGap < 0
    simpa only [centerSeparatorValue,
      fourWeightedMinorCenterFinalGap, Rat.cast_sub, Rat.cast_add] using hc
  have hreconstruct : fourWeightedMinorCenterFinalGap = ∑ k, w k • v k := by
    funext p
    rw [h p]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, centerIndicator,
      mul_ite, mul_one, mul_zero]
  rw [hreconstruct, map_sum] at hg
  simp_rw [map_smul, smul_eq_mul] at hg
  exact (not_lt_of_ge (Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (hv k))) hg

end

end MOC
