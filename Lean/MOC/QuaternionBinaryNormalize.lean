import MOC.QuaternionBinaryBasis
import MOC.Realification
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Normalization of the binary quaternion table by skew-pair
cancellation. -/

open Finset BigOperators Matrix

namespace MOC.QuaternionIntrinsic

noncomputable section

def quaternionBinaryReal (q : BinaryLabels → ℝ) : Matrix BinaryLabels BinaryLabels ℝ :=
  Matrix.of fun i j => quaternionBinarySign (i+j) j * q (i+j)

theorem quaternionBinary_gram (q : BinaryLabels → ℝ) :
    (quaternionBinaryReal q)ᵀ * quaternionBinaryReal q = (∑ k, q k^2) • 1 := by
  classical
  have hb := quaternionBinarySign_basisSigning
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply]
  simp only [Matrix.transpose_apply, quaternionBinaryReal, Matrix.of_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq, mul_one]
    calc
      _ = ∑ k, q (k+i)^2 := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          _ = quaternionBinarySign (k+i) i ^ 2 * q (k+i)^2 := by ring
          _ = _ := by rw [hb.sq, one_mul]
      _ = _ := Equiv.sum_comp (Equiv.addRight i) (fun k => q k^2)
  · rw [Matrix.one_apply_ne hij, mul_zero]
    let f (k : BinaryLabels) := (quaternionBinarySign (k+i) i * q (k+i)) *
      (quaternionBinarySign (k+j) j * q (k+j))
    have hneg (k : BinaryLabels) : f (k+(i+j)) = -f k := by
      have hi : k+(i+j)+i = k+j := by
        calc
          _ = k+j+(i+i) := by abel
          _ = _ := by rw [binaryLabels_exponentTwo, add_zero]
      have hj : k+(i+j)+j = k+i := by
        calc
          _ = k+i+(j+j) := by abel
          _ = _ := by rw [binaryLabels_exponentTwo, add_zero]
      have hh := hb.pair (k+i) i j hij
      rw [show i+j+(k+i) = k+j by
        calc
          _ = k+j+(i+i) := by abel
          _ = _ := by rw [binaryLabels_exponentTwo, add_zero]] at hh
      have hh' : quaternionBinarySign (k+j) i * quaternionBinarySign (k+i) j =
          -(quaternionBinarySign (k+i) i * quaternionBinarySign (k+j) j) := by
        calc
          _ = (quaternionBinarySign (k+j) i * quaternionBinarySign (k+j) j *
            (quaternionBinarySign (k+i) i * quaternionBinarySign (k+i) j)) *
            (quaternionBinarySign (k+i) i * quaternionBinarySign (k+j) j) := by
              symm
              calc
                _ = quaternionBinarySign (k+i) i^2 * quaternionBinarySign (k+j) j^2 *
                    (quaternionBinarySign (k+j) i * quaternionBinarySign (k+i) j) := by ring
                _ = _ := by rw [hb.sq, hb.sq, one_mul, one_mul]
          _ = _ := by rw [hh, neg_one_mul]
      unfold f
      rw [hi, hj]
      calc
        _ = (quaternionBinarySign (k+j) i * quaternionBinarySign (k+i) j) *
            (q (k+i) * q (k+j)) := by ring
        _ = _ := by rw [hh']; ring
    have he := Equiv.sum_comp (Equiv.addRight (i+j)) f
    change (∑ k, f (k+(i+j))) = ∑ k, f k at he
    simp_rw [hneg, Finset.sum_neg_distrib] at he
    change ∑ k, f k = 0
    linarith

/-- A unit coordinate vector produces a genuine unitary mixer. -/
theorem quaternionBinary_isUnitary (q : BinaryLabels → ℝ) (hq : ∑ k, q k^2 = 1) :
    IsUnitary (signedKleinMixerTable quaternionBinarySign q) := by
  have hgram := quaternionBinary_gram q
  rw [hq, one_smul] at hgram
  let R : Matrix BinaryLabels BinaryLabels ℝ := quaternionBinaryReal q
  have hO : R ∈ Matrix.orthogonalGroup BinaryLabels ℝ :=
    (Matrix.mem_orthogonalGroup_iff' _ ℝ).mpr hgram
  exact isUnitary_ofReal_orthogonal ⟨R,hO⟩


/-- The real determinant has unit magnitude by the Gram identity
and positive sign by connectedness of the unit sphere. -/
theorem quaternionBinary_det_real (q : BinaryLabels → ℝ) (hq : ∑ k, q k^2 = 1) :
    (quaternionBinaryReal q).det = 1 := by
  classical
  let E := EuclideanSpace ℝ BinaryLabels
  let S : Set E := Metric.sphere 0 1
  let f (v : E) : ℝ := (quaternionBinaryReal fun k => v k).det
  have hnorm (v : E) : ‖v‖^2 = ∑ k, v k^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : BinaryLabels => ℝ) v
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank, show Module.finrank ℝ E = 4 by
      unfold E
      rw [finrank_euclideanSpace, binaryLabels_card]]
    norm_num
  have hconn : IsPreconnected S := isPreconnected_sphere hrank 0 1
  have hcont : Continuous f := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous fun v : E => quaternionBinarySign (i+j) j * v (i+j)
    exact continuous_const.mul (PiLp.proj (𝕜 := ℝ) 2 (fun _ : BinaryLabels => ℝ) (i+j)).continuous
  have hsq (v : E) (hv : v ∈ S) : f v ^ 2 = 1 := by
    have hn : ‖v‖ = 1 := by
      change dist v 0 = 1 at hv
      rwa [dist_eq_norm, sub_zero] at hv
    have hg := quaternionBinary_gram (fun k => v k)
    rw [← hnorm v, hn, one_pow, one_smul] at hg
    have hd := congrArg Matrix.det hg
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two, f] using hd
  let e : E := fun k => if k=0 then 1 else 0
  have he : e ∈ S := by
    have hn : ‖e‖^2 = 1 := by rw [hnorm e]; simp [e, ite_pow]
    have h : ‖e‖ = 1 := by nlinarith [norm_nonneg e]
    change dist _ 0 = 1
    rw [dist_eq_norm, sub_zero]
    exact h
  have hidentity : quaternionBinaryReal (fun k => e k) = 1 := by
    ext i j
    by_cases h : i=j
    · subst j
      simp only [quaternionBinaryReal, Matrix.of_apply, binaryLabels_exponentTwo, e, if_true,
        mul_one, Matrix.one_apply_eq]
      unfold quaternionBinarySign
      change (if (0 : ZMod 2)*i.1+0*i.1+0*i.2=0 then (1 : ℝ) else -1) = 1
      simp
    · have hne : i+j ≠ 0 := fun hz => h (add_right_cancel (hz.trans (binaryLabels_exponentTwo j).symm))
      simp [quaternionBinaryReal, e, hne, Matrix.one_apply_ne h]
  have h1 : (1 : ℝ) ∈ f '' S := ⟨e, he, by simp [f, hidentity]⟩
  let v : E := q
  have hv : v ∈ S := by
    have hn : ‖v‖^2 = 1 := (hnorm v).trans hq
    have h : ‖v‖ = 1 := by nlinarith [norm_nonneg v]
    change dist _ 0 = 1
    rw [dist_eq_norm, sub_zero]
    exact h
  have hsqv := hsq v hv
  change f v = 1
  apply Classical.byContradiction
  intro h
  have hm : f v = -1 := by
    have hh : (f v - 1)*(f v + 1)=0 := by nlinarith only [hsqv]
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr h))
  have hminus : (-1 : ℝ) ∈ f '' S := ⟨v, hv, hm⟩
  have h0 : (0 : ℝ) ∈ f '' S :=
    (hconn.image f hcont.continuousOn).Icc_subset hminus h1 (by norm_num)
  obtain ⟨w, hw, hw0⟩ := h0
  have hw1 := hsq w hw
  rw [hw0] at hw1
  norm_num at hw1

/-- The determinant normalization also holds after real-to-complex cast. -/
theorem quaternionBinary_det (q : BinaryLabels → ℝ) (hq : ∑ k, q k^2 = 1) :
    (signedKleinMixerTable quaternionBinarySign q).det = 1 := by
  change (Complex.ofRealHom.mapMatrix (quaternionBinaryReal q)).det = 1
  rw [← Complex.ofRealHom.map_det, quaternionBinary_det_real q hq, map_one]

/-- Near-balanced, scalar-normalized quaternion mixers satisfy the
actual MOC conclusion for all complex spectra. -/
theorem holds_normalized_nearBalanced_quaternionBinary
    (a b : BinaryLabels → ℂ) (u : BinaryLabels) {x t : ℝ}
    (hx : 0 < x) (ht : 0 < t) (ht' : t ≤ 1) (h : 0 ≤ t^3+3*t-2)
    (hnorm : ∑ l : BinaryLabels, (x * if l = u then t else 1)^2 = 1) :
    Holds a b (signedKleinMixerTable quaternionBinarySign
      (fun l => x * if l = u then t else 1)) :=
  holds_nearBalanced_quaternionBinary a b u hx ht ht' h
    (quaternionBinary_isUnitary _ hnorm) (quaternionBinary_det _ hnorm)


/-- An explicit shape parameter defines the unitary mixer; there are
no structural hypotheses on this matrix or on the two spectra. -/
theorem holds_explicit_nearBalanced_quaternionBinary
    (a b : BinaryLabels → ℂ) (u : BinaryLabels) {t : ℝ}
    (ht : 0 < t) (ht' : t ≤ 1) (h : 0 ≤ t^3+3*t-2) :
    Holds a b (signedKleinMixerTable quaternionBinarySign
      (fun l => (1 / Real.sqrt (3+t^2)) * if l = u then t else 1)) := by
  classical
  let d := Real.sqrt (3+t^2)
  have hd : 0 < d := Real.sqrt_pos.2 (by positivity)
  have hd2 : d^2 = 3+t^2 := Real.sq_sqrt (by positivity)
  let x : ℝ := 1/d
  have hx : 0 < x := one_div_pos.mpr hd
  apply holds_normalized_nearBalanced_quaternionBinary a b u hx ht ht' h
  have hC : ((univ : Finset BinaryLabels).erase u).card = 3 := by
    rw [card_erase_of_mem (mem_univ u), card_univ, binaryLabels_card]
  let f (l : BinaryLabels) : ℝ := (x * if l = u then t else 1)^2
  change ∑ l, f l = 1
  rw [← Finset.add_sum_erase univ f (mem_univ u)]
  have hsum : (∑ l ∈ univ.erase u, f l) = 3*x^2 := by
    calc
      _ = ∑ _l ∈ (univ : Finset BinaryLabels).erase u, x^2 := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [f, (mem_erase.mp hj).1]
      _ = _ := by simp [hC, nsmul_eq_mul]
  rw [hsum, show f u = (x*t)^2 by simp [f]]
  dsimp [x]
  field_simp
  nlinarith only [hd2]

end

end MOC.QuaternionIntrinsic
