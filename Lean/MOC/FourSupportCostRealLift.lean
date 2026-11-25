import MOC.FourMatchingLift
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The rank-two moment equations for a real order-four matching profile. -/

open BigOperators Matrix

namespace MOC

/-- Coordinates `(a,b,c)` of the symmetric matrix with rows `(a,b)` and `(b,c)`. -/
def binaryMomentPSD (m : Fin 3 → ℝ) : Prop :=
  0 ≤ m 0 ∧ 0 ≤ m 2 ∧ (m 1) ^ 2 ≤ m 0 * m 2

def binaryMomentDet (m : Fin 3 → ℝ) : ℝ :=
  m 0 * m 2 - (m 1) ^ 2

def binaryMomentTrace (m : Fin 3 → ℝ) : ℝ :=
  m 0 + m 2

theorem binaryMomentPSD_iff_det_trace (m : Fin 3 → ℝ) :
    binaryMomentPSD m ↔ 0 ≤ binaryMomentDet m ∧ 0 ≤ binaryMomentTrace m := by
  change (0 ≤ m 0 ∧ 0 ≤ m 2 ∧ (m 1) ^ 2 ≤ m 0 * m 2) ↔
    0 ≤ m 0 * m 2 - (m 1) ^ 2 ∧ 0 ≤ m 0 + m 2
  constructor
  · rintro ⟨ha, hc, h⟩
    exact ⟨sub_nonneg.mpr h, add_nonneg ha hc⟩
  · rintro ⟨hdet, htr⟩
    have hp : 0 ≤ m 0 * m 2 := (sq_nonneg (m 1)).trans (sub_nonneg.mp hdet)
    have ha : 0 ≤ m 0 := by
      by_contra h
      have hneg : m 0 < 0 := lt_of_not_ge h
      have hpos : 0 < m 2 := by linarith
      exact (not_lt_of_ge hp) (mul_neg_of_neg_of_pos hneg hpos)
    have hc : 0 ≤ m 2 := by
      by_contra h
      have hneg : m 2 < 0 := lt_of_not_ge h
      have hpos : 0 < m 0 := by linarith
      exact (not_lt_of_ge hp) (mul_neg_of_pos_of_neg hpos hneg)
    exact ⟨ha, hc, sub_nonneg.mp hdet⟩

/-- The three columns are the two pure gradient values and the polarization term. -/
noncomputable def fourMatchingMomentEvaluation (x y : Fin 14 → ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 14 → ℝ) where
  toFun m i := m 0 * fourMatchingGradient x i +
    m 1 * (fourMatchingGradient (fun j => x j + y j) i -
      fourMatchingGradient x i - fourMatchingGradient y i) +
    m 2 * fourMatchingGradient y i
  map_add' a b := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' r m := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- A real Hessian of rank twelve on fourteen coordinates has a two-vector kernel basis. -/
noncomputable def fourMatchingKernelBasis (f : Fin 14 → ℝ)
    (hrank : Module.finrank ℝ (LinearMap.range (fourMatchingHessian f).mulVecLin) = 12) :
    Basis (Fin 2) ℝ (LinearMap.ker (fourMatchingHessian f).mulVecLin) := by
  have h := (fourMatchingHessian f).mulVecLin.finrank_range_add_finrank_ker
  rw [hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  exact Module.finBasisOfFinrankEq ℝ _ (by omega)

private theorem fourMatchingKernelBasis_spans (f : Fin 14 → ℝ)
    (K : Basis (Fin 2) ℝ (LinearMap.ker (fourMatchingHessian f).mulVecLin))
    (g : Fin 14 → ℝ) (hg : (fourMatchingHessian f).mulVec g = 0) :
    ∃ s t : ℝ, g = fun i => s * (K 0 : Fin 14 → ℝ) i + t * (K 1 : Fin 14 → ℝ) i := by
  let v : LinearMap.ker (fourMatchingHessian f).mulVecLin := ⟨g, LinearMap.mem_ker.mpr hg⟩
  have he := K.sum_repr v
  rw [Fin.sum_univ_two] at he
  refine ⟨K.repr v 0, K.repr v 1, funext fun i => ?_⟩
  have h := congrArg (fun z : LinearMap.ker (fourMatchingHessian f).mulVecLin =>
    (z : Fin 14 → ℝ) i) he
  change K.repr v 0 * (K 0 : Fin 14 → ℝ) i +
    K.repr v 1 * (K 1 : Fin 14 → ℝ) i = g i at h
  exact h.symm

private theorem moment_nonzero_coordinate {d : Fin 3 → ℝ} (hd : d ≠ 0) :
    d 0 ≠ 0 ∨ d 1 ≠ 0 ∨ d 2 ≠ 0 := by
  by_contra! h
  apply hd
  funext j
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- On a two-dimensional Hessian kernel, a moment map of rank at most two has an exact
positive semidefinite feasibility test for the complex critical lift. -/
theorem fourMatchingCriticalLift_iff_psd_moment (f : Fin 14 → ℝ)
    (K : Basis (Fin 2) ℝ (LinearMap.ker (fourMatchingHessian f).mulVecLin))
    (hrank : Module.finrank ℝ (LinearMap.range
      (fourMatchingMomentEvaluation (K 0) (K 1))) ≤ 2) :
    (∃ g : Fin 14 → ℝ, ∀ i, fourMatchingGradient (fun j => (⟨f j, g j⟩ : ℂ)) i = 0) ↔
      ∃ m : Fin 3 → ℝ, fourMatchingMomentEvaluation (K 0) (K 1) m =
        fourMatchingGradient f ∧ binaryMomentPSD m := by
  let x : Fin 14 → ℝ := K 0
  let y : Fin 14 → ℝ := K 1
  let L := fourMatchingMomentEvaluation x y
  have hL : Module.finrank ℝ (LinearMap.range L) ≤ 2 := hrank
  have hr := L.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr
  have hk : 0 < Module.finrank ℝ (LinearMap.ker L) := by omega
  obtain ⟨d, hdn⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hk
  have hd : (d : Fin 3 → ℝ) ≠ 0 := fun h => hdn (Subtype.ext h)
  have hnull := LinearMap.mem_ker.mp d.property
  have hx : (fourMatchingHessian f).mulVec x = 0 := LinearMap.mem_ker.mp (K 0).property
  have hy : (fourMatchingHessian f).mulVec y = 0 := LinearMap.mem_ker.mp (K 1).property
  have he := fourMatchingGradient_binary_psd_iff f x y hx hy
    (fourMatchingKernelBasis_spans f K) (d.val 0) (d.val 1) (d.val 2)
    (moment_nonzero_coordinate hd) (fun i => congrFun hnull i)
  constructor
  · intro h
    obtain ⟨a, b, c, ha, hc, hdet, hG⟩ := he.mp h
    exact ⟨![a,b,c], funext fun i => (hG i).symm, ⟨ha, hc, hdet⟩⟩
  · rintro ⟨m, hm, ha, hc, hdet⟩
    exact he.mpr ⟨m 0, m 1, m 2, ha, hc, hdet, fun i => (congrFun hm i).symm⟩

private theorem moment_solution_line_of_rank_two
    (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 14 → ℝ))
    (hrank : Module.finrank ℝ (LinearMap.range L) = 2) (m₀ : Fin 3 → ℝ) :
    ∃ d : Fin 3 → ℝ, d ≠ 0 ∧ L d = 0 ∧
      ∀ m, L m = L m₀ ↔ ∃ t : ℝ, m = m₀ + t • d := by
  have hr := L.finrank_range_add_finrank_ker
  rw [hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr
  let K := Module.finBasisOfFinrankEq ℝ (LinearMap.ker L) (n := 1) (by omega)
  let d : Fin 3 → ℝ := K 0
  have hd : d ≠ 0 := by
    intro h
    exact LinearIndependent.ne_zero 0 K.linearIndependent (Subtype.ext h)
  refine ⟨d, hd, LinearMap.mem_ker.mp (K 0).property, fun m => ?_⟩
  constructor
  · intro hm
    have hdiff : L (m - m₀) = 0 := by rw [map_sub, hm, sub_self]
    let v : LinearMap.ker L := ⟨m - m₀, LinearMap.mem_ker.mpr hdiff⟩
    have he := K.sum_repr v
    rw [Fin.sum_univ_one] at he
    have hV : K.repr v 0 • d = m - m₀ :=
      congrArg (fun z : LinearMap.ker L => (z : Fin 3 → ℝ)) he
    refine ⟨K.repr v 0, ?_⟩
    rw [hV, add_comm, sub_add_cancel]
  · rintro ⟨t, rfl⟩
    have hd0 : L d = 0 := LinearMap.mem_ker.mp (K 0).property
    rw [map_add, map_smul, hd0, smul_zero, add_zero]

/-- On the rank-twelve Hessian and rank-two moment chart, any compatible moment gives
a nonconstant affine solution line. A complex critical lift exists exactly when the
line intersects the positive semidefinite cone. -/
theorem fourMatchingCriticalLift_iff_psd_line (f : Fin 14 → ℝ)
    (K : Basis (Fin 2) ℝ (LinearMap.ker (fourMatchingHessian f).mulVecLin))
    (hL : Module.finrank ℝ (LinearMap.range (fourMatchingMomentEvaluation (K 0) (K 1))) = 2)
    (m₀ : Fin 3 → ℝ)
    (hbase : fourMatchingMomentEvaluation (K 0) (K 1) m₀ = fourMatchingGradient f) :
    let L := fourMatchingMomentEvaluation (K 0) (K 1)
    ∃ d : Fin 3 → ℝ, d ≠ 0 ∧ L d = 0 ∧
      (∀ m, L m = fourMatchingGradient f ↔ ∃ t : ℝ, m = m₀ + t • d) ∧
      ((∃ g : Fin 14 → ℝ, ∀ i, fourMatchingGradient (fun j => (⟨f j, g j⟩ : ℂ)) i = 0) ↔
        ∃ t : ℝ, binaryMomentPSD (m₀ + t • d)) := by
  let L := fourMatchingMomentEvaluation (K 0) (K 1)
  obtain ⟨d, hd, hker, he⟩ := moment_solution_line_of_rank_two L hL m₀
  have hline (m : Fin 3 → ℝ) : L m = fourMatchingGradient f ↔
      ∃ t : ℝ, m = m₀ + t • d := by
    rw [← hbase]
    exact he m
  refine ⟨d, hd, hker, hline, ?_⟩
  refine (fourMatchingCriticalLift_iff_psd_moment f K hL.le).trans ?_
  constructor
  · rintro ⟨m, hm, hp⟩
    obtain ⟨t, rfl⟩ := (hline m).mp hm
    exact ⟨t, hp⟩
  · rintro ⟨t, ht⟩
    exact ⟨m₀ + t • d, (hline (m₀ + t • d)).mpr ⟨t, rfl⟩, ht⟩

/-- The coefficient of degree one in the determinant along a line of symmetric matrices. -/
def binaryMomentDetLinear (A W : Fin 3 → ℝ) : ℝ :=
  A 0 * W 2 + W 0 * A 2 - 2 * A 1 * W 1

theorem binaryMomentDet_affine (A W : Fin 3 → ℝ) (t : ℝ) :
    binaryMomentDet (A + t • W) =
      binaryMomentDet A + t * binaryMomentDetLinear A W + t ^ 2 * binaryMomentDet W := by
  simp only [binaryMomentDet, binaryMomentDetLinear, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem binaryMomentTrace_affine (A W : Fin 3 → ℝ) (t : ℝ) :
    binaryMomentTrace (A + t • W) = binaryMomentTrace A + t * binaryMomentTrace W := by
  simp only [binaryMomentTrace, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem binaryMomentDet_nonpos_of_trace_zero {A : Fin 3 → ℝ}
    (h : binaryMomentTrace A = 0) : binaryMomentDet A ≤ 0 := by
  change A 0 + A 2 = 0 at h
  have h₂ : A 2 = -A 0 := by linarith
  simp only [binaryMomentDet, h₂]
  nlinarith only [sq_nonneg (A 0), sq_nonneg (A 1)]

private theorem binaryMoment_eq_zero_of_det_ge_trace_eq_zero {A : Fin 3 → ℝ}
    (hd : 0 ≤ binaryMomentDet A) (ht : binaryMomentTrace A = 0) : A = 0 := by
  obtain ⟨h₀, h₂, h₁⟩ := (binaryMomentPSD_iff_det_trace A).mpr ⟨hd, ht.ge⟩
  change A 0 + A 2 = 0 at ht
  have h₀' : A 0 = 0 := by linarith only [h₀, h₂, ht]
  have h₂' : A 2 = 0 := by linarith only [h₀, h₂, ht]
  have h₁' : A 1 = 0 := by
    rw [h₀', zero_mul] at h₁
    exact sq_eq_zero_iff.mp (le_antisymm h₁ (sq_nonneg (A 1)))
  funext j
  fin_cases j
  · exact h₀'
  · exact h₁'
  · exact h₂'

private theorem binaryMomentDetLinear_shift (A W : Fin 3 → ℝ) (t : ℝ) :
    binaryMomentDetLinear (A + t • W) W =
      binaryMomentDetLinear A W + 2 * t * binaryMomentDet W := by
  simp only [binaryMomentDetLinear, binaryMomentDet, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A line with indefinite direction meets the positive semidefinite cone exactly
when its maximum-determinant midpoint is positive semidefinite. -/
theorem binaryCenteredMomentLine_psd_iff (A W : Fin 3 → ℝ)
    (hcenter : binaryMomentDetLinear A W = 0) (hW : binaryMomentDet W < 0) :
    (∃ t : ℝ, binaryMomentPSD (A + t • W)) ↔ binaryMomentPSD A := by
  constructor
  · rintro ⟨t, ht⟩
    let D := binaryMomentDet A
    let E := binaryMomentDet W
    have hdcurve (r : ℝ) : binaryMomentDet (A + r • W) = D + r ^ 2 * E := by
      rw [binaryMomentDet_affine, hcenter, mul_zero, add_zero]
    have htd := ((binaryMomentPSD_iff_det_trace _).mp ht).1
    have htt := ((binaryMomentPSD_iff_det_trace _).mp ht).2
    have hD : 0 ≤ D := by
      have hneg : t ^ 2 * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hW.le
      rw [hdcurve] at htd
      linarith only [htd, hneg]
    refine (binaryMomentPSD_iff_det_trace A).mpr ⟨hD, ?_⟩
    by_contra hA
    have hAneg : binaryMomentTrace A < 0 := lt_of_not_ge hA
    by_cases htt0 : binaryMomentTrace (A + t • W) = 0
    · have hzero := binaryMoment_eq_zero_of_det_ge_trace_eq_zero htd htt0
      have he := binaryMomentDetLinear_shift A W t
      rw [hzero, hcenter] at he
      have hzeroLin : binaryMomentDetLinear 0 W = 0 := by
        simp only [binaryMomentDetLinear, Pi.zero_apply, zero_mul, mul_zero,
          add_zero, sub_self]
      rw [hzeroLin, zero_add] at he
      have hte : 2 * t * binaryMomentDet W = 0 := he.symm
      have htz : t = 0 := by
        rcases mul_eq_zero.mp hte with ht' | h'
        · exact (mul_eq_zero.mp ht').resolve_left (by norm_num)
        · exact False.elim (hW.ne h')
      exact hA (by simpa only [htz, zero_smul, add_zero] using htt)
    · have httpos : 0 < binaryMomentTrace (A + t • W) := lt_of_le_of_ne htt
        (fun h => htt0 h.symm)
      let T := binaryMomentTrace A
      let U := binaryMomentTrace (A + t • W)
      let r := -T / (U - T)
      have hden : 0 < U - T := sub_pos.mpr (hAneg.trans httpos)
      have hr0 : 0 < r := div_pos (neg_pos.mpr hAneg) hden
      have hr1 : r < 1 := (div_lt_one hden).mpr (by
        change -T < U - T
        dsimp only [T, U]
        linarith only [httpos])
      have hrden : r * (U - T) = -T := div_mul_cancel₀ _ hden.ne'
      have hbal : U - T = t * binaryMomentTrace W := by
        change binaryMomentTrace (A + t • W) - binaryMomentTrace A = _
        rw [binaryMomentTrace_affine, add_sub_cancel_left]
      have htrzero : binaryMomentTrace (A + (r * t) • W) = 0 := by
        rw [binaryMomentTrace_affine, mul_assoc, ← hbal, hrden]
        exact add_neg_cancel T
      have ht0 : t ≠ 0 := by
        intro hz
        apply hA
        simpa only [hz, zero_smul, add_zero] using htt
      rw [hdcurve] at htd
      have hEt : t ^ 2 * E < 0 := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ht0) hW
      have hDpos : 0 < D := by linarith only [htd, hEt]
      have hrsq : r ^ 2 < 1 := by
        have h := mul_pos (sub_pos.mpr hr1) (by linarith only [hr0] : 0 < 1 + r)
        nlinarith only [h]
      have hdpos : 0 < binaryMomentDet (A + (r * t) • W) := by
        rw [hdcurve, show D + (r * t) ^ 2 * E =
          (1 - r ^ 2) * D + r ^ 2 * (D + t ^ 2 * E) by ring]
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hrsq) hDpos)
          (mul_nonneg (sq_nonneg r) htd)
      exact (not_lt_of_ge (binaryMomentDet_nonpos_of_trace_zero htrzero)) hdpos
  · exact fun h => ⟨0, by simpa only [zero_smul, add_zero] using h⟩

/-- The midpoint test applies to every indefinite direction, including
zero discriminant. -/
theorem binaryMomentLine_psd_iff_midpoint (A W : Fin 3 → ℝ)
    (hW : binaryMomentDet W < 0) :
    (∃ t : ℝ, binaryMomentPSD (A + t • W)) ↔
      binaryMomentPSD (A + (-binaryMomentDetLinear A W / (2 * binaryMomentDet W)) • W) := by
  let r := -binaryMomentDetLinear A W / (2 * binaryMomentDet W)
  let B := A + r • W
  have hden : 2 * binaryMomentDet W ≠ 0 := mul_ne_zero (by norm_num) hW.ne
  have hr : r * (2 * binaryMomentDet W) = -binaryMomentDetLinear A W :=
    div_mul_cancel₀ _ hden
  have hcenter : binaryMomentDetLinear B W = 0 := by
    change binaryMomentDetLinear (A + r • W) W = 0
    rw [binaryMomentDetLinear_shift]
    rw [show 2 * r * binaryMomentDet W = r * (2 * binaryMomentDet W) by ring, hr, add_neg_cancel]
  have hline : (∃ t : ℝ, binaryMomentPSD (A + t • W)) ↔
      ∃ t : ℝ, binaryMomentPSD (B + t • W) := by
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t - r, ?_⟩
      change binaryMomentPSD (A + r • W + (t - r) • W)
      rw [add_assoc, ← add_smul, show r + (t - r) = t by ring]
      exact ht
    · rintro ⟨t, ht⟩
      refine ⟨r + t, ?_⟩
      rw [add_smul, ← add_assoc]
      exact ht
  exact hline.trans (binaryCenteredMomentLine_psd_iff B W hcenter hW)

/-- The determinant at the center is minus the discriminant divided by four
times the determinant of the direction. -/
theorem binaryMomentDet_midpoint (A W : Fin 3 → ℝ) (hW : binaryMomentDet W ≠ 0) :
    binaryMomentDet (A + (-binaryMomentDetLinear A W / (2 * binaryMomentDet W)) • W) =
      -((binaryMomentDetLinear A W) ^ 2 - 4 * binaryMomentDet W * binaryMomentDet A) /
        (4 * binaryMomentDet W) := by
  rw [binaryMomentDet_affine]
  field_simp [hW]
  <;> ring

/-- A positive semidefinite solve on a nonconstant line can be chosen singular. -/
theorem binaryMomentLine_psd_iff_singular (A W : Fin 3 → ℝ) (hW : W ≠ 0) :
    (∃ t : ℝ, binaryMomentPSD (A + t • W)) ↔
      ∃ t : ℝ, binaryMomentDet (A + t • W) = 0 ∧ 0 ≤ binaryMomentTrace (A + t • W) := by
  constructor
  · rintro ⟨t, ha, hc, hdet⟩
    obtain ⟨s, hs₀, hs₂, hsdet⟩ := binary_psd_line_hits_singular
      ((A + t • W) 0) ((A + t • W) 1) ((A + t • W) 2) (W 0) (W 1) (W 2)
      ha hc hdet (moment_nonzero_coordinate hW)
    refine ⟨t + s, ?_, ?_⟩
    · rw [add_smul, ← add_assoc]
      change ((A + t • W) 0 + s * W 0) * ((A + t • W) 2 + s * W 2) -
        ((A + t • W) 1 + s * W 1) ^ 2 = 0
      rw [hsdet, sub_self]
    · rw [add_smul, ← add_assoc]
      exact add_nonneg hs₀ hs₂
  · rintro ⟨t, hd, ht⟩
    exact ⟨t, (binaryMomentPSD_iff_det_trace (A + t • W)).mpr ⟨hd.ge, ht⟩⟩

/-- A singular direction with nonzero linear determinant coefficient has one
singular candidate. Its trace gives the feasibility test. -/
theorem binaryMomentLine_psd_iff_linear_root (A W : Fin 3 → ℝ)
    (hW : binaryMomentDet W = 0) (hb : binaryMomentDetLinear A W ≠ 0) :
    (∃ t : ℝ, binaryMomentPSD (A + t • W)) ↔
      0 ≤ binaryMomentTrace (A + (-binaryMomentDet A / binaryMomentDetLinear A W) • W) := by
  have hne : W ≠ 0 := by
    intro he
    apply hb
    rw [he]
    simp only [binaryMomentDetLinear, Pi.zero_apply, mul_zero, zero_mul, add_zero, sub_self]
  rw [binaryMomentLine_psd_iff_singular A W hne]
  constructor
  · rintro ⟨t, hd, ht⟩
    rw [binaryMomentDet_affine, hW, mul_zero, add_zero] at hd
    have he : t = -binaryMomentDet A / binaryMomentDetLinear A W := by
      apply (eq_div_iff hb).mpr
      linarith only [hd]
    simpa only [he] using ht
  · intro ht
    refine ⟨_, ?_, ht⟩
    rw [binaryMomentDet_affine, hW, mul_zero, add_zero, div_mul_cancel₀ _ hb, add_neg_cancel]

/-- A nonconstant line with constant determinant meets the cone exactly when
the constant is zero. -/
theorem binaryMomentLine_psd_iff_constant_det (A W : Fin 3 → ℝ)
    (hW : binaryMomentDet W = 0) (hne : W ≠ 0) (hb : binaryMomentDetLinear A W = 0) :
    (∃ t : ℝ, binaryMomentPSD (A + t • W)) ↔ binaryMomentDet A = 0 := by
  rw [binaryMomentLine_psd_iff_singular A W hne]
  constructor
  · rintro ⟨t, hd, _⟩
    simpa only [binaryMomentDet_affine, hW, hb, mul_zero, add_zero] using hd
  · intro hd
    have ht : binaryMomentTrace W ≠ 0 := fun h =>
      hne (binaryMoment_eq_zero_of_det_ge_trace_eq_zero hW.ge h)
    refine ⟨-binaryMomentTrace A / binaryMomentTrace W, ?_, ?_⟩
    · simp only [binaryMomentDet_affine, hW, hb, hd, mul_zero, add_zero]
    · rw [binaryMomentTrace_affine, div_mul_cancel₀ _ ht, add_neg_cancel]

private theorem binaryMomentLine_psd_of_positive_direction (A W : Fin 3 → ℝ)
    (hD : 0 < binaryMomentDet W) (hT : 0 < binaryMomentTrace W) :
    ∃ t : ℝ, binaryMomentPSD (A + t • W) := by
  let b := binaryMomentDetLinear A W
  let c := binaryMomentDet A
  let u := (|b| + |c| + 1) / binaryMomentDet W
  let v := (|binaryMomentTrace A| + 1) / binaryMomentTrace W
  let t := 1 + u + v
  have hu : 0 ≤ u := div_nonneg (add_nonneg (add_nonneg (abs_nonneg b) (abs_nonneg c))
    zero_le_one) hD.le
  have hv : 0 ≤ v := div_nonneg (add_nonneg (abs_nonneg _) zero_le_one) hT.le
  have htu : u ≤ t := by change u ≤ 1 + u + v; linarith only [hv]
  have htv : v ≤ t := by change v ≤ 1 + u + v; linarith only [hu]
  have ht : 1 ≤ t := by change 1 ≤ 1 + u + v; linarith only [hu, hv]
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hdet := mul_le_mul_of_nonneg_right htu hD.le
  have htrace := mul_le_mul_of_nonneg_right htv hT.le
  change (|b| + |c| + 1) / binaryMomentDet W * binaryMomentDet W ≤ _ at hdet
  change (|binaryMomentTrace A| + 1) / binaryMomentTrace W * binaryMomentTrace W ≤ _ at htrace
  rw [div_mul_cancel₀ _ hD.ne'] at hdet
  rw [div_mul_cancel₀ _ hT.ne'] at htrace
  refine ⟨t, (binaryMomentPSD_iff_det_trace _).mpr ⟨?_, ?_⟩⟩
  · rw [binaryMomentDet_affine]
    change 0 ≤ c + t * b + t ^ 2 * binaryMomentDet W
    have hlarge := mul_le_mul_of_nonneg_left hdet ht0
    have hlin := mul_le_mul_of_nonneg_left (neg_abs_le b) ht0
    have hconst := mul_le_mul_of_nonneg_right ht (abs_nonneg c)
    nlinarith only [hlarge, hlin, hconst, ht0, neg_abs_le c]
  · rw [binaryMomentTrace_affine]
    linarith only [htrace, neg_abs_le (binaryMomentTrace A)]

/-- A line with definite direction always contains a positive semidefinite moment. -/
theorem binaryMomentLine_psd_of_pos_det (A W : Fin 3 → ℝ) (hW : 0 < binaryMomentDet W) :
    ∃ t : ℝ, binaryMomentPSD (A + t • W) := by
  have hne : binaryMomentTrace W ≠ 0 := by
    intro h
    exact (not_lt_of_ge (binaryMomentDet_nonpos_of_trace_zero h)) hW
  rcases lt_or_gt_of_ne hne with hT | hT
  · have hdet : binaryMomentDet (-W) = binaryMomentDet W := by
      simp only [binaryMomentDet, Pi.neg_apply]
      ring
    have htr : binaryMomentTrace (-W) = -binaryMomentTrace W := by
      simp only [binaryMomentTrace, Pi.neg_apply]
      ring
    obtain ⟨t, ht⟩ := binaryMomentLine_psd_of_positive_direction A (-W)
      (hdet.symm ▸ hW) (by rw [htr]; exact neg_pos.mpr hT)
    exact ⟨-t, by simpa only [smul_neg, neg_smul] using ht⟩
  · exact binaryMomentLine_psd_of_positive_direction A W hW hT

/-- A bracket profile of eight nonzero two-coordinate vectors is a common
nonzero multiple of the matching profile of two finite complex spectra. -/
theorem fourBracketCoordinates_exists_finite_spectra (p q : Fin 8 → ℂ)
    (hn : ∀ i, p i ≠ 0 ∨ q i ≠ 0) :
    ∃ (a b : Fin 4 → ℂ) (η : ℂ), η ≠ 0 ∧
      fourBracketCoordinates (fun i j => p i * q j - p j * q i) =
        fun k => η * fourNoncrossingCoordinates (fourSpectralPoints a b) k := by
  classical
  letI : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  let bad := Finset.univ.image (fun i : Fin 8 => -q i / p i)
  obtain ⟨t, ht⟩ := Infinite.exists_not_mem_finset bad
  let h (i : Fin 8) := q i + t * p i
  have hh (i : Fin 8) : h i ≠ 0 := by
    intro hz
    change q i + t * p i = 0 at hz
    by_cases hp : p i = 0
    · exact ((hn i).resolve_left (fun hne => hne hp))
        (by simpa only [hp, mul_zero, add_zero] using hz)
    · have he : t = -q i / p i := (eq_div_iff hp).mpr (by linear_combination hz)
      exact ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he.symm⟩)
  let z (i : Fin 8) := p i / h i
  have hz (i : Fin 8) : z i * h i = p i := div_mul_cancel₀ _ (hh i)
  let a (i : Fin 4) := z (Fin.castAdd 4 i)
  let b (i : Fin 4) := -z (Fin.natAdd 4 i)
  have hlegs : fourSpectralPoints a b = z := by
    funext i
    fin_cases i <;> simp [fourSpectralPoints, a, b] <;> rfl
  refine ⟨a, b, ∏ i, h i, Finset.prod_ne_zero_iff.mpr (fun i _ => hh i), ?_⟩
  rw [hlegs]
  have hbracket (i j : Fin 8) : p i * q j - p j * q i =
      (z i - z j) * (h i * h j) := by
    calc
      _ = p i * h j - p j * h i := by dsimp only [h]; ring
      _ = _ := by rw [← hz i, ← hz j]; ring
  funext k
  fin_cases k <;>
    simp [fourNoncrossingCoordinates, fourBracketCoordinates, hbracket, Fin.prod_univ_succ] <;>
    ring

private theorem fourMatchingMomentEvaluation_of_kernel (f g : Fin 14 → ℝ)
    (K : Basis (Fin 2) ℝ (LinearMap.ker (fourMatchingHessian f).mulVecLin))
    (hg : (fourMatchingHessian f).mulVec g = 0) :
    ∃ m : Fin 3 → ℝ, fourMatchingMomentEvaluation (K 0) (K 1) m = fourMatchingGradient g := by
  obtain ⟨s, t, rfl⟩ := fourMatchingKernelBasis_spans f K g hg
  let x : Fin 14 → ℝ := K 0
  let y : Fin 14 → ℝ := K 1
  refine ⟨![s ^ 2, s * t, t ^ 2], funext fun i => ?_⟩
  change s ^ 2 * fourMatchingGradient x i +
    (s * t) * (fourMatchingGradient (fun j => x j + y j) i -
      fourMatchingGradient x i - fourMatchingGradient y i) +
    t ^ 2 * fourMatchingGradient y i =
    fourMatchingGradient (fun j => s * x j + t * y j) i
  fin_cases i <;> simp [fourMatchingGradient] <;> ring

/-- The real midpoint of complex critical profiles with opposite imaginary
parts has a compatible real moment target on any two-vector Hessian kernel
basis. Compatibility does not require a rank assumption on the moment map. -/
set_option maxHeartbeats 1500000 in
theorem fourMatchingSecant_real_moment_compatible (u v y : Fin 14 → ℝ)
    (hu : ∀ i, fourMatchingGradient (fun j => (⟨u j, y j⟩ : ℂ)) i = 0)
    (hv : ∀ i, fourMatchingGradient (fun j => (⟨v j, -y j⟩ : ℂ)) i = 0) :
    let f (j : Fin 14) := (u j + v j) / 2
    ∀ K : Basis (Fin 2) ℝ (LinearMap.ker (fourMatchingHessian f).mulVecLin),
      ∃ m : Fin 3 → ℝ, fourMatchingMomentEvaluation (K 0) (K 1) m =
        fourMatchingGradient f := by
  dsimp only
  intro K
  let f (j : Fin 14) := (u j + v j) / 2
  let z (j : Fin 14) := (u j - v j) / 2
  obtain ⟨hYu, hGu⟩ := (fourMatchingGradient_lift_iff u y).mp hu
  obtain ⟨hYv, hGv⟩ := (fourMatchingGradient_lift_iff v (fun j => -y j)).mp hv
  change (fourMatchingHessian v).mulVec (-y) = 0 at hYv
  rw [Matrix.mulVec_neg, neg_eq_zero] at hYv
  have hGv' : fourMatchingGradient v = fourMatchingGradient y := by
    funext i
    rw [hGv]
    simpa only [neg_one_mul, neg_one_sq, one_mul] using
      fourMatchingGradient_scale y (-1 : ℝ) i
  have hy : (fourMatchingHessian f).mulVec y = 0 := by
    funext i
    have h : (fourMatchingHessian f).mulVec y i =
        ((fourMatchingHessian u).mulVec y i + (fourMatchingHessian v).mulVec y i) / 2 := by
      simp only [fourMatchingHessian_mulVec_apply]
      fin_cases i <;> simp [f, fourMatchingGradient] <;> ring
    rw [h, hYu, hYv]
    simp only [Pi.zero_apply, add_zero, zero_div]
  have hz : (fourMatchingHessian f).mulVec z = 0 := by
    funext i
    have h : (fourMatchingHessian f).mulVec z i =
        (fourMatchingGradient u i - fourMatchingGradient v i) / 2 := by
      rw [fourMatchingHessian_mulVec_apply]
      fin_cases i <;> simp [f, z, fourMatchingGradient] <;> ring
    rw [h, hGu, hGv', sub_self, zero_div] <;> rfl
  have hf : fourMatchingGradient f = fourMatchingGradient y - fourMatchingGradient z := by
    funext i
    have h : fourMatchingGradient f i + fourMatchingGradient z i =
        (fourMatchingGradient u i + fourMatchingGradient v i) / 2 := by
      fin_cases i <;> simp [f, z, fourMatchingGradient] <;> ring
    rw [hGu, hGv'] at h
    change fourMatchingGradient f i = fourMatchingGradient y i - fourMatchingGradient z i
    linarith only [h]
  obtain ⟨m, hm⟩ := fourMatchingMomentEvaluation_of_kernel f y K hy
  obtain ⟨n, hn⟩ := fourMatchingMomentEvaluation_of_kernel f z K hz
  exact ⟨m - n, by rw [map_sub, hm, hn, hf]⟩

end MOC
