import MOC.FourMatchingSegre
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Prod

/-! First-order row and column symmetries of the Segre response. -/

open Matrix TrivSqZeroExt
open scoped BigOperators

namespace MOC

variable {R : Type*} [CommRing R]

private def dualMatrix {m n : Type*} (A B : Matrix m n R) : Matrix m n (DualNumber R) :=
  fun i j => ⟨A i j, B i j⟩

private theorem dualMatrix_mul {m n k : Type*} [Fintype n]
    (A B : Matrix m n R) (C D : Matrix n k R) :
    dualMatrix A B * dualMatrix C D = dualMatrix (A * C) (A * D + B * C) := by
  ext i j : 1
  apply TrivSqZeroExt.ext
  · simp only [dualMatrix, Matrix.mul_apply, fst_sum, fst_mul, fst_mk]
  · simp only [dualMatrix, Matrix.mul_apply, Matrix.add_apply, snd_sum, DualNumber.snd_mul,
      fst_mk, snd_mk, Finset.sum_add_distrib]

private theorem det_dualMatrix_one (L : Matrix (Fin 4) (Fin 4) R) :
    (dualMatrix 1 L).det = (⟨1, L.trace⟩ : DualNumber R) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  apply TrivSqZeroExt.ext <;>
    norm_num [dualMatrix, Matrix.one_apply, Matrix.trace, Fin.sum_univ_four, Fin.succAbove,
      Fin.castSucc, Fin.succ, Fin.lt_def, TrivSqZeroExt.fst_mul, DualNumber.snd_mul] <;> ring

private theorem prod_dual_one (c : Fin 8 → R) :
    (∏ i, (⟨1, c i⟩ : DualNumber R)) = (⟨1, ∑ i, c i⟩ : DualNumber R) := by
  apply TrivSqZeroExt.ext <;>
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, TrivSqZeroExt.fst_mul, DualNumber.snd_mul,
      add_comm]

/-- The first-order part of the Segre response vanishes along traceless
row directions and zero-sum column directions, even over a general ring. -/
theorem fourSegreResponse_dual_directions (X : Matrix (Fin 4) (Fin 8) R)
    (L : Matrix (Fin 4) (Fin 4) R) (c : Fin 8 → R)
    (hL : L.trace = 0) (hc : (∑ i, c i) = 0) :
    fourSegreResponse (fun i j => (⟨X i j, (L * X + X * diagonal c) i j⟩ : DualNumber R)) =
      fourSegreResponse (fun i j => (⟨X i j, 0⟩ : DualNumber R)) := by
  change fourSegreResponse (dualMatrix X (L * X + X * diagonal c)) =
    fourSegreResponse (dualMatrix X 0)
  let d (i : Fin 8) : DualNumber R := ⟨1, c i⟩
  have hd : (∏ i, d i) = 1 := by
    change (∏ i, (⟨1, c i⟩ : DualNumber R)) = 1
    rw [prod_dual_one, hc] <;> rfl
  have hdet : (dualMatrix 1 L).det = 1 := by
    rw [det_dualMatrix_one, hL] <;> rfl
  have hD : diagonal d = dualMatrix 1 (diagonal c) := by
    ext i j : 1
    by_cases hij : i = j <;> simp [d, dualMatrix, Matrix.one_apply, Matrix.diagonal_apply, hij]
  have hmul : dualMatrix 1 L * dualMatrix X 0 * diagonal d =
      dualMatrix X (L * X + X * diagonal c) := by
    rw [hD, dualMatrix_mul, dualMatrix_mul]
    simp [add_comm]
  rw [← hmul, fourSegreResponse_mul_diagonal _ _ hd, fourSegreResponse_mul_left _ _ hdet]

private theorem fourSegreResponse_snd_map {M : Type*} [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (f : M →ₗ[R] R)
    (X : Matrix (Fin 4) (Fin 8) R) (V : Matrix (Fin 4) (Fin 8) M) (i : Fin 14) :
    f ((fourSegreResponse (fun j k => (⟨X j k, V j k⟩ : TrivSqZeroExt R M)) i).snd) =
      (fourSegreResponse (dualMatrix X (V.map f)) i).snd := by
  let A : Matrix (Fin 4) (Fin 8) (TrivSqZeroExt R M) := fun j k => ⟨X j k, V j k⟩
  let F := (TrivSqZeroExt.map f).toRingHom
  have h : A.map F = dualMatrix X (V.map f) := by
    ext j k : 1
    exact TrivSqZeroExt.ext (fst_map f _) (snd_map f _)
  calc
    _ = (F (fourSegreResponse A i)).snd := (snd_map f _).symm
    _ = (fourSegreResponse (A.map F) i).snd :=
      congrArg TrivSqZeroExt.snd (fourSegreResponse_map F A i)
    _ = _ := by rw [h]

/-- The linear part of the Segre response at a fixed matrix. -/
def fourSegreResponseDifferential (X : Matrix (Fin 4) (Fin 8) R) :
    Matrix (Fin 4) (Fin 8) R →ₗ[R] (Fin 14 → R) where
  toFun V i := (fourSegreResponse (dualMatrix X V) i).snd
  map_add' V W := by
    funext i
    let A : Matrix (Fin 4) (Fin 8) (R × R) := fun j k => (V j k, W j k)
    let p := LinearMap.fst R R R
    let q := LinearMap.snd R R R
    exact (fourSegreResponse_snd_map (p + q) X A i).symm.trans
      (congrArg₂ (· + ·) (fourSegreResponse_snd_map p X A i)
        (fourSegreResponse_snd_map q X A i))
  map_smul' t V := by
    funext i
    exact (fourSegreResponse_snd_map (t • LinearMap.id) X V i).symm

/-- The linear response annihilates every traceless row direction and
zero-sum column direction. -/
theorem fourSegreResponseDifferential_directions (X : Matrix (Fin 4) (Fin 8) R)
    (L : Matrix (Fin 4) (Fin 4) R) (c : Fin 8 → R)
    (hL : L.trace = 0) (hc : (∑ i, c i) = 0) :
    fourSegreResponseDifferential X (L * X + X * diagonal c) = 0 := by
  calc
    _ = fourSegreResponseDifferential X 0 := by
      funext i
      exact congrArg (fun a : Fin 14 → DualNumber R => (a i).snd)
        (fourSegreResponse_dual_directions X L c hL hc)
    _ = _ := map_zero _

private theorem segre_directions_injective
    (X : Matrix (Fin 4) (Fin 8) ℂ) (e : Fin 4 → Fin 8) (j₀ : Fin 8) (v : Fin 4 → ℂ)
    (hP : IsUnit (X.submatrix id e)) (hv : ∀ j, v j ≠ 0)
    (hframe : (X.submatrix id e).mulVec v = fun i => X i j₀)
    (hcols : ∀ j, ∃ i, X i j ≠ 0)
    (L : Matrix (Fin 4) (Fin 4) ℂ) (c : Fin 8 → ℂ) (hL : L.trace = 0)
    (hz : L * X + X * diagonal c = 0) : L = 0 ∧ c = 0 := by
  let P := X.submatrix id e
  let D := diagonal (fun j => -c (e j))
  have hcol (j : Fin 8) : L.mulVec (fun i => X i j) = (-c j) • (fun i => X i j) := by
    funext i
    have he : (L * X + X * diagonal c) i j = 0 := congrArg (fun A => A i j) hz
    rw [Matrix.add_apply, Matrix.mul_diagonal] at he
    change (L * X) i j = (-c j) * X i j
    linear_combination he
  have heq : L * P = P * D := by
    ext i j : 1
    change (L * X) i (e j) = (P * D) i j
    rw [Matrix.mul_diagonal]
    simpa [P, mul_comm] using congrFun (hcol (e j)) i
  have hdiag : D.mulVec v = (-c j₀) • v := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr hP
    calc
      P.mulVec (D.mulVec v) = L.mulVec (P.mulVec v) := by
        simp only [Matrix.mulVec_mulVec, heq]
      _ = (-c j₀) • P.mulVec v := by rw [hframe, hcol]
      _ = P.mulVec ((-c j₀) • v) := (Matrix.mulVec_smul _ _ _).symm
  have hconstant (j : Fin 4) : -c (e j) = -c j₀ := by
    apply mul_right_cancel₀ (hv j)
    simpa only [D, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] using congrFun hdiag j
  have hD : D = (-c j₀) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    rw [Matrix.smul_one_eq_diagonal]
    exact congrArg diagonal (funext hconstant)
  have hL' : L = (-c j₀) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    apply hP.mul_right_cancel
    rw [heq, hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hzero : -c j₀ = 0 := by
    have htr : (-c j₀) * (4 : ℂ) = 0 := by
      simpa [hL', Matrix.trace_one, smul_eq_mul] using hL
    exact (mul_eq_zero.mp htr).resolve_right (by norm_num)
  have hL₀ : L = 0 := by rw [hL', hzero, zero_smul]
  refine ⟨hL₀, funext fun j => ?_⟩
  obtain ⟨i, hi⟩ := hcols j
  have he : (-c j) * X i j = 0 := by
    simpa only [hL₀, Matrix.zero_mulVec, Pi.smul_apply, smul_eq_mul] using (congrFun (hcol j) i).symm
  exact neg_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hi)

/-- Four independent columns and one column supported on all four basis
coordinates force a ten-dimensional upper bound on the differential image. -/
theorem fourSegreResponseDifferential_finrank_le_ten
    (X : Matrix (Fin 4) (Fin 8) ℂ) (e : Fin 4 → Fin 8) (j₀ : Fin 8) (v : Fin 4 → ℂ)
    (hP : IsUnit (X.submatrix id e)) (hv : ∀ j, v j ≠ 0)
    (hframe : (X.submatrix id e).mulVec v = fun i => X i j₀)
    (hcols : ∀ j, ∃ i, X i j ≠ 0) :
    Module.finrank ℂ (LinearMap.range (fourSegreResponseDifferential X)) ≤ 10 := by
  let tr := Matrix.traceLinearMap (Fin 4) ℂ ℂ
  let sm : (Fin 8 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i
  let S := LinearMap.ker tr
  let T := LinearMap.ker sm
  let F : (S × T) →ₗ[ℂ] Matrix (Fin 4) (Fin 8) ℂ :=
    { toFun := fun w => w.1.val * X + X * diagonal w.2.val
      map_add' := by
        intro a b
        simp [Matrix.add_mul, Matrix.mul_add, Matrix.diagonal_add] <;> abel
      map_smul' := by
        intro t a
        simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.diagonal_smul, smul_add] }
  have hF (w : S × T) : F w ∈ LinearMap.ker (fourSegreResponseDifferential X) := by
    apply LinearMap.mem_ker.mpr
    exact fourSegreResponseDifferential_directions X w.1.val w.2.val
      (LinearMap.mem_ker.mp w.1.property)
      (by simpa [sm, LinearMap.sum_apply] using LinearMap.mem_ker.mp w.2.property)
  let G := F.codRestrict _ hF
  have hG : Function.Injective G := by
    apply (injective_iff_map_eq_zero G).mpr
    intro w hw
    have hzero : F w = 0 := congrArg Subtype.val hw
    obtain ⟨h₁, h₂⟩ := segre_directions_injective X e j₀ v hP hv hframe hcols
      w.1.val w.2.val (LinearMap.mem_ker.mp w.1.property) hzero
    exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
  have hdim := LinearMap.finrank_le_finrank_of_injective hG
  rw [Module.finrank_prod] at hdim
  have hr₁ : Module.finrank ℂ (LinearMap.range tr) ≤ 1 := by
    simpa using (LinearMap.range tr).finrank_le
  have hr₂ : Module.finrank ℂ (LinearMap.range sm) ≤ 1 := by
    simpa using (LinearMap.range sm).finrank_le
  have hs := tr.finrank_range_add_finrank_ker
  have ht := sm.finrank_range_add_finrank_ker
  have hn := (fourSegreResponseDifferential X).finrank_range_add_finrank_ker
  simp only [Module.finrank_matrix, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Module.finrank_self] at hs ht hn
  change Module.finrank ℂ (LinearMap.ker tr) + Module.finrank ℂ (LinearMap.ker sm) ≤
    Module.finrank ℂ (LinearMap.ker (fourSegreResponseDifferential X)) at hdim
  omega

end MOC
