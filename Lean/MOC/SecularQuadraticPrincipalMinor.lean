import MOC.SecularQuadraticCalculus
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Real.Sqrt

/-! Identification of the quadratic secular moment with the
corresponding principal minor of the rank-one matrix. -/

open BigOperators Finset Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant after a diagonal shift is a product of diagonal entries
times the determinant of a two-by-two correction. -/
private theorem det_diagonal_add_rank_two_factor {K : Type*} [Field K]
    (w : ι → K) (hw : ∀ i, w i ≠ 0)
    (L : Matrix ι (Fin 2) K) (R : Matrix (Fin 2) ι K) :
    (diagonal w + L * R).det =
      (∏ i, w i) * (1 + R * diagonal (fun i => (w i)⁻¹) * L).det := by
  let X := diagonal fun i => (w i)⁻¹
  have hWX : diagonal w * X = 1 := by
    simp only [X, Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (hw _), Matrix.diagonal_one]
  calc
    _ = (diagonal w * (1 + (X * L) * R)).det := by
      rw [Matrix.mul_add, mul_one, ← Matrix.mul_assoc (diagonal w) (X * L) R,
        ← Matrix.mul_assoc (diagonal w) X L, hWX]
      simp only [Matrix.one_mul]
    _ = _ := by
      rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_one_add_mul_comm,
        ← Matrix.mul_assoc R X L]

/-- The scalar secular formula computes the principal minors of the
quadratic image of the rank-one matrix. -/
theorem det_quadratic_principal_minor_eq_secular (h d v : ι → ℝ)
    (hv : ∀ i, v i * v i = secularResidue h d i)
    (S : Finset ι) (t u : ℝ) (htu : t ≠ u)
    (ht : ∀ i, d i ≠ t) (hu : ∀ i, d i ≠ u) :
    let H := diagonal d + vecMulVec v v
    (((H - t • 1) * (H - u • 1)).submatrix (fun i : S => i.val) (fun i : S => i.val)).det =
      secularQuadraticMinor h d S t u := by
  intro H
  let r := secularResidue h d
  let q := ∑ j, r j
  let b := q-t-u
  let k (i : ι) := (d i-t)*(d i-u)
  let L : Matrix S (Fin 2) ℝ := Matrix.of fun i j => if j = 0 then d i.val * v i.val else v i.val
  let R : Matrix (Fin 2) S ℝ := Matrix.of fun j i => if j = 0 then v i.val else (d i.val+b) * v i.val
  let K : S → ℝ := fun i => k i.val
  let N := (H-t • 1)*(H-u • 1)
  have hR₂ : (vecMulVec v v : Matrix ι ι ℝ) * vecMulVec v v = q • vecMulVec v v := by
    ext i j : 1
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      q, Finset.sum_mul]
    apply sum_congr rfl
    intro e _
    dsimp only [r]
    rw [← hv e]
    ring
  have hS (z : ℝ) : H - z • 1 = diagonal (fun i => d i - z) + vecMulVec v v := by
    ext i j : 1
    by_cases he : i = j
    · subst j
      simp only [H, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_eq, Matrix.diagonal_apply_eq, mul_one]
      ring
    · simp only [H, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_ne he, Matrix.diagonal_apply_ne _ he, mul_zero, sub_zero]
  have hN : N.submatrix (fun i : S => i.val) (fun i : S => i.val) = diagonal K + L * R := by
    change ((H-t • 1)*(H-u • 1)).submatrix _ _ = _
    rw [hS t, hS u, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.diagonal_mul_diagonal, hR₂]
    ext i j : 1
    have hdiag :
        diagonal (fun a : ι => (d a-t)*(d a-u)) i.val j.val = diagonal K i j := by
      by_cases he : i = j
      · subst j; simp only [Matrix.diagonal_apply_eq, K, k]
      · have he' : i.val ≠ j.val := fun hz => he (Subtype.ext hz)
        simp only [Matrix.diagonal_apply_ne _ he', Matrix.diagonal_apply_ne _ he]
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, hdiag]
    rw [Matrix.mul_apply]
    simp [L, R, Fin.sum_univ_two, b]
    ring
  have hK (i : ι) : k i ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (ht i)) (sub_ne_zero.mpr (hu i))
  let w (i : ι) := r i / k i
  let m₀ := ∑ i ∈ S, w i
  let m₁ := ∑ i ∈ S, w i * d i
  let m₂ := ∑ i ∈ S, w i * d i ^ 2
  let A := R * diagonal (fun i => (K i)⁻¹) * L
  have hEntry (a z : Fin 2) : A a z = ∑ i : S, R a i * (K i)⁻¹ * L i z := by
    change ((R * diagonal (fun i => (K i)⁻¹)) * L) a z = _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
  have hsum (c : ι → ℝ) : (∑ i : S, c i.val) = ∑ i ∈ S, c i :=
    Finset.sum_coe_sort S c
  have h₀₀ : A 0 0 = m₁ := by
    rw [hEntry]
    simp only [R, L, Matrix.of_apply, if_pos rfl, if_true, K]
    rw [hsum (fun i => v i * (k i)⁻¹ * (d i * v i))]
    apply sum_congr rfl
    intro i _
    simp only [w, r, div_eq_mul_inv, ← hv i]
    ring
  have h₀₁ : A 0 1 = m₀ := by
    rw [hEntry]
    simp only [R, L, Matrix.of_apply, if_pos rfl, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0), K]
    rw [hsum (fun i => v i * (k i)⁻¹ * v i)]
    apply sum_congr rfl
    intro i _
    simp only [w, r, div_eq_mul_inv, ← hv i]
    ring
  have h₁₀ : A 1 0 = m₂+b*m₁ := by
    rw [hEntry]
    simp only [R, L, Matrix.of_apply, if_pos rfl, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0),
      K, m₁, m₂, mul_sum, ← sum_add_distrib]
    rw [hsum (fun i => (d i+b)*v i*(k i)⁻¹*(d i*v i))]
    apply sum_congr rfl
    intro i _
    simp only [w, r, div_eq_mul_inv, ← hv i]
    ring
  have h₁₁ : A 1 1 = m₁+b*m₀ := by
    rw [hEntry]
    simp only [R, L, Matrix.of_apply, if_neg (by decide : (1 : Fin 2) ≠ 0),
      K, m₁, m₀, mul_sum, ← sum_add_distrib]
    rw [hsum (fun i => (d i+b)*v i*(k i)⁻¹*v i)]
    apply sum_congr rfl
    intro i _
    simp only [w, r, div_eq_mul_inv, ← hv i]
    ring
  have hA : (1+A).det = (1+m₁)^2+b*m₀-m₀*m₂ := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), h₀₀, h₀₁, h₁₀, h₁₁, zero_add]
    ring
  have h₂ : m₂ = (∑ i ∈ S, r i) + (t+u)*m₁ - t*u*m₀ := by
    simp only [m₂, m₁, m₀, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    dsimp only [w, k]
    field_simp [sub_ne_zero.mpr (ht i), sub_ne_zero.mpr (hu i)]
    ring
  let ℓ (z : ℝ) := 1 + ∑ i ∈ S, r i * (d i-z)⁻¹
  have hℓ (z a : ℝ) (hza : ∀ i, k i = (d i-z)*(d i-a))
      (hz : ∀ i, d i ≠ z) : ℓ z = 1+m₁-a*m₀ := by
    dsimp only [ℓ, m₁, m₀]
    rw [mul_sum, add_sub_assoc, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    dsimp only [w]
    field_simp [hK i, sub_ne_zero.mpr (hz i)]
    rw [hza i]
    ring
  have hℓt : ℓ t = 1+m₁-u*m₀ := hℓ t u (fun i => rfl) ht
  have hℓu : ℓ u = 1+m₁-t*m₀ := hℓ u t (fun i => mul_comm _ _) hu
  have hm : (ℓ t - ℓ u) / (t-u) = m₀ := by
    rw [hℓt, hℓu]
    field_simp [sub_ne_zero.mpr htu]
    ring
  have hq : q = (∑ i ∈ S, r i) + ∑ i ∈ Sᶜ, r i :=
    (sum_add_sum_compl S r).symm
  have hdet : (1+A).det = ℓ t * ℓ u + (∑ i ∈ Sᶜ, r i) * ((ℓ t-ℓ u)/(t-u)) := by
    rw [hA, h₂, hm, hℓt, hℓu]
    dsimp only [b]
    rw [hq]
    ring
  have hprod : (∏ i : S, K i) = secularNodalMinor d S t * secularNodalMinor d S u := by
    rw [show (∏ i : S, K i) = ∏ i ∈ S, k i from Finset.prod_coe_sort S k]
    unfold secularNodalMinor
    exact prod_mul_distrib
  have hnorm (z : ℝ) (hz : ∀ i, d i ≠ z) :
      secularLinearMinor h d S z = secularNodalMinor d S z * ℓ z := by
    unfold secularLinearMinor
    dsimp only [ℓ]
    rw [mul_add, mul_one, mul_sum]
    congr 1
    apply sum_congr rfl
    intro j hj
    unfold secularNodalMinor
    rw [← prod_erase_mul S _ hj]
    field_simp [sub_ne_zero.mpr (hz j)]
    ring
  rw [show (H - t • 1) * (H - u • 1) = N from rfl, hN,
    det_diagonal_add_rank_two_factor K (fun i => hK i.val) L R, hprod]
  change secularNodalMinor d S t * secularNodalMinor d S u * (1+A).det = _
  rw [hdet]
  simp only [secularQuadraticMinor, hnorm t ht, hnorm u hu, r, div_eq_mul_inv]
  ring

/-- The Hermitian rank-one matrix inside the secular chamber. -/
def secularChamberMatrix (h d : ι → ℝ) : Matrix ι ι ℝ :=
  diagonal d + vecMulVec (fun i => Real.sqrt (secularResidue h d i))
    (fun i => Real.sqrt (secularResidue h d i))

/-- The actual principal minors of the quadratic image satisfy the
weighted pure second-derivative identity inside the chamber. -/
theorem det_quadratic_principal_minor_weighted_second_sum (h d : ι → ℝ)
    (hd : Function.Injective d) (hr : ∀ i, 0 < secularResidue h d i) (S : Finset ι)
    (t u : ℝ) (htu : t ≠ u) (ht : ∀ i, d i ≠ t) (hu : ∀ i, d i ≠ u) :
    let F (p : ι → ℝ) :=
      let H := secularChamberMatrix h p
      (((H - t • 1) * (H - u • 1)).submatrix (fun i : S => i.val) (fun i : S => i.val)).det
    (∑ i, secularResidue h d i * deriv (deriv (fun z => F (Function.update d i z))) (d i)) = 0 := by
  intro F
  have hD (i j : ι) :
      ContinuousAt (fun x => secularResidue h (Function.update d i x) j) (d i) := by
    by_cases hj : j = i
    · subst j
      exact (hasDerivAt_secularResidue_update_self h d hd i).continuousAt
    · exact (hasDerivAt_secularResidue_update_of_ne h d (Ne.symm hj) (hd.ne (Ne.symm hj))).continuousAt
  have hregular (i : ι) (a : ℝ) (ha : ∀ j, d j ≠ a) :
      ∀ᶠ x in 𝓝 (d i), ∀ j, Function.update d i x j ≠ a := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j = i
    · subst j
      have hO : IsOpen {x : ℝ | x ≠ a} := isOpen_ne_fun continuous_id continuous_const
      have hE : ∀ᶠ x in 𝓝 (d i), x ≠ a := hO.mem_nhds (ha i)
      simpa only [Function.update_self] using hE
    · simp only [Function.update_of_ne hj]
      exact Eventually.of_forall fun _ => ha j
  have hE (i : ι) : (fun x => F (Function.update d i x)) =ᶠ[𝓝 (d i)]
      (fun x => secularQuadraticMinor h (Function.update d i x) S t u) := by
    have hpos : ∀ᶠ x in 𝓝 (d i), ∀ j, 0 < secularResidue h (Function.update d i x) j := by
      apply Filter.eventually_all.mpr
      intro j
      exact (hD i j).tendsto.eventually (Ioi_mem_nhds
        (by simpa only [Function.update_eq_self] using hr j))
    filter_upwards [hpos, hregular i t ht, hregular i u hu] with x hx ht' hu'
    let p := Function.update d i x
    exact det_quadratic_principal_minor_eq_secular h p
      (fun j => Real.sqrt (secularResidue h p j))
      (fun j => Real.mul_self_sqrt (hx j).le) S t u htu ht' hu'
  simp_rw [(hE _).deriv.deriv_eq]
  exact secularQuadraticMinor_weighted_second_sum h d hd S t u htu ht hu

end

end MOC
