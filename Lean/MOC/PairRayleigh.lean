import MOC.OrderFourGivens

/-! Closed support formula for a complex two-coordinate Rayleigh quotient.
For the geometric numerical-range interpretation, see G. Lakos,
DOI: 10.1007/s00013-023-01957-9. The orbit and support proofs here are direct. -/

namespace MOC

noncomputable section

/-- The real quadratic form of a Hermitian two-by-two block. -/
def pairRayleigh (a b : ℝ) (z x y : ℂ) : ℝ :=
  a * Complex.normSq x + b * Complex.normSq y + 2 * (star x * z * y).re

/-- Its maximum on the unit sphere, in terms of the diagonal difference
and the modulus of the mixed coefficient. -/
def pairRayleighMax (a b : ℝ) (z : ℂ) : ℝ :=
  (a + b + Real.sqrt ((a - b)^2 + 4 * Complex.normSq z)) / 2

private theorem normSq_pair_complete (t : ℝ) (z x y : ℂ) :
    Complex.normSq ((t : ℂ) * x - z * y) =
      t^2 * Complex.normSq x + Complex.normSq z * Complex.normSq y -
        2 * t * (star x * z * y).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private theorem pairRayleighMax_properties (a b : ℝ) (z : ℂ) :
    let l := pairRayleighMax a b z
    a ≤ l ∧ b ≤ l ∧ (l - a) * (l - b) = Complex.normSq z := by
  intro l
  let r := Real.sqrt ((a - b)^2 + 4 * Complex.normSq z)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = (a-b)^2 + 4 * Complex.normSq z :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)))
  have hle : |a-b| ≤ r := by
    apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs, hr2]
    linarith [Complex.normSq_nonneg z]
  have h1 := (abs_le.mp hle).1
  have h2 := (abs_le.mp hle).2
  change a ≤ (a + b + r) / 2 ∧ b ≤ (a + b + r) / 2 ∧ _ = _
  refine ⟨by linarith, by linarith, ?_⟩
  change ((a + b + r) / 2 - a) * ((a + b + r) / 2 - b) = Complex.normSq z
  linear_combination hr2 / 4

/-- The closed Rayleigh bound for every normalized pair. No spectral
decomposition of the ambient matrix is needed. -/
theorem pairRayleigh_le_max (a b : ℝ) (z x y : ℂ)
    (hxy : Complex.normSq x + Complex.normSq y = 1) :
    pairRayleigh a b z x y ≤ pairRayleighMax a b z := by
  let l := pairRayleighMax a b z
  obtain ⟨ha, hb, hprod⟩ := pairRayleighMax_properties a b z
  change a ≤ l at ha
  change b ≤ l at hb
  change (l-a)*(l-b) = Complex.normSq z at hprod
  change pairRayleigh a b z x y ≤ l
  by_cases ht : l-a = 0
  · have hz : z = 0 := Complex.normSq_eq_zero.mp (by rw [← hprod, ht, zero_mul])
    have ha' : a = l := (sub_eq_zero.mp ht).symm
    simp only [pairRayleigh, hz, mul_zero, zero_mul, Complex.zero_re, add_zero, ha']
    have hby := mul_le_mul_of_nonneg_right hb (Complex.normSq_nonneg y)
    linarith only [hby, show l*Complex.normSq x + l*Complex.normSq y = l by rw [← mul_add, hxy, mul_one]]
  · apply le_of_mul_le_mul_left _ (lt_of_le_of_ne (sub_nonneg.mpr ha) (Ne.symm ht))
    have h := Complex.normSq_nonneg ((↑(l-a) : ℂ) * x - z*y)
    rw [normSq_pair_complete, ← hprod] at h
    have he : l * (Complex.normSq x + Complex.normSq y) = l := by rw [hxy, mul_one]
    simp only [pairRayleigh]
    apply sub_nonneg.mp
    convert h using 1
    linear_combination -(l-a)*he

/-- Exact attainment of the Rayleigh bound, including a scalar block. -/
theorem exists_pairRayleigh_eq_max (a b : ℝ) (z : ℂ) :
    ∃ x y : ℂ, Complex.normSq x + Complex.normSq y = 1 ∧
      pairRayleigh a b z x y = pairRayleighMax a b z := by
  let l := pairRayleighMax a b z
  obtain ⟨ha, _, hprod⟩ := pairRayleighMax_properties a b z
  change a ≤ l at ha
  change (l-a)*(l-b) = Complex.normSq z at hprod
  let t := l-a
  by_cases ht : t = 0
  · refine ⟨1, 0, by simp, ?_⟩
    simpa [pairRayleigh] using (sub_eq_zero.mp ht).symm
  · let r := Real.sqrt (Complex.normSq z + t^2)
    have hrpos : 0 < r := Real.sqrt_pos.2
      (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_ne_zero ht))
    have hr2 : r^2 = Complex.normSq z + t^2 :=
      Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))
    let x : ℂ := z / (r : ℂ)
    let y : ℂ := ((t/r : ℝ) : ℂ)
    have hxy : Complex.normSq x + Complex.normSq y = 1 := by
      simp only [x, y, Complex.ofReal_div, Complex.normSq_div, Complex.normSq_ofReal, ← pow_two]
      rw [← add_div, ← hr2, div_self (pow_ne_zero _ hrpos.ne')]
    have he : (t : ℂ)*x - z*y = 0 := by
      simp only [x, y, Complex.ofReal_div]
      ring
    have hz := normSq_pair_complete t z x y
    rw [he, Complex.normSq_zero, ← hprod] at hz
    refine ⟨x, y, hxy, ?_⟩
    change pairRayleigh a b z x y = l
    apply mul_left_cancel₀ ht
    have hl : l * (Complex.normSq x + Complex.normSq y) = l := by rw [hxy, mul_one]
    change 0 = (l-a)^2 * Complex.normSq x + (l-a)*(l-b) * Complex.normSq y -
        2*(l-a)*(star x*z*y).re at hz
    change (l-a)*pairRayleigh a b z x y = (l-a)*l
    simp only [pairRayleigh]
    linear_combination hz + (l-a)*hl

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector with prescribed entries on a coordinate pair. -/
def pairVector (i j : ι) (x y : ℂ) : ι → ℂ :=
  fun k => if k = i then x else if k = j then y else 0

/-- An update by a rank-one matrix supported on a coordinate pair uses just
four entries of the adjugate of the unperturbed matrix. No invertibility
hypothesis is needed. -/
theorem det_add_pair_rankOne (C : Matrix ι ι ℂ) {i j : ι} (hij : i ≠ j)
    (δ x y : ℂ) :
    let w := pairVector i j x y
    (C + δ • vecMulVec w (star ∘ w)).det = C.det +
      δ * (star x * (C.adjugate i i * x + C.adjugate i j * y) +
        star y * (C.adjugate j i * x + C.adjugate j j * y)) := by
  intro w
  let u : ι → ℂ := (δ * star x) • w
  let v : ι → ℂ := (δ * star y) • w
  let col (k : ι) : ι → ℂ := fun k' => C k' k
  have hm : C + δ • vecMulVec w (star ∘ w) =
      (C.updateCol i (col i + u)).updateCol j (col j + v) := by
    ext p q : 1
    by_cases hqj : q = j
    · subst q
      simp [w, pairVector, u, v, col, Ne.symm hij, Matrix.vecMulVec_apply,
        Matrix.updateCol_apply, smul_eq_mul, Pi.smul_apply, mul_comm, mul_left_comm]
    · by_cases hqi : q = i
      · subst q
        simp [w, pairVector, u, v, col, hij, Matrix.vecMulVec_apply,
          Matrix.updateCol_apply, smul_eq_mul, Pi.smul_apply, mul_comm, mul_left_comm]
      · simp [w, pairVector, u, v, col, hqi, hqj, Matrix.vecMulVec_apply,
          Matrix.updateCol_apply, smul_eq_mul, Pi.smul_apply]
  have hci : C.updateCol i (col i) = C := Matrix.updateCol_eq_self _ _
  have hcj : C.updateCol j (col j) = C := Matrix.updateCol_eq_self _ _
  have hcomm (s t : ι → ℂ) : (C.updateCol i s).updateCol j t =
      (C.updateCol j t).updateCol i s := by
    ext p q : 1
    by_cases hqj : q = j
    · subst q
      simp [Matrix.updateCol_apply, Ne.symm hij]
    · by_cases hqi : q = i <;> simp [Matrix.updateCol_apply, hqi, hqj, hij]
  have hzero : ((C.updateCol i w).updateCol j w).det = 0 := by
    apply Matrix.det_zero_of_column_eq hij
    intro k
    simp [Matrix.updateCol_apply, hij]
  have hcross : ((C.updateCol i u).updateCol j v).det = 0 := by
    rw [show v = (δ * star y) • w from rfl, Matrix.det_updateCol_smul, hcomm u w,
      show u = (δ * star x) • w from rfl, Matrix.det_updateCol_smul,
      ← hcomm w w, hzero, mul_zero, mul_zero]
  rw [hm, Matrix.det_updateCol_add, hcomm, Matrix.det_updateCol_add, hcj, hci,
    Matrix.det_updateCol_smul, hcomm _ v, Matrix.det_updateCol_add, ← hcomm (col i) v, hci,
    ← hcomm u v, hcross, add_zero, Matrix.det_updateCol_smul,
    ← Matrix.cramer_apply, ← Matrix.cramer_apply,
    Matrix.cramer_eq_adjugate_mulVec]
  have hMv (k : ι) : (C.adjugate *ᵥ w) k = C.adjugate k i * x + C.adjugate k j * y := by
    rw [Matrix.mulVec, dotProduct]
    calc
      _ = ∑ q ∈ ({i,j} : Finset ι), C.adjugate k q * w q := by
        apply (Finset.sum_subset (Finset.subset_univ _ ) ?_).symm
        intro q _ hn
        have he : q ≠ i ∧ q ≠ j := by simpa using hn
        simp [w, pairVector, he.1, he.2]
      _ = _ := by rw [Finset.sum_pair hij]; simp [w, pairVector, Ne.symm hij]
  rw [hMv, hMv]
  ring

private theorem re_pairQuadratic (A B C D x y : ℂ) :
    (star x * (A * x + B * y) + star y * (C * x + D * y)).re =
      pairRayleigh A.re D.re ((B + star C) / 2) x y := by
  have ht : ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) := by norm_num [Complex.ofReal_div, one_div]
  rw [div_eq_mul_inv, ht]
  simp only [pairRayleigh, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add]
  ring

/-- The projected rank-one determinant over a coordinate pair is exactly a
Hermitian Rayleigh quotient plus the baseline determinant's projection. -/
theorem support_add_pair_rankOne (C : Matrix ι ι ℂ) {i j : ι} (hij : i ≠ j)
    (η δ x y : ℂ) :
    let w := pairVector i j x y
    let Z := (η * δ) • C.adjugate
    (η * (C + δ • vecMulVec w (star ∘ w)).det).re = (η * C.det).re +
      pairRayleigh (Z i i).re (Z j j).re ((Z i j + star (Z j i)) / 2) x y := by
  dsimp only
  rw [det_add_pair_rankOne C hij, mul_add, Complex.add_re, ← mul_assoc]
  congr 1
  rw [← re_pairQuadratic]
  congr 1
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- Exact support value of the pair perturbation, including when the
baseline determinant vanishes. The displayed bound is attained. -/
theorem isGreatest_support_add_pair_rankOne (C : Matrix ι ι ℂ) {i j : ι} (hij : i ≠ j)
    (η δ : ℂ) :
    let Z := (η * δ) • C.adjugate
    IsGreatest
      {t : ℝ | ∃ x y : ℂ, Complex.normSq x + Complex.normSq y = 1 ∧
        let w := pairVector i j x y
        t = (η * (C + δ • vecMulVec w (star ∘ w)).det).re}
      ((η * C.det).re + pairRayleighMax (Z i i).re (Z j j).re ((Z i j + star (Z j i)) / 2)) := by
  dsimp only
  constructor
  · obtain ⟨x, y, hxy, he⟩ := exists_pairRayleigh_eq_max
      (((η * δ) • C.adjugate) i i).re (((η * δ) • C.adjugate) j j).re
      ((((η * δ) • C.adjugate) i j + star (((η * δ) • C.adjugate) j i)) / 2)
    refine ⟨x, y, hxy, ?_⟩
    dsimp only
    rw [support_add_pair_rankOne C hij, he]
  · rintro t ⟨x, y, hxy, he⟩
    rw [he, support_add_pair_rankOne C hij]
    exact add_le_add_left (pairRayleigh_le_max _ _ _ _ _ hxy) _

private theorem pairPlane_exists_unitary (x y : ℂ)
    (hxy : Complex.normSq x + Complex.normSq y = 1) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℂ, IsUnitary V ∧ V 0 0 = x ∧ V 1 0 = y := by
  let V : Matrix (Fin 2) (Fin 2) ℂ := !![x, -star y; y, star x]
  have he : (starRingEnd ℂ) x * x + (starRingEnd ℂ) y * y = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_add, hxy, Complex.ofReal_one]
  have hV : V * Vᴴ = 1 := by
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp only [V, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.vecCons,
        Fin.cons_zero, Fin.cons_one,
        Matrix.one_apply_eq, star_neg, star_star, neg_mul, mul_neg] <;>
      simp [Matrix.one_apply] <;> first | exact he | exact Eq.trans (by ac_rfl) he | ring
  exact ⟨V, ⟨hV, Matrix.mul_eq_one_comm.mp hV⟩, by simp [V], by simp [V]⟩

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Replace the first value in the pair by the second. The remaining
difference can then move freely as a rank-one projector on the pair. -/
def pairPlaneFlatten (a : Fin 2 ⊕ κ → ℂ) : Fin 2 ⊕ κ → ℂ :=
  Sum.elim (fun _ => a (.inl 1)) (fun k => a (.inr k))

private theorem conjugate_diagonal_pairPlane
    (a : Fin 2 ⊕ κ → ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) (hV : IsUnitary V) :
    let R : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ := fromBlocks V 0 0 1
    let w := pairVector (Sum.inl 0 : Fin 2 ⊕ κ) (.inl 1) (V 0 0) (V 1 0)
    R * diagonal a * Rᴴ = diagonal (pairPlaneFlatten a) +
      (a (.inl 0) - a (.inl 1)) • vecMulVec w (star ∘ w) := by
  intro R w
  have ha : diagonal a =
      fromBlocks (diagonal (fun k => a (.inl k))) 0 0
        (diagonal (fun k => a (.inr k))) := by
    ext p q
    cases p <;> cases q <;> simp [Matrix.diagonal_apply]
  rw [ha]
  simp only [R, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  ext p q : 1
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have hVpq := congrArg (fun T : Matrix (Fin 2) (Fin 2) ℂ => T p q) hV.1
      change (V * Vᴴ) p q = _ at hVpq
      have hwp (t : Fin 2) : w (.inl t) = V t 0 := by
        fin_cases t <;> simp [w, pairVector]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.vecMulVec_apply, Function.comp_apply, hwp]
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_diagonal]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at hVpq
      have hd : (diagonal (pairPlaneFlatten a)) (.inl p) (.inl q) =
          (1 : Matrix (Fin 2) (Fin 2) ℂ) p q * a (.inl 1) := by
        by_cases hpq : p=q <;> simp [Matrix.diagonal_apply, Matrix.one_apply, pairPlaneFlatten, hpq]
      rw [hd]
      linear_combination a (.inl 1) * hVpq
    | inr q => simp [w, pairVector, Matrix.diagonal_apply, Matrix.vecMulVec_apply]
  | inr p =>
    cases q <;> simp [w, pairVector, Matrix.diagonal_apply, Matrix.vecMulVec_apply, pairPlaneFlatten]

/-- Exact maximum on the full complex two-coordinate unitary orbit of the
first summand. The second summand is arbitrary, and singular baselines
require no separate argument. Reindexing makes the pair any two labels. -/
theorem isGreatest_unitary_pairPlane_support (a : Fin 2 ⊕ κ → ℂ)
    (B : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ) (η : ℂ) :
    let C := diagonal (pairPlaneFlatten a) + B
    let Z := (η * (a (.inl 0) - a (.inl 1))) • C.adjugate
    let i : Fin 2 ⊕ κ := .inl 0
    let j : Fin 2 ⊕ κ := .inl 1
    IsGreatest
      {t : ℝ | ∃ V : Matrix (Fin 2) (Fin 2) ℂ, IsUnitary V ∧
        let R : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ := fromBlocks V 0 0 1
        t = (η * (R * diagonal a * Rᴴ + B).det).re}
      ((η * C.det).re + pairRayleighMax (Z i i).re (Z j j).re ((Z i j + star (Z j i)) / 2)) := by
  intro C Z i j
  have hij : i ≠ j := by simp [i, j]
  have hs := isGreatest_support_add_pair_rankOne C hij η (a (.inl 0) - a (.inl 1))
  convert hs using 2
  ext t
  constructor
  · rintro ⟨V, hV, hval⟩
    have hnorm : Complex.normSq (V 0 0) + Complex.normSq (V 1 0) = 1 := by
      have hv00 := congrArg (fun W : Matrix (Fin 2) (Fin 2) ℂ => W 0 0) hV.2
      change (Vᴴ * V) 0 0 = 1 at hv00
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.conjTranspose_apply] at hv00
      change (starRingEnd ℂ) (V 0 0) * V 0 0 + (starRingEnd ℂ) (V 1 0) * V 1 0 = 1 at hv00
      rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
        ← Complex.ofReal_add, ← Complex.ofReal_one] at hv00
      exact Complex.ofReal_injective hv00
    refine ⟨V 0 0, V 1 0, hnorm, ?_⟩
    rw [hval, conjugate_diagonal_pairPlane a V hV]
    congr 2
    dsimp only [i, j, C]
    exact congrArg Matrix.det (add_right_comm _ _ _)
  · rintro ⟨x, y, hxy, hval⟩
    obtain ⟨V, hV, hx, hy⟩ := pairPlane_exists_unitary x y hxy
    refine ⟨V, hV, ?_⟩
    dsimp only
    rw [conjugate_diagonal_pairPlane a V hV, hx, hy, hval]
    congr 2
    dsimp only [i, j, C]
    exact congrArg Matrix.det (add_right_comm _ _ _)

private theorem pairRayleighMax_eq_first_iff (a b : ℝ) (z : ℂ) :
    pairRayleighMax a b z = a ↔ b ≤ a ∧ z = 0 := by
  constructor
  · intro he
    obtain ⟨_, hb, hp⟩ := pairRayleighMax_properties a b z
    rw [he, sub_self, zero_mul] at hp
    exact ⟨he ▸ hb, Complex.normSq_eq_zero.mp hp.symm⟩
  · rintro ⟨hb, rfl⟩
    simp only [pairRayleighMax, Complex.normSq_zero, mul_zero, add_zero, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hb)]
    ring

/-- The identity mixer is a maximum in the full two-coordinate plane
exactly when a diagonal inequality and a mixed-cofactor equation hold.
This derivative-free stationarity test uses no inverse of the baseline. -/
theorem unitary_pairPlane_identity_max_iff (a : Fin 2 ⊕ κ → ℂ)
    (B : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ) (η : ℂ) :
    let C := diagonal (pairPlaneFlatten a) + B
    let δ := a (.inl 0) - a (.inl 1)
    let Z := (η * δ) • C.adjugate
    let i : Fin 2 ⊕ κ := .inl 0
    let j : Fin 2 ⊕ κ := .inl 1
    (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsUnitary V →
      let R : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ := fromBlocks V 0 0 1
      (η * (R * diagonal a * Rᴴ + B).det).re ≤ (η * (diagonal a + B).det).re) ↔
      (Z j j).re ≤ (Z i i).re ∧ Z i j + star (Z j i) = 0 := by
  intro C δ Z i j
  let z := (Z i j + star (Z j i)) / 2
  have hij : i ≠ j := by simp [i, j]
  have h1 : IsUnitary (1 : Matrix (Fin 2) (Fin 2) ℂ) := isUnitary_one
  have hbase := conjugate_diagonal_pairPlane a (1 : Matrix (Fin 2) (Fin 2) ℂ) h1
  dsimp only at hbase
  rw [Matrix.fromBlocks_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at hbase
  have hC : diagonal a + B =
      C + δ • vecMulVec (pairVector i j 1 0) (star ∘ pairVector i j 1 0) := by
    change diagonal a + B = _
    rw [hbase]
    exact add_right_comm _ _ _
  have hval : (η * (diagonal a + B).det).re = (η * C.det).re + (Z i i).re := by
    rw [hC, support_add_pair_rankOne C hij]
    simp [pairRayleigh, Z]
  have hg := isGreatest_unitary_pairPlane_support a B η
  change IsGreatest _ ((η * C.det).re + pairRayleighMax (Z i i).re (Z j j).re z) at hg
  have hmem : (η * (diagonal a + B).det).re ∈
      {t : ℝ | ∃ V : Matrix (Fin 2) (Fin 2) ℂ, IsUnitary V ∧
        let R : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℂ := fromBlocks V 0 0 1
        t = (η * (R * diagonal a * Rᴴ + B).det).re} := by
    refine ⟨1, h1, ?_⟩
    dsimp only
    rw [Matrix.fromBlocks_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  constructor
  · intro hmax
    obtain ⟨W, hW, hEq⟩ := hg.1
    have hle := hmax W hW
    dsimp only at hEq hle
    rw [← hEq, hval] at hle
    have hge := hg.2 hmem
    rw [hval] at hge
    obtain ⟨hdiag, hz⟩ := (pairRayleighMax_eq_first_iff _ _ _).mp
      (le_antisymm (le_of_add_le_add_left hle) (le_of_add_le_add_left hge))
    exact ⟨hdiag, (div_eq_zero_iff.mp hz).resolve_right (by norm_num)⟩
  · rintro ⟨hdiag, hz⟩ V hV
    dsimp only
    have hm := hg.2 ⟨V, hV, rfl⟩
    have he := (pairRayleighMax_eq_first_iff (Z i i).re (Z j j).re z).mpr
      ⟨hdiag, by dsimp only [z]; rw [hz, zero_div]⟩
    rwa [he, ← hval] at hm

end

end MOC
