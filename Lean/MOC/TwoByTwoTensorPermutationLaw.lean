import MOC.FiniteMinorLaw
import MOC.Small
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! A law on ten indexed permutations gives all squared minors of a
Kronecker product of two complex two by two unitaries. -/

open BigOperators Finset Matrix
open scoped Kronecker

namespace MOC

noncomputable section

private def rotation (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c : ℂ), (s : ℂ); -(s : ℂ), (c : ℂ)]

private theorem rotation_unitary (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    IsUnitary (rotation c s) := by
  have hr : c * c + s * s = 1 := by simpa only [pow_two] using h
  have hc : (c : ℂ) * c + (s : ℂ) * s = 1 := by exact_mod_cast hr
  have hs : (s : ℂ) * s + (c : ℂ) * c = 1 := by rwa [add_comm]
  have hunit : rotation c s * (rotation c s)ᴴ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotation, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
        Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val, Complex.star_def, hc, hs] <;> ring
  exact ⟨hunit, Matrix.mul_eq_one_comm.mp hunit⟩

private theorem tensor_adjoint (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kronecker_apply, star_mul', mul_comm]

private theorem tensor_unitary (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (A ⊗ₖ B) := by
  constructor
  · rw [tensor_adjoint, ← Matrix.mul_kronecker_mul, hA.1, hB.1, Matrix.one_kronecker_one]
  · rw [tensor_adjoint, ← Matrix.mul_kronecker_mul, hA.2, hB.2, Matrix.one_kronecker_one]

private def tensorCoordinate : Fin 4 ≃ Fin 2 × Fin 2 :=
  (finProdFinEquiv (m := 2) (n := 2)).symm

private def rotationTensorReal (c s d t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![c*d, c*t, s*d, s*t;
    -c*t, c*d, -s*t, s*d;
    -s*d, -s*t, c*d, c*t;
    s*t, -s*d, -c*t, c*d]

private theorem tensor_rotation_entries (c s d t : ℝ) :
    (rotation c s ⊗ₖ rotation d t).submatrix tensorCoordinate tensorCoordinate =
      Complex.ofRealHom.mapMatrix (rotationTensorReal c s d t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tensorCoordinate, finProdFinEquiv, Fin.divNat, Fin.modNat, rotation, rotationTensorReal,
      Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three,
      RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe,
      Complex.ofReal_mul, Complex.ofReal_neg, neg_mul] <;> ring

private def tensorPermImage : Fin 10 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![1, 0, 2, 3], ![0, 3, 2, 1],
    ![2, 1, 0, 3], ![1, 0, 3, 2], ![1, 2, 3, 0], ![3, 0, 1, 2],
    ![2, 3, 1, 0], ![3, 2, 0, 1]]

private def tensorPermInverse : Fin 10 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![1, 0, 2, 3], ![0, 3, 2, 1],
    ![2, 1, 0, 3], ![1, 0, 3, 2], ![3, 0, 1, 2], ![1, 2, 3, 0],
    ![3, 2, 0, 1], ![2, 3, 1, 0]]

private theorem tensorPerm_left :
    ∀ k i, tensorPermInverse k (tensorPermImage k i) = i := by decide +kernel

private theorem tensorPerm_right :
    ∀ k i, tensorPermImage k (tensorPermInverse k i) = i := by decide +kernel

private def tensorPerm (k : Fin 10) : Equiv.Perm (Fin 4) :=
  ⟨tensorPermImage k, tensorPermInverse k, tensorPerm_left k, tensorPerm_right k⟩

private def tensorWeight (p q : ℝ) : Fin 10 → ℝ :=
  let x := 1 - 2 * q
  let y := 2 * (q - p)
  let z := 2 * p
  let fixed := x^2 + x*y + y^2/4
  let sideSwap := x*y/2 + x*z/2 + y^2/4 + y*z/2 + z^2/8
  let crossSwap := x*z/2 + y*z/4 + z^2/8
  let cycle := y*z/4 + z^2/8
  ![fixed, sideSwap, sideSwap, crossSwap, crossSwap, y^2/4, cycle, cycle, z^2/8, z^2/8]

private theorem tensorWeight_nonneg {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1/2)
    (k : Fin 10) : 0 ≤ tensorWeight p q k := by
  have hx : 0 ≤ 1 - 2*q := by linarith only [hq]
  have hy : 0 ≤ 2*(q-p) := mul_nonneg (by norm_num) (sub_nonneg.mpr hpq)
  have hz : 0 ≤ 2*p := mul_nonneg (by norm_num) hp
  fin_cases k <;> dsimp [tensorWeight] <;> positivity

private theorem tensorWeight_sum (p q : ℝ) : ∑ k, tensorWeight p q k = 1 := by
  norm_num [tensorWeight, Fin.sum_univ_succ, Matrix.cons_val] <;> ring

private def tensorPair : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

private theorem tensorPair_cover : ∀ i j : Fin 4, i ≠ j →
    ∃ k : Fin 6, ({i, j} : Finset (Fin 4)) = {(tensorPair k).1, (tensorPair k).2} := by
  decide +kernel

private theorem tensorPair_distinct (i : Fin 6) : (tensorPair i).1 ≠ (tensorPair i).2 := by
  fin_cases i <;> decide

private theorem tensor_pair_event (a b c d : Fin 4) :
    ({a, b} : Finset (Fin 4)) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  revert a b c d
  decide +kernel

private theorem tensor_singleton_polynomial (c s d t : ℝ)
    (hc : c^2 + s^2 = 1) (hd : d^2 + t^2 = 1) (i j : Fin 4) :
    rotationTensorReal c s d t i j ^ 2 =
      ∑ k, if tensorPermImage k j = i then tensorWeight (s^2) (t^2) k else 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp (disch := decide) only [if_pos, if_neg]
    norm_num [rotationTensorReal, tensorWeight, Matrix.of_apply, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> first
      | ring1
      | linear_combination d^2 * hc + (1-s^2) * hd
      | linear_combination t^2 * hc
      | linear_combination s^2 * hd

set_option maxHeartbeats 1500000 in
private theorem tensor_pair_polynomial (c s d t : ℝ) (hc : c^2+s^2 = 1) (hd : d^2+t^2 = 1)
    (i j : Fin 6) :
    let a := (tensorPair i).1
    let b := (tensorPair i).2
    let x := (tensorPair j).1
    let y := (tensorPair j).2
    let R := rotationTensorReal c s d t
    (R a x * R b y - R a y * R b x)^2 =
      ∑ k, if (tensorPermImage k x = a ∧ tensorPermImage k y = b) ∨
          (tensorPermImage k x = b ∧ tensorPermImage k y = a)
        then tensorWeight (s^2) (t^2) k else 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    dsimp only
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp (disch := decide) only [if_pos, if_neg]
    norm_num [tensorPair, rotationTensorReal, tensorWeight, Matrix.of_apply, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> first
      | ring1
      | linear_combination (-(d^2 + t^2)^2*(-c^2 + s^2 - 1)) * hc + ((s - 1)^2*(s + 1)^2*(d^2 + t^2 + 1)) * hd
      | linear_combination (s^2*(d^2 + t^2)^2) * hc + (-s^2*(s - 1)*(s + 1)*(d^2 + t^2 + 1)) * hd
      | linear_combination (s^4*(d^2 + t^2 + 1)) * hd
      | linear_combination (d^4*(c^2 + s^2 + 1)) * hc + (d^2 - t^2 + 1) * hd
      | linear_combination (d^2*t^2*(c^2 + s^2 + 1)) * hc + (t^2) * hd
      | linear_combination (t^4*(c^2 + s^2 + 1)) * hc
      | linear_combination (-d^2*(-c^2*d^2 + d^2*s^2 - d^2 + 2*s^2*t^2)) * hc + ((s - 1)*(s + 1)*(d^2*s^2 - d^2 + s^2*t^2 + s^2 + t^2 - 1)) * hd
      | linear_combination (-t^2*(-c^2*t^2 + 2*d^2*s^2 + s^2*t^2 - t^2)) * hc + (s^2*(d^2*s^2 + s^2*t^2 + s^2 - 2*t^2)) * hd

private def TenTensorWeights {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) : Prop :=
  ∃ (p : Fin 10 → Equiv.Perm ι) (w : Fin 10 → ℝ),
    (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
    ∀ a b : ι → ℂ, (∑ k, (w k : ℂ) * matchingProduct a b (p k)) = determinantValue a b U

private theorem tensor_chart_weights (c s d t : ℝ) (hc : c^2+s^2 = 1) (hd : d^2+t^2 = 1)
    (hs : s^2 ≤ t^2) (ht : t^2 ≤ 1/2) :
    TenTensorWeights ((rotation c s ⊗ₖ rotation d t).submatrix tensorCoordinate tensorCoordinate) := by
  let U := (rotation c s ⊗ₖ rotation d t).submatrix tensorCoordinate tensorCoordinate
  let R := rotationTensorReal c s d t
  have hU : IsUnitary U := unitary_reindex tensorCoordinate tensorCoordinate
    (tensor_unitary _ _ (rotation_unitary c s hc) (rotation_unitary d t hd))
  have hentry (i j : Fin 4) : U i j = (R i j : ℂ) := by
    change ((rotation c s ⊗ₖ rotation d t).submatrix tensorCoordinate tensorCoordinate) i j = _
    rw [tensor_rotation_entries] <;> rfl
  let w := tensorWeight (s^2) (t^2)
  have hw : ∀ k, 0 ≤ w k := tensorWeight_nonneg (sq_nonneg s) hs ht
  have hsum : ∑ k, w k = 1 := tensorWeight_sum _ _
  refine ⟨tensorPerm, w, hw, hsum, fun a b =>
    determinantValue_eq_sum_of_indexed_minor_law a b U hU tensorPerm w ?_⟩
  apply indexed_minor_law_of_small U hU tensorPerm w
  intro I J hIJ hsmall
  have hle : I.card ≤ 2 := by simpa only [Fintype.card_fin] using hsmall
  by_cases hzero : I.card = 0
  · obtain rfl := Finset.card_eq_zero.mp hzero
    obtain rfl := Finset.card_eq_zero.mp (hIJ.symm.trans hzero)
    apply Complex.ofReal_injective
    rw [← sum_signedWeight_image_eq_subsetMinorSq U hU]
    simp [sum_signedWeight U (det_ne_zero_of_unitary hU), hsum]
  by_cases hone : I.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (hIJ.symm.trans hone)
    rw [subsetMinorSq_singleton U hU, hentry, Complex.normSq_ofReal, ← pow_two, Finset.sum_filter]
    simpa only [Finset.map_singleton, Finset.singleton_inj, Equiv.toEmbedding_apply, tensorPerm]
      using tensor_singleton_polynomial c s d t hc hd i j
  have htwo : I.card = 2 := by omega
  obtain ⟨i, k, hik, rfl⟩ := Finset.card_eq_two.mp htwo
  obtain ⟨j, l, hjl, rfl⟩ := Finset.card_eq_two.mp (hIJ.symm.trans htwo)
  obtain ⟨a, ha⟩ := tensorPair_cover i k hik
  obtain ⟨b, hb⟩ := tensorPair_cover j l hjl
  rw [ha, hb, subsetMinorSq_pair U hU (tensorPair_distinct a) (tensorPair_distinct b)]
  simp only [hentry, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.normSq_ofReal, ← pow_two,
    Finset.sum_filter, Finset.map_insert, Finset.map_singleton, tensor_pair_event,
    Equiv.toEmbedding_apply, tensorPerm]
  exact tensor_pair_polynomial c s d t hc hd a b

private theorem tensor_weights_of_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι ι ℂ) (r s : κ ≃ ι) (h : TenTensorWeights (U.submatrix r s)) :
    TenTensorWeights U := by
  obtain ⟨p, w, hw, hsum, he⟩ := h
  refine ⟨fun k => (s.symm.trans (p k)).trans r, w, hw, hsum, fun a b => ?_⟩
  have hv := he (a ∘ r) (b ∘ s)
  rw [determinantValue_reindex r s a b U] at hv
  have hmatch (k : Fin 10) :
      matchingProduct (a ∘ r) (b ∘ s) (p k) =
        matchingProduct a b ((s.symm.trans (p k)).trans r) := by
    unfold matchingProduct
    rw [← Equiv.prod_comp s (fun j => a (((s.symm.trans (p k)).trans r) j) + b j)]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Function.comp_apply]
  simpa only [hmatch] using hv

private theorem rotation_tensor_weights (c s d t : ℝ)
    (hc : c^2+s^2 = 1) (hd : d^2+t^2 = 1) (hs : s^2 ≤ 1/2) (ht : t^2 ≤ 1/2) :
    TenTensorWeights (rotation c s ⊗ₖ rotation d t) := by
  by_cases hst : s^2 ≤ t^2
  · exact tensor_weights_of_reindex _ tensorCoordinate tensorCoordinate
      (tensor_chart_weights c s d t hc hd hst ht)
  let swap := Equiv.prodComm (Fin 2) (Fin 2)
  have hs' : (rotation c s ⊗ₖ rotation d t).submatrix swap swap =
      rotation d t ⊗ₖ rotation c s := by
    ext ⟨i, j⟩ ⟨k, l⟩
    exact mul_comm _ _
  apply tensor_weights_of_reindex _ swap swap
  rw [hs']
  exact tensor_weights_of_reindex _ tensorCoordinate tensorCoordinate
    (tensor_chart_weights d t c s hd hc (le_of_lt (lt_of_not_ge hst)) hs)

private theorem phase_norm (z : ℂ) (h : Complex.normSq z = 1) : star z * z = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, h, Complex.ofReal_one]

theorem diagonal_phase_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (hf : ∀ i, Complex.normSq (f i) = 1) : IsUnitary (diagonal f) := by
  have hr : (diagonal f : Matrix ι ι ℂ) * (diagonal f)ᴴ = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    change f i * star (f i) = 1
    rw [mul_comm, phase_norm (f i) (hf i)]
  exact ⟨hr, Matrix.mul_eq_one_comm.mp hr⟩

private theorem phase_fixes_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f a : ι → ℂ) (hf : ∀ i, Complex.normSq (f i) = 1) :
    diagonal f * diagonal a * (diagonal f)ᴴ = diagonal a := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  change (f i * a i) * star (f i) = a i
  rw [mul_comm (f i) (a i), mul_assoc, mul_comm (f i) (star (f i)), phase_norm (f i) (hf i), mul_one]

theorem determinant_two_phases {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b l r : ι → ℂ) (V : Matrix ι ι ℂ)
    (hl : ∀ i, Complex.normSq (l i) = 1) (hr : ∀ i, Complex.normSq (r i) = 1) :
    determinantValue a b (diagonal l * V * diagonal r) = determinantValue a b V := by
  let L := diagonal l
  let R := diagonal r
  change (diagonal a + (L * V * R) * diagonal b * (L * V * R)ᴴ).det =
    (diagonal a + V * diagonal b * Vᴴ).det
  have h : (L * V * R) * diagonal b * (L * V * R)ᴴ =
      L * (V * (R * diagonal b * Rᴴ) * Vᴴ) * Lᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [h, phase_fixes_diagonal r b hr,
    ← det_unitary_conjugation L (diagonal a + V * diagonal b * Vᴴ)
      (diagonal_phase_unitary l hl), Matrix.mul_add, Matrix.add_mul, phase_fixes_diagonal l a hl]

theorem scalar_phase (z : ℂ) :
    ∃ u : ℂ, Complex.normSq u = 1 ∧ z = (‖z‖ : ℂ) * u := by
  by_cases hz : z = 0
  · exact ⟨1, Complex.normSq_one, by simp [hz]⟩
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  refine ⟨z / (‖z‖ : ℂ), ?_, ?_⟩
  · rw [Complex.normSq_div, Complex.normSq_ofReal, ← pow_two, ← Complex.normSq_eq_norm_sq]
    exact div_self (fun h => hz (Complex.normSq_eq_zero.mp h))
  · rw [mul_comm, div_mul_cancel₀ z hn]

private theorem phase_rotation (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnitary A)
    (hsorted : Complex.normSq (A 0 1) ≤ Complex.normSq (A 0 0)) :
    ∃ (c s : ℝ) (l r : Fin 2 → ℂ), c^2+s^2 = 1 ∧ s^2 ≤ 1/2 ∧
      (∀ i, Complex.normSq (l i) = 1) ∧ (∀ j, Complex.normSq (r j) = 1) ∧
      ∀ i j, A i j = l i * rotation c s i j * r j := by
  let c := ‖A 0 0‖
  let s := ‖A 0 1‖
  obtain ⟨r₀, hr₀, h₀⟩ := scalar_phase (A 0 0)
  obtain ⟨r₁, hr₁, h₁⟩ := scalar_phase (A 0 1)
  let r : Fin 2 → ℂ := ![r₀, r₁]
  have hr (i : Fin 2) : Complex.normSq (r i) = 1 := by
    fin_cases i
    · exact hr₀
    · exact hr₁
  let D := diagonal (fun i => star (r i))
  have hD : IsUnitary D := diagonal_phase_unitary _ (fun i => by
    simpa only [Complex.star_def, Complex.normSq_conj] using hr i)
  let B := A * D
  have hB : B * Bᴴ = 1 := by
    change (A * D) * (A * D)ᴴ = 1
    rw [Matrix.conjTranspose_mul]
    calc
      _ = A * (D * Dᴴ) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hD.1, Matrix.mul_one, hA.1]
  have hrecover (i j : Fin 2) : B i j * r j = A i j := by
    change (A * diagonal (fun i => star (r i))) i j * r j = _
    rw [Matrix.mul_diagonal, mul_assoc, phase_norm (r j) (hr j), mul_one]
  have hB₀ : B 0 0 = (c : ℂ) := by
    change (A * diagonal (fun i => star (r i))) 0 0 = _
    rw [Matrix.mul_diagonal, h₀]
    change ((c : ℂ) * r₀) * star r₀ = (c : ℂ)
    rw [mul_assoc, mul_comm r₀, phase_norm r₀ hr₀, mul_one]
  have hB₁ : B 0 1 = (s : ℂ) := by
    change (A * diagonal (fun i => star (r i))) 0 1 = _
    rw [Matrix.mul_diagonal, h₁]
    change ((s : ℂ) * r₁) * star r₁ = (s : ℂ)
    rw [mul_assoc, mul_comm r₁, phase_norm r₁ hr₁, mul_one]
  have hcsC : (c : ℂ)^2 + (s : ℂ)^2 = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hB
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hB₀, hB₁,
      Complex.star_def, Complex.conj_ofReal, Matrix.one_apply_eq, ← pow_two] using h
  have hcs : c^2+s^2 = 1 := by exact_mod_cast hcsC
  have hs : s^2 ≤ 1/2 := by
    have hsc : s^2 ≤ c^2 := by simpa only [c, s, Complex.normSq_eq_norm_sq] using hsorted
    linarith only [hsc, hcs]
  have horth : B 1 0 * (c : ℂ) + B 1 1 * (s : ℂ) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hB
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hB₀, hB₁,
      Complex.star_def, Complex.conj_ofReal, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
      using h
  let u := B.det
  have hu : Complex.normSq u = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self, Complex.ofReal_one, mul_comm]
    change B.det * star B.det = 1
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hB, Matrix.det_one]
  have hdet : u = (c : ℂ) * B 1 1 - (s : ℂ) * B 1 0 := by
    unfold u
    rw [Matrix.det_fin_two, hB₀, hB₁]
  have hB₂ : B 1 0 = u * -(s : ℂ) := by
    linear_combination (s : ℂ) * hdet + (c : ℂ) * horth - B 1 0 * hcsC
  have hB₃ : B 1 1 = u * (c : ℂ) := by
    linear_combination -(c : ℂ) * hdet + (s : ℂ) * horth - B 1 1 * hcsC
  let l : Fin 2 → ℂ := ![1, u]
  refine ⟨c, s, l, r, hcs, hs, fun i => ?_, hr, fun i j => ?_⟩
  · fin_cases i
    · exact Complex.normSq_one
    · exact hu
  · rw [← hrecover i j]
    fin_cases i <;> fin_cases j <;>
      simp [l, rotation, Matrix.of_apply, Matrix.cons_val, hB₀, hB₁, hB₂, hB₃]

private theorem sort_two_columns (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ p : Equiv.Perm (Fin 2), Complex.normSq (A 0 (p 1)) ≤ Complex.normSq (A 0 (p 0)) := by
  by_cases h : Complex.normSq (A 0 1) ≤ Complex.normSq (A 0 0)
  · exact ⟨Equiv.refl _, h⟩
  · exact ⟨Equiv.swap 0 1, by
      simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using le_of_lt (lt_of_not_ge h)⟩

private theorem arbitrary_tensor_weights (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnitary A) (hB : IsUnitary B) : TenTensorWeights (A ⊗ₖ B) := by
  obtain ⟨p, hp⟩ := sort_two_columns A
  obtain ⟨q, hq⟩ := sort_two_columns B
  let e : Equiv.Perm (Fin 2) := Equiv.refl _
  obtain ⟨c, s, lA, rA, hcs, hs, hlA, hrA, hAE⟩ :=
    phase_rotation (A.submatrix e p) (unitary_reindex e p hA) hp
  obtain ⟨d, t, lB, rB, hdt, ht, hlB, hrB, hBE⟩ :=
    phase_rotation (B.submatrix e q) (unitary_reindex e q hB) hq
  let L (ij : Fin 2 × Fin 2) := lA ij.1 * lB ij.2
  let R (ij : Fin 2 × Fin 2) := rA ij.1 * rB ij.2
  have hL (ij : Fin 2 × Fin 2) : Complex.normSq (L ij) = 1 := by
    dsimp only [L]
    rw [Complex.normSq_mul, hlA ij.1, hlB ij.2, one_mul]
  have hR (ij : Fin 2 × Fin 2) : Complex.normSq (R ij) = 1 := by
    dsimp only [R]
    rw [Complex.normSq_mul, hrA ij.1, hrB ij.2, one_mul]
  let V := rotation c s ⊗ₖ rotation d t
  have hv : (A ⊗ₖ B).submatrix (e.prodCongr e) (p.prodCongr q) = diagonal L * V * diagonal R := by
    ext ⟨i, j⟩ ⟨k, m⟩
    change (A.submatrix e p) i k * (B.submatrix e q) j m =
      (diagonal L * V * diagonal R) (i, j) (k, m)
    rw [hAE i k, hBE j m, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change (lA i * rotation c s i k * rA k) * (lB j * rotation d t j m * rB m) =
      (lA i * lB j) * (rotation c s i k * rotation d t j m) * (rA k * rB m)
    ring
  apply tensor_weights_of_reindex (A ⊗ₖ B) (e.prodCongr e) (p.prodCongr q)
  rw [hv]
  obtain ⟨perms, w, hw, hsum, h⟩ := rotation_tensor_weights c s d t hcs hdt hs ht
  refine ⟨perms, w, hw, hsum, fun a b => ?_⟩
  rw [determinant_two_phases a b L R V hL hR]
  exact h a b

/-- Ten indexed permutations with nonnegative weights give every squared minor
of the Kronecker product of two complex two by two unitaries. -/
theorem twoByTwoTensor_minorLaw (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnitary A) (hB : IsUnitary B) :
    ∃ (p : Fin 10 → Equiv.Perm (Fin 2 × Fin 2)) (w : Fin 10 → ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
      ∀ I J : Finset (Fin 2 × Fin 2), subsetMinorSq (A ⊗ₖ B) I J =
        ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k := by
  let U := A ⊗ₖ B
  have hU : IsUnitary U := tensor_unitary A B hA hB
  obtain ⟨p, w, hw, hs, he⟩ := arbitrary_tensor_weights A B hA hB
  refine ⟨p, w, hw, hs, fun I J => ?_⟩
  by_cases hcard : I.card = J.card
  · let a (i : Fin 2 × Fin 2) : ℂ := if i ∈ I then 0 else 1
    let b (j : Fin 2 × Fin 2) : ℂ := if j ∈ J then 1 else 0
    have hmarker : determinantValue a b U = (subsetMinorSq U I J : ℂ) := by
      rw [← signed_determinant a b U hU, ← sum_signedWeight_image_eq_subsetMinorSq U hU,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro σ _
      change signedWeight U σ * matchingProduct
        (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0) σ = _
      rw [matchingProduct_subset_marker I J hcard σ]
      split_ifs <;> simp
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, ← hmarker, ← he a b, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    change (w k : ℂ) * matchingProduct
      (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0) (p k) = _
    rw [matchingProduct_subset_marker I J hcard (p k)]
    split_ifs <;> simp
  · have hempty : (univ.filter (fun k => J.map (p k).toEmbedding = I)) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro k _ h
      exact hcard (by rw [← h, Finset.card_map])
    simp [subsetMinorSq, hcard, hempty]

/-- The same weights work for every pair of complex spectral lists. -/
theorem twoByTwoTensor_commonLaw (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnitary A) (hB : IsUnitary B) :
    ∃ (p : Fin 10 → Equiv.Perm (Fin 2 × Fin 2)) (w : Fin 10 → ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
      ∀ a b : Fin 2 × Fin 2 → ℂ, (∑ k, (w k : ℂ) * matchingProduct a b (p k)) =
        determinantValue a b (A ⊗ₖ B) :=
  arbitrary_tensor_weights A B hA hB

/-- The determinant inclusion for a Kronecker product of two complex two by two unitaries. -/
theorem holds_twoByTwoTensor (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnitary A) (hB : IsUnitary B) (a b : Fin 2 × Fin 2 → ℂ) : Holds a b (A ⊗ₖ B) := by
  obtain ⟨p, w, hw, hs, hm⟩ := twoByTwoTensor_minorLaw A B hA hB
  exact holds_of_indexed_minor_law a b _ (tensor_unitary A B hA hB) p w hw hs hm

end

end MOC
