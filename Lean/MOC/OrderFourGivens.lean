import MOC.SparseRow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MOC.Realification
import MOC.Support

/-!
An exact flat-swap test. The determinant numerator for a two-row
rotation is quadratic by row multilinearity.
-/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def weighted (a b : ι → ℂ) (U : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (a i + b j) * U i j

private def mixedRows (U : Matrix ι ι ℂ) (i j : ι) (c s : ℂ) : Matrix ι ι ℂ :=
  (U.updateRow i (c • U i + s • U j)).updateRow j (c • U j + (-s) • U i)

private theorem weighted_mixedRows_det (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (i j : ι) (hij : i ≠ j) (c s : ℂ) :
    let W := weighted a b U
    let Wᵢⱼ := fun k => (a i + b k) * U j k
    let Wⱼᵢ := fun k => (a j + b k) * U i k
    (weighted a b (mixedRows U i j c s)).det =
      c ^ 2 * W.det + s ^ 2 * (weighted a b (mixedRows U i j 0 1)).det +
        c * s * ((W.updateRow i Wᵢⱼ).det - (W.updateRow j Wⱼᵢ).det) := by
  intro W Wᵢⱼ Wⱼᵢ
  have hmat (r t : ℂ) :
      weighted a b (mixedRows U i j r t) =
        (W.updateRow i (r • W i + t • Wᵢⱼ)).updateRow j
          (r • W j + (-t) • Wⱼᵢ) := by
    ext x y
    by_cases hxj : x = j
    · subst x
      simp [weighted, mixedRows, W, Wⱼᵢ, Matrix.updateRow, Pi.smul_apply, smul_eq_mul]
      ring
    · by_cases hxi : x = i
      · subst x
        simp [weighted, mixedRows, W, Wᵢⱼ, Matrix.updateRow, Pi.smul_apply, smul_eq_mul, hij]
        ring
      · simp [weighted, mixedRows, W, Matrix.updateRow, hxi, hxj]
  have hcomm (u v : ι → ℂ) :
      (W.updateRow i u).updateRow j v = (W.updateRow j v).updateRow i u := by
    ext x y
    by_cases hj : x = j
    · subst x
      simp [Matrix.updateRow, Ne.symm hij]
    · by_cases hi : x = i
      · subst x
        simp [Matrix.updateRow, hij]
      · simp [Matrix.updateRow, hi, hj]
  have hswap :
      (weighted a b (mixedRows U i j 0 1)).det =
        -((W.updateRow j Wⱼᵢ).updateRow i Wᵢⱼ).det := by
    rw [hmat]
    simp only [zero_smul, zero_add, one_smul]
    simp_rw [Matrix.det_updateRow_smul]
    simp only [neg_one_mul, hcomm]
  rw [hmat, hswap, Matrix.det_updateRow_add,
    Matrix.det_updateRow_smul, Matrix.det_updateRow_smul, hcomm, hcomm]
  simp only [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  rw [← hcomm (W i) Wⱼᵢ, Matrix.updateRow_eq_self]
  ring

/-- Two opposite 45-degree rotations suffice to show that the real mixed
coefficient vanishes when both the original and the swapped value already
equal the maximum. There is no enumeration of row pairs or matchings. -/
theorem flat_two_variable_circle {A B C : ℝ} (hswap : B = A)
    (hmax : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 →
      c ^ 2 * A + s ^ 2 * B + c * s * C ≤ A) :
    ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 →
      c ^ 2 * A + s ^ 2 * B + c * s * C = A := by
  let r : ℝ := Real.sqrt (1 / 2)
  have hr : r ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have h₁ := hmax r r (by linarith)
  have h₂ := hmax r (-r) (by rw [neg_sq]; linarith)
  have hc : C = 0 := by
    rw [hswap, ← pow_two, hr] at h₁
    rw [hswap, neg_sq, mul_neg, ← pow_two, hr, neg_mul] at h₂
    linarith
  intro c s h
  rw [hswap, hc, mul_zero, add_zero, ← add_mul, h, one_mul]


private theorem mixedRows_unitary (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (i j : ι) (hij : i ≠ j) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsUnitary (mixedRows U i j (c : ℂ) (s : ℂ)) := by
  let W := mixedRows U i j (c : ℂ) (s : ℂ)
  have hWi : W i = (c : ℂ) • U i + (s : ℂ) • U j := by
    funext x
    simp [W, mixedRows, Matrix.updateRow, hij]
  have hWj : W j = (c : ℂ) • U j + -(s : ℂ) • U i := by
    funext x
    simp [W, mixedRows, Matrix.updateRow]
  have hWk (k : ι) (ki : k ≠ i) (kj : k ≠ j) : W k = U k := by
    funext x
    simp [W, mixedRows, Matrix.updateRow, ki, kj]
  have hconj (r t : ℝ) (x y : ι → ℂ) :
      (star ∘ ((r : ℂ) • x + (t : ℂ) • y)) =
        (r : ℂ) • (star ∘ x) + (t : ℂ) • (star ∘ y) := by
    funext k
    simp [Pi.smul_apply, smul_eq_mul, Complex.star_def]
  have hdot (x y : ι) : U x ⬝ᵥ (star ∘ U y) = (1 : Matrix ι ι ℂ) x y := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Function.comp_apply]
      using congrArg (fun M : Matrix ι ι ℂ => M x y) hU.1
  have hWW : W * Wᴴ = 1 := by
    ext x y
    change W x ⬝ᵥ (star ∘ W y) = _
    have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    by_cases hxi : x = i
    · subst x
      by_cases hyi : y = i
      · subst y
        simp only [hWi, hconj, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
          hdot, Matrix.one_apply_eq, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij),
          smul_eq_mul, mul_zero, zero_add, add_zero, mul_one]
        simpa only [pow_two] using hcs'
      · by_cases hyj : y = j
        · subst y
          simp only [hWi, hWj, ← Complex.ofReal_neg, hconj, add_dotProduct, dotProduct_add,
            smul_dotProduct, dotProduct_smul, hdot, Matrix.one_apply_eq, Matrix.one_apply_ne hij,
            Matrix.one_apply_ne (Ne.symm hij), smul_eq_mul, mul_zero, zero_add, add_zero, mul_one]
          push_cast
          ring
        · rw [hWi, hWk y hyi hyj]
          simp only [add_dotProduct, smul_dotProduct, hdot, Matrix.one_apply_ne (Ne.symm hyi), Matrix.one_apply_ne (Ne.symm hyj), smul_zero, add_zero]
    · by_cases hxj : x = j
      · subst x
        by_cases hyi : y = i
        · subst y
          simp only [hWi, hWj, hconj, add_dotProduct, dotProduct_add,
            smul_dotProduct, dotProduct_smul, hdot, Matrix.one_apply_eq, Matrix.one_apply_ne hij,
            Matrix.one_apply_ne (Ne.symm hij), smul_eq_mul, mul_zero, zero_add, add_zero, mul_one]
          ring
        · by_cases hyj : y = j
          · subst y
            simp only [hWj, ← Complex.ofReal_neg, hconj, add_dotProduct, dotProduct_add,
              smul_dotProduct, dotProduct_smul, hdot, Matrix.one_apply_eq, Matrix.one_apply_ne hij,
              Matrix.one_apply_ne (Ne.symm hij), smul_eq_mul, mul_zero, zero_add, add_zero, mul_one]
            push_cast
            linear_combination hcs'
          · rw [hWj, hWk y hyi hyj]
            simp only [add_dotProduct, smul_dotProduct, hdot, Matrix.one_apply_ne (Ne.symm hyi), Matrix.one_apply_ne (Ne.symm hyj), smul_zero, add_zero]
      · rw [hWk x hxi hxj]
        by_cases hyi : y = i
        · subst y
          rw [hWi, hconj]
          simp only [dotProduct_add, dotProduct_smul, hdot, Matrix.one_apply_ne hxi, Matrix.one_apply_ne hxj, smul_zero, add_zero]
        · by_cases hyj : y = j
          · subst y
            rw [hWj, ← Complex.ofReal_neg, hconj]
            simp only [dotProduct_add, dotProduct_smul, hdot, Matrix.one_apply_ne hxi, Matrix.one_apply_ne hxj, smul_zero, add_zero]
          · rw [hWk y hyi hyj, hdot]
  exact ⟨hWW, mul_eq_one_comm.mp hWW⟩


private theorem det_mixedRows_eq (U : Matrix ι ι ℂ) (i j : ι) (hij : i ≠ j)
    (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (mixedRows U i j c s).det = U.det := by
  let S := U.submatrix (Equiv.swap i j) id
  have hSj : S j = U i := by funext k; simp [S]
  have hswap : mixedRows U i j 0 1 = S.updateRow j ((-1 : ℂ) • S j) := by
    ext x y
    by_cases hxj : x = j
    · subst x
      simp [mixedRows, hSj, Matrix.updateRow, Pi.smul_apply, smul_eq_mul]
    · by_cases hxi : x = i
      · subst x
        simp [mixedRows, Matrix.updateRow, S, hij]
      · simp [mixedRows, Matrix.updateRow, S, hxj, hxi, Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have hswap' : (mixedRows U i j 0 1).det = U.det := by
    rw [hswap, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
    change (-1 : ℂ) * (U.submatrix (Equiv.swap i j) id).det = _
    rw [Matrix.det_permute, Equiv.Perm.sign_swap hij]
    simp
  have h := weighted_mixedRows_det (fun _ => 1) (fun _ => 0) U i j hij c s
  have hwt (X : Matrix ι ι ℂ) : weighted (fun _ => 1) (fun _ => 0) X = X := by
    ext x y
    simp [weighted]
  dsimp only at h
  rw [hwt, hwt, hwt, hswap'] at h
  simp only [add_zero, one_mul] at h
  rw [Matrix.det_updateRow_eq_zero (Ne.symm hij), Matrix.det_updateRow_eq_zero hij,
    sub_self, mul_zero, add_zero, ← add_mul, hcs, one_mul] at h
  exact h

private theorem det_weighted_eq (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (weighted a b U).det = determinantValue a b U * U.det := by
  rw [determinantValue, ← Matrix.det_mul]
  congr 1
  change weighted a b U = (diagonal a + U * diagonal b * Uᴴ) * U
  rw [Matrix.add_mul, Matrix.mul_assoc _ _ U, hU.2, Matrix.mul_one]
  ext x y
  simp only [weighted, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring


/-- Rotate rows (i,j) by the oriented (2	imes 2) block
(left(egin{smallmatrix}c&s\-s&cend{smallmatrix}ight)). -/
def rotateRows (U : Matrix ι ι ℂ) (i j : ι) (c s : ℝ) : Matrix ι ι ℂ :=
  mixedRows U i j (c : ℂ) (s : ℂ)

theorem isUnitary_rotateRows (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (i j : ι) (hij : i ≠ j) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsUnitary (rotateRows U i j c s) := mixedRows_unitary U hU i j hij c s hcs

/-- At a global support maximum, a flat signed swap of two rows forces the
entire plane rotation of those rows to be flat. -/
theorem flat_rotateRows_of_support_max (a b : ι → ℂ) (η : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (i j : ι) (hij : i ≠ j)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (hswap : (η * determinantValue a b (rotateRows U i j 0 1)).re =
      (η * determinantValue a b U).re)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (η * determinantValue a b (rotateRows U i j c s)).re =
      (η * determinantValue a b U).re := by
  let W := weighted a b U
  let wᵢⱼ := fun k => (a i + b k) * U j k
  let wⱼᵢ := fun k => (a j + b k) * U i k
  let x := ((W.updateRow i wᵢⱼ).det - (W.updateRow j wⱼᵢ).det) / U.det
  let f (V : Matrix ι ι ℂ) := (η * determinantValue a b V).re
  have he (r t : ℝ) (hrt : r ^ 2 + t ^ 2 = 1) :
      f (rotateRows U i j r t) = r ^ 2 * f U +
        t ^ 2 * f (rotateRows U i j 0 1) + r * t * (η * x).re := by
    have h := weighted_mixedRows_det a b U i j hij (r : ℂ) (t : ℂ)
    dsimp only at h
    change (weighted a b (rotateRows U i j r t)).det =
      (r : ℂ) ^ 2 * (weighted a b U).det +
        (t : ℂ) ^ 2 * (weighted a b (rotateRows U i j 0 1)).det +
        (r : ℂ) * (t : ℂ) * ((W.updateRow i wᵢⱼ).det - (W.updateRow j wⱼᵢ).det) at h
    have hdW : (rotateRows U i j r t).det = U.det :=
      det_mixedRows_eq U i j hij _ _ (by exact_mod_cast hrt)
    have hdS : (rotateRows U i j 0 1).det = U.det :=
      det_mixedRows_eq U i j hij _ _ (by norm_num)
    rw [det_weighted_eq _ _ _ (isUnitary_rotateRows U hU i j hij r t hrt), hdW,
      det_weighted_eq _ _ _ hU,
      det_weighted_eq _ _ _ (isUnitary_rotateRows U hU i j hij 0 1 (by norm_num)), hdS] at h
    have h' : determinantValue a b (rotateRows U i j r t) =
      (r : ℂ) ^ 2 * determinantValue a b U +
        (t : ℂ) ^ 2 * determinantValue a b (rotateRows U i j 0 1) +
        (r : ℂ) * (t : ℂ) * x := by
      apply mul_right_cancel₀ (det_ne_zero_of_unitary hU)
      rw [h, add_mul, add_mul]
      dsimp only [x]
      rw [mul_assoc ((r : ℂ) * (t : ℂ)), div_mul_cancel₀ _ (det_ne_zero_of_unitary hU)]
      ring
    dsimp only [f]
    rw [h']
    simp only [mul_add, Complex.add_re]
    rw [mul_left_comm η, mul_left_comm η ((t : ℂ) ^ 2), mul_left_comm η ((r : ℂ) * (t : ℂ)),
      ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    simp only [Complex.re_ofReal_mul]
  change f (rotateRows U i j c s) = f U
  rw [he c s hcs]
  exact flat_two_variable_circle hswap (fun r t hrt => by
    rw [← he r t hrt]
    exact hmax _ (isUnitary_rotateRows U hU i j hij r t hrt)) c s hcs


private theorem exists_real_annihilating_rotation (x y : ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c * x + s * y = 0 := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg y]
    exact ⟨1, 0, by norm_num, by simp [hx]⟩
  · have hp : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    let d := Real.sqrt (x ^ 2 + y ^ 2)
    have hd : d ≠ 0 := (Real.sqrt_pos.2 hp).ne'
    have hds : d ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hp.le
    refine ⟨y / d, -x / d, ?_, ?_⟩
    · rw [div_pow, div_pow, ← add_div, neg_sq, hds, add_comm]
      exact div_self h
    · field_simp
      ring

/-- A strict order-four violation cannot have a flat signed row swap avoiding
the row of any existing zero. Indeed a plane rotation at the same height
then places a second zero in that column, and the smaller-order theorem
bounds the rotated value. -/
theorem four_no_flat_swap_away_from_zero
    (a b : Fin 4 → ℂ) (η : ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (i j r k : Fin 4) (hij : i ≠ j) (hri : r ≠ i) (hrj : r ≠ j)
    (hzero : O.val r k = 0) :
    let U := Complex.ofRealHom.mapMatrix O.val
    (∀ V : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) →
    (∀ p : Equiv.Perm (Fin 4),
      (η * matchingProduct a b p).re < (η * determinantValue a b U).re) →
    (η * determinantValue a b (rotateRows U i j 0 1)).re <
      (η * determinantValue a b U).re := by
  intro U hmax hgap
  have hU := isUnitary_ofReal_orthogonal O
  have hswaple := hmax _ (isUnitary_rotateRows U hU i j hij 0 1 (by norm_num))
  by_contra! hns
  obtain ⟨c, s, hcs, hz⟩ := exists_real_annihilating_rotation (O.val i k) (O.val j k)
  let V := rotateRows U i j c s
  have hV := isUnitary_rotateRows U hU i j hij c s hcs
  have hflat := flat_rotateRows_of_support_max a b η U hU i j hij hmax
    (le_antisymm hswaple hns) c s hcs
  have hi : V i k = 0 := by
    have hh := congrArg (fun x : ℝ => (x : ℂ)) hz
    simpa [V, rotateRows, mixedRows, Matrix.updateRow, hij, U, Pi.smul_apply, smul_eq_mul] using hh
  have hr : V r k = 0 := by
    simp [V, rotateRows, mixedRows, Matrix.updateRow, hri, hrj, U, hzero]
  classical
  have hsub : supportColumns Vᴴ {k} ⊆ (Finset.univ.erase i).erase r := by
    intro p hp
    have hne : V p k ≠ 0 := by
      simpa [supportColumns, Matrix.conjTranspose_apply] using hp
    have hpi : p ≠ i := fun he => hne (he ▸ hi)
    have hpr : p ≠ r := fun he => hne (he ▸ hr)
    simp [hpi, hpr]
  have hcard : ((Finset.univ.erase i).erase r : Finset (Fin 4)).card = 2 := by
    rw [Finset.card_erase_of_mem (by simp [hri]), Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hsparse : (supportColumns Vᴴ {k}).card ≤ 2 := (Finset.card_le_card hsub).trans_eq hcard
  have hholds := holds_of_column_degree_le_two (conjecture_le_three (by omega)) a b hV k hsparse
  obtain ⟨p, hp⟩ := (holds_iff_directional a b V).mp hholds η
  exact (not_lt_of_ge (hflat.symm.le.trans hp)) (hgap p)

end

end MOC
