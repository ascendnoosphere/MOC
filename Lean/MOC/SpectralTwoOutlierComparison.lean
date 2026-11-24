import MOC.TwoOutlierInverseGram
import MOC.FullSupportReduction
import MOC.TwoOutlierZeroSupport

/-! The supporting half-plane at height zero for two imaginary outliers.
The comparison uses positive real spectator endpoints and does not assert
the full determinant hull for these spectra. -/

open Matrix
open scoped ComplexOrder Matrix

namespace MOC
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def spectator (j : ι) (x : ι → ℝ) (k : ι) : ℂ :=
  if k = j then 0 else (x k : ℂ)

private def twoColumns (U : Matrix ι ι ℂ) (j : ι) : Matrix ι (Fin 2) ℂ :=
  Matrix.of fun i => ![(if i = j then 1 else 0 : ℂ), U i j]

private theorem twoColumns_diagonal (U : Matrix ι ι ℂ) (j : ι) (α β : ℂ) :
    twoColumns U j * diagonal ![α, β] * (twoColumns U j)ᴴ =
      diagonal (Pi.single j α) + U * diagonal (Pi.single j β) * Uᴴ := by
  ext i k
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fin.sum_univ_two, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, twoColumns, Matrix.of_apply, Matrix.vecCons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [Finset.sum_eq_single j]
  · by_cases hi : i = j <;> by_cases hk : k = j
    · subst i; subst k; simp
    · subst i; simp [hk, Ne.symm hk, Matrix.diagonal_apply]
    · subst k; simp [hi, Matrix.diagonal_apply]
    · simp [hi, hk, Matrix.diagonal_apply, Pi.single_eq_of_ne hi]
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp

omit [Fintype ι] in
private theorem spectator_const_diagonal (j : ι) (a : ℝ) :
    diagonal (spectator j (fun _ => a)) =
      (a : ℂ) • (1 : Matrix ι ι ℂ) - diagonal (Pi.single j (a : ℂ)) := by
  ext i k
  by_cases hi : i = k
  · subst k
    by_cases hij : i = j
    · subst i; simp [spectator]
    · simp [spectator, hij, Pi.single_eq_of_ne hij]
  · simp [Matrix.diagonal_apply_ne _ hi, Matrix.one_apply_ne hi]

private def spectatorSum (U : Matrix ι ι ℂ) (j : ι) (x y : ι → ℝ) : Matrix ι ι ℂ :=
  diagonal (spectator j x) + U * diagonal (spectator j y) * Uᴴ

private theorem spectatorSum_const (U : Matrix ι ι ℂ) (hU : IsUnitary U) (j : ι) (a b : ℝ) :
    spectatorSum U j (fun _ => a) (fun _ => b) =
      (a + b : ℂ) • (1 : Matrix ι ι ℂ) -
        twoColumns U j * diagonal ![(a : ℂ), (b : ℂ)] * (twoColumns U j)ᴴ := by
  unfold spectatorSum
  rw [twoColumns_diagonal, spectator_const_diagonal, spectator_const_diagonal]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hU.1, add_smul]
  abel

private theorem spectator_posSemidef (j : ι) (a : ι → ℝ)
    (ha : ∀ i, i ≠ j → 0 ≤ a i) : (diagonal (spectator j a)).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases hi : i = j
  · simp [spectator, hi]
  · simpa [spectator, hi] using ha i hi

omit [Fintype ι] in
private theorem spectator_sub (j : ι) (a b : ι → ℝ) :
    spectator j (fun i => a i - b i) = spectator j a - spectator j b := by
  funext i
  by_cases hi : i = j <;> simp [spectator, hi]

private theorem spectatorSum_order (U : Matrix ι ι ℂ) (j : ι)
    (x y a b : ι → ℝ)
    (hx : ∀ i, i ≠ j → a i ≤ x i) (hy : ∀ i, i ≠ j → b i ≤ y i) :
    (spectatorSum U j x y - spectatorSum U j a b).PosSemidef := by
  have hx' := spectator_posSemidef j (fun i => x i - a i) fun i hi => sub_nonneg.mpr (hx i hi)
  have hy' := spectator_posSemidef j (fun i => y i - b i) fun i hi => sub_nonneg.mpr (hy i hi)
  have h := hx'.add (hy'.mul_mul_conjTranspose_same U)
  rw [spectator_sub, spectator_sub, show diagonal (spectator j x - spectator j a) = diagonal (spectator j x) - diagonal (spectator j a) from (Matrix.diagonal_sub _ _).symm, show diagonal (spectator j y - spectator j b) = diagonal (spectator j y) - diagonal (spectator j b) from (Matrix.diagonal_sub _ _).symm,
    Matrix.mul_sub, Matrix.sub_mul] at h
  unfold spectatorSum
  convert h using 1
  abel


omit [Fintype ι] in
private theorem twoColumns_mulVec (U : Matrix ι ι ℂ) (j : ι) (t : Fin 2 → ℂ) (i : ι) :
    (twoColumns U j *ᵥ t) i = (if i = j then 1 else 0) * t 0 + U i j * t 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, twoColumns]

private theorem eq_single_of_spectator_kernel (j : ι) (a : ι → ℝ)
    (ha : ∀ i, i ≠ j → 0 < a i) (t : ι → ℂ)
    (ht : diagonal (spectator j a) *ᵥ t = 0) : t = Pi.single j (t j) := by
  funext i
  by_cases hj : i = j
  · subst i; simp
  · have h := congrFun ht i
    simp only [Matrix.mulVec_diagonal, spectator, if_neg hj, Pi.zero_apply] at h
    have hne : (a i : ℂ) ≠ 0 := by exact_mod_cast (ha i hj).ne'
    simpa [Pi.single_eq_of_ne hj] using (mul_eq_zero.mp h).resolve_left hne

private theorem spectatorSum_posDef (U : Matrix ι ι ℂ) (hU : IsUnitary U) (j : ι)
    (hV : Function.Injective (twoColumns U j).mulVec)
    (a b : ι → ℝ) (ha : ∀ i, i ≠ j → 0 < a i) (hb : ∀ i, i ≠ j → 0 < b i) :
    (spectatorSum U j a b).PosDef := by
  let A := diagonal (spectator j a)
  let B := U * diagonal (spectator j b) * Uᴴ
  have hA : A.PosSemidef := spectator_posSemidef j a fun i hi => (ha i hi).le
  have hB : B.PosSemidef :=
    (spectator_posSemidef j b fun i hi => (hb i hi).le).mul_mul_conjTranspose_same U
  change (A + B).PosDef
  refine ⟨(hA.add hB).1, fun t ht => ?_⟩
  rw [Matrix.add_mulVec, dotProduct_add]
  apply lt_of_le_of_ne (add_nonneg (hA.2 _) (hB.2 _))
  intro he
  have he' := (add_eq_zero_iff_of_nonneg (hA.2 t) (hB.2 t)).mp he.symm
  have heA := (hA.dotProduct_mulVec_zero_iff t).mp he'.1
  have heB := (hB.dotProduct_mulVec_zero_iff t).mp he'.2
  have htA := eq_single_of_spectator_kernel j a ha t heA
  let w := Uᴴ *ᵥ t
  have hB' : diagonal (spectator j b) *ᵥ w = 0 := by
    have h := congrArg (fun v => Uᴴ *ᵥ v) heB
    change Uᴴ *ᵥ ((U * diagonal (spectator j b) * Uᴴ) *ᵥ t) = Uᴴ *ᵥ 0 at h
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← Matrix.mul_assoc Uᴴ,
      ← Matrix.mul_assoc Uᴴ, hU.2, Matrix.one_mul, ← Matrix.mulVec_mulVec] at h
    exact h
  have hw := eq_single_of_spectator_kernel j b hb w hB'
  have htB : t = U *ᵥ Pi.single j (w j) := by
    rw [← hw]
    simp [w, Matrix.mulVec_mulVec, hU.1]
  let tA : Fin 2 → ℂ := ![t j, 0]
  let tB : Fin 2 → ℂ := ![0, w j]
  have hx : twoColumns U j *ᵥ tA = t := by
    funext i
    rw [twoColumns_mulVec]
    suffices h : ↑(if i = j then (1 : ℕ) else 0) * t j = t i by simpa [tA] using h
    have h := congrFun htA i
    by_cases hi : i = j
    · subst i; simp
    · simpa [Pi.single_eq_of_ne hi, hi] using h.symm
  have hy : twoColumns U j *ᵥ tB = t := by
    funext i
    rw [twoColumns_mulVec]
    have h := congrFun htB i
    simpa [Matrix.mulVec_single, tB, mul_comm] using h.symm
  have h := congrFun (hV (hx.trans hy.symm)) 0
  have hj : t j = 0 := by simpa [tA, tB] using h
  exact ht (by simpa [hj] using htA)


private theorem twoColumns_unit (U : Matrix ι ι ℂ) (hU : IsUnitary U) (j : ι) :
    ((twoColumns U j)ᴴ * twoColumns U j) 0 0 = 1 ∧
      ((twoColumns U j)ᴴ * twoColumns U j) 1 1 = 1 := by
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [twoColumns]
    · intro k _ hk
      simp [twoColumns, hk]
    · simp
  · have h := congrFun (congrFun hU.2 j) j
    simpa [Matrix.mul_apply, twoColumns] using h

omit [Fintype ι] in
private theorem twoColumns_injective (U : Matrix ι ι ℂ) (j i : ι)
    (hi : i ≠ j) (hu : U i j ≠ 0) :
    Function.Injective (twoColumns U j).mulVec := by
  intro t s h
  have h₁ := congrFun h i
  simp only [twoColumns_mulVec, if_neg hi, zero_mul, zero_add] at h₁
  have h₁' := mul_left_cancel₀ hu h₁
  have h₀ := congrFun h j
  simp only [twoColumns_mulVec, if_pos rfl, if_true, one_mul, h₁', add_left_inj] at h₀
  exact funext (Fin.forall_fin_two.mpr ⟨h₀, h₁'⟩)

omit [Fintype ι] in
private theorem diagonal_withImaginaryOutlier (a : ι → ℝ) (j : ι) (u : ℝ) :
    diagonal (withImaginaryOutlier a j u) =
      diagonal (spectator j a) + diagonal (Pi.single j (Complex.I * u)) := by
  have addDiag := Matrix.diagonal_add (spectator j a) (Pi.single j (Complex.I * u) : ι → ℂ)
  rw [addDiag]
  apply congrArg diagonal
  funext i
  by_cases hi : i = j
  · subst i
    simp [withImaginaryOutlier, spectator]
  · simp [withImaginaryOutlier, spectator, hi, Pi.single_eq_of_ne hi,
      Function.update_of_ne hi]

private theorem determinantValue_twoOutlier (U : Matrix ι ι ℂ) (j : ι)
    (x y : ι → ℝ) (u v : ℝ) :
    determinantValue (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) U =
      (spectatorSum U j x y +
        twoColumns U j * diagonal ![Complex.I * u, Complex.I * v] * (twoColumns U j)ᴴ).det := by
  unfold determinantValue spectatorSum
  rw [twoColumns_diagonal, diagonal_withImaginaryOutlier, diagonal_withImaginaryOutlier,
    Matrix.mul_add, Matrix.add_mul]
  congr 1
  abel

private theorem twoOutlier_ambient_lower {U : Matrix ι ι ℂ} (hU : IsUnitary U) {j : ι}
    (hV : Function.Injective (twoColumns U j).mulVec)
    (x y : ι → ℝ) (u v a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : ∀ i, i ≠ j → a ≤ x i) (hy : ∀ i, i ≠ j → b ≤ y i)
    (huv : u * v ≤ a * b) :
    0 ≤ (determinantValue (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) U).re := by
  have hx' i hi := ha.trans_le (hx i hi)
  have hy' i hi := hb.trans_le (hy i hi)
  have hH := spectatorSum_posDef U hU j hV x y hx' hy'
  have hR := spectatorSum_posDef U hU j hV (fun _ => a) (fun _ => b) (fun _ _ => ha) (fun _ _ => hb)
  have ⟨h₀, h₁⟩ := twoColumns_unit U hU j
  rw [determinantValue_twoOutlier]
  exact (re_det_two_outliers_of_ambient_comparison _ hH _ hV h₀ h₁ u v a b ha hb _
    (spectatorSum_const U hU j a b) hR).2 (spectatorSum_order U j x y _ _ hx hy) huv

private theorem twoOutlier_ambient_upper {U : Matrix ι ι ℂ} (hU : IsUnitary U) {j : ι}
    (hV : Function.Injective (twoColumns U j).mulVec)
    (x y : ι → ℝ) (u v a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx₀ : ∀ i, i ≠ j → 0 < x i) (hy₀ : ∀ i, i ≠ j → 0 < y i)
    (hx : ∀ i, i ≠ j → x i ≤ a) (hy : ∀ i, i ≠ j → y i ≤ b)
    (huv : a * b ≤ u * v) :
    (determinantValue (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) U).re ≤ 0 := by
  have hH := spectatorSum_posDef U hU j hV x y hx₀ hy₀
  have hR := spectatorSum_posDef U hU j hV (fun _ => a) (fun _ => b) (fun _ _ => ha) (fun _ _ => hb)
  have ⟨h₀, h₁⟩ := twoColumns_unit U hU j
  rw [determinantValue_twoOutlier]
  exact (re_det_two_outliers_of_ambient_comparison _ hH _ hV h₀ h₁ u v a b ha hb _
    (spectatorSum_const U hU j a b) hR).1 (spectatorSum_order U j _ _ x y hx hy) huv


omit [Fintype ι] in
private theorem crossing_outliers_exists (j i k : ι) (hi : i ≠ j) (hk : k ≠ j) :
    ∃ σ : Equiv.Perm ι, σ j = i ∧ σ.symm j = k := by
  let σ := Equiv.swap j i * Equiv.swap k i
  refine ⟨σ, ?_, ?_⟩
  · change Equiv.swap j i (Equiv.swap k i j) = i
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hk) (Ne.symm hi), Equiv.swap_apply_left]
  · apply σ.injective
    rw [Equiv.apply_symm_apply]
    change j = Equiv.swap j i (Equiv.swap k i k)
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]

private theorem crossing_outliers_signs (j : ι) (x y : ι → ℝ) (u v : ℝ)
    (hx : ∀ i, i ≠ j → 0 < x i) (hy : ∀ i, i ≠ j → 0 < y i)
    (i k : ι) (hi : i ≠ j) (hk : k ≠ j) :
    ∃ σ : Equiv.Perm ι, ∃ p : ℝ, 0 < p ∧
      (matchingProduct (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) σ).re =
        (x i * y k - u * v) * p := by
  obtain ⟨σ, hs, ht⟩ := crossing_outliers_exists j i k hi hk
  refine ⟨σ, ∏ t ∈ (Finset.univ.erase j).erase (σ.symm j), (x (σ t) + y t), ?_, ?_⟩
  · apply Finset.prod_pos
    intro t h
    have h₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1
    have h₂ := (Finset.mem_erase.mp h).1
    have h₃ : σ t ≠ j := fun e => h₂ (σ.injective (e.trans (σ.apply_symm_apply j).symm))
    exact add_pos (hx _ h₃) (hy _ h₁)
  · rw [matchingProduct_two_outliers_real, if_neg (hs.trans_ne hi), hs, ht]

/-- For positive real spectators on both sides, if the imaginary axis
supports the matching products, it supports the determinant for every
unitary mixer. The use of both inequalities allows either orientation of
the supporting half-plane. The matrix size is arbitrary. -/
theorem two_imaginary_outliers_zero_support [Nontrivial ι]
    (j : ι) (x y : ι → ℝ) (u v : ℝ)
    (hx : ∀ i, i ≠ j → 0 < x i) (hy : ∀ i, i ≠ j → 0 < y i)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ((∀ σ, (matchingProduct (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) σ).re ≤ 0) →
      (determinantValue (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) U).re ≤ 0) ∧
    ((∀ σ, 0 ≤ (matchingProduct (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) σ).re) →
      0 ≤ (determinantValue (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) U).re) := by
  classical
  obtain ⟨i, hi⟩ := exists_ne j
  let S : Finset ι := Finset.univ.erase j
  have hS : S.Nonempty := ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩⟩
  let D (V : Matrix ι ι ℂ) :=
    (determinantValue (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) V).re
  have hD : Continuous D := by unfold D determinantValue; fun_prop
  constructor
  · intro hall
    obtain ⟨r, hr, hrmax⟩ := Finset.exists_max_image S x hS
    obtain ⟨s, hs, hsmax⟩ := Finset.exists_max_image S y hS
    have hrj := (Finset.mem_erase.mp hr).1
    have hsj := (Finset.mem_erase.mp hs).1
    obtain ⟨σ, p, hp, he⟩ := crossing_outliers_signs j x y u v hx hy r s hrj hsj
    have huv : x r * y s ≤ u * v := by
      have hh := hall σ
      rw [he] at hh
      apply le_of_not_gt
      intro hv
      exact (not_lt_of_ge hh) (mul_pos (sub_pos.mpr hv) hp)
    change D U ≤ 0
    by_contra! hbad
    have hO : IsOpen {V : Matrix ι ι ℂ | 0 < D V} := isOpen_lt continuous_const hD
    obtain ⟨V, hV, hVunit, hfull⟩ := exists_full_support_unitary_mem_open hO U hU hbad
    exact (not_lt_of_ge (twoOutlier_ambient_upper hVunit (twoColumns_injective V j i hi (hfull i j))
      x y u v (x r) (y s) (hx r hrj) (hy s hsj) hx hy
      (fun k hk => hrmax k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩))
      (fun k hk => hsmax k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)) huv)) hV
  · intro hall
    obtain ⟨r, hr, hrmin⟩ := Finset.exists_min_image S x hS
    obtain ⟨s, hs, hsmin⟩ := Finset.exists_min_image S y hS
    have hrj := (Finset.mem_erase.mp hr).1
    have hsj := (Finset.mem_erase.mp hs).1
    obtain ⟨σ, p, hp, he⟩ := crossing_outliers_signs j x y u v hx hy r s hrj hsj
    have huv : u * v ≤ x r * y s := by
      have hh := hall σ
      rw [he] at hh
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hp).mp hh)
    change 0 ≤ D U
    by_contra! hbad
    have hO : IsOpen {V : Matrix ι ι ℂ | D V < 0} := isOpen_lt hD continuous_const
    obtain ⟨V, hV, hVunit, hfull⟩ := exists_full_support_unitary_mem_open hO U hU hbad
    exact (not_lt_of_ge (twoOutlier_ambient_lower hVunit (twoColumns_injective V j i hi (hfull i j))
      x y u v (x r) (y s) (hx r hrj) (hy s hsj)
      (fun k hk => hrmin k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩))
      (fun k hk => hsmin k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)) huv)) hV

end
end MOC
