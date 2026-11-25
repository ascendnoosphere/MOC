import MOC.ContactCensus
import MOC.SupportedWeights
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Lattice

/-! At order four a trace projection supporting every derangement forces
collinearity when one spectrum is injective. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem off_diagonal_additive_of_derangements (c : Fin 4 → Fin 4 → ℝ) (t : ℝ)
    (h : ∀ σ : FourPerm, (∀ j, σ j ≠ j) → (∑ j, c (σ j) j) = t) :
    ∃ r s : Fin 4 → ℝ, ∀ i j, i ≠ j → c i j = r i + s j := by
  let r : Fin 4 → ℝ := ![0, c 1 2 - c 0 2, c 2 1 - c 0 1, c 3 1 - c 0 1]
  let s : Fin 4 → ℝ := ![c 1 0 - r 1, c 0 1, c 0 2, c 0 3]
  have h7 := h (fourPerm 7) (by decide +kernel)
  have h9 := h (fourPerm 9) (by decide +kernel)
  have h10 := h (fourPerm 10) (by decide +kernel)
  have h13 := h (fourPerm 13) (by decide +kernel)
  have h16 := h (fourPerm 16) (by decide +kernel)
  have h17 := h (fourPerm 17) (by decide +kernel)
  have h18 := h (fourPerm 18) (by decide +kernel)
  have h22 := h (fourPerm 22) (by decide +kernel)
  have h23 := h (fourPerm 23) (by decide +kernel)
  simp only [Fin.sum_univ_four] at h7 h9 h10 h13 h16 h17 h18 h22 h23
  change c 1 0 + c 0 1 + c 3 2 + c 2 3 = t at h7
  change c 1 0 + c 2 1 + c 3 2 + c 0 3 = t at h9
  change c 1 0 + c 3 1 + c 0 2 + c 2 3 = t at h10
  change c 2 0 + c 0 1 + c 3 2 + c 1 3 = t at h13
  change c 2 0 + c 3 1 + c 0 2 + c 1 3 = t at h16
  change c 2 0 + c 3 1 + c 1 2 + c 0 3 = t at h17
  change c 3 0 + c 0 1 + c 1 2 + c 2 3 = t at h18
  change c 3 0 + c 2 1 + c 0 2 + c 1 3 = t at h22
  change c 3 0 + c 2 1 + c 1 2 + c 0 3 = t at h23
  refine ⟨r, s, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | simp [r, s] <;> linarith only [h7, h9, h10, h13, h16, h17, h18, h22, h23]

/-- A projected assignment cost attaining its minimum on every derangement
forces the second spectrum onto a line when the first spectrum has no repeats. -/
theorem second_spectrum_collinear_of_derangements_minimize (a b : Fin 4 → ℂ)
    (η : ℂ) (hη : η ≠ 0) (ha : Function.Injective a) (m : ℝ)
    (hmin : ∀ σ : FourPerm, m ≤ ∑ j, (η * (a (σ j) * b j)).re)
    (hder : ∀ σ : FourPerm, (∀ j, σ j ≠ j) → (∑ j, (η * (a (σ j) * b j)).re) = m) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∃ t : ℝ, ∀ j, (κ * b j).re = t := by
  classical
  let c (i j : Fin 4) := (η * (a i * b j)).re
  obtain ⟨r, s, hadd⟩ := off_diagonal_additive_of_derangements c m hder
  let d (i : Fin 4) := c i i - (r i + s i)
  let base := (∑ i, r i) + ∑ j, s j
  have hentry (i j : Fin 4) : c i j = r i + s j + (if i = j then d j else 0) := by
    by_cases h : i = j
    · subst i
      simp [d]
    · simp [h, hadd i j h]
  have hcost (σ : FourPerm) : (∑ j, c (σ j) j) = base + ∑ j, if σ j = j then d j else 0 := by
    simp only [hentry, Finset.sum_add_distrib, base, Equiv.sum_comp σ r]
  have h7 : ∀ j, fourPerm 7 j ≠ j := by decide +kernel
  have hbase : base = m := by
    have h := hder (fourPerm 7) h7
    change (∑ j, c (fourPerm 7 j) j) = m at h
    simpa only [hcost, h7, if_false, Finset.sum_const_zero,
      add_zero] using h
  have hdnonneg (i : Fin 4) : 0 ≤ d i := by
    have hfixed : ∀ i : Fin 4, ∃ k : Fin 24, ∀ j, fourPerm k j = j ↔ j = i := by
      decide +kernel
    obtain ⟨k, hk⟩ := hfixed i
    have hi := hmin (fourPerm k)
    change m ≤ ∑ j, c (fourPerm k j) j at hi
    simp only [hcost, hk, Finset.sum_ite_eq', Finset.mem_univ, if_true, hbase] at hi
    linarith only [hi]
  let f (i : Fin 4) : ℝ × ℂ := (1, a i)
  have hdep : ¬ LinearIndependent ℝ f := by
    intro h
    have hcard := h.fintype_card_le_finrank
    norm_num [Fintype.card_fin, Module.finrank_prod, Complex.finrank_real_complex] at hcard
  obtain ⟨v, hv, i, hvi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hvsum : (∑ i, v i) = 0 := by
    simpa [Prod.fst_sum, f] using congrArg Prod.fst hv
  have hvcomb : (∑ i, v i • a i) = 0 := by
    simpa [Prod.snd_sum, f] using congrArg Prod.snd hv
  obtain ⟨j, hji, hvj⟩ : ∃ j, j ≠ i ∧ v j ≠ 0 := by
    apply Classical.byContradiction
    intro hnone
    have hz (j : Fin 4) (hj : j ≠ i) : v j = 0 :=
      Classical.byContradiction (fun hn => hnone ⟨j, hj, hn⟩)
    have hs : (∑ j, v j) = v i := Finset.sum_eq_single i (fun j _ hj => hz j hj)
      (fun hi => (hi (Finset.mem_univ i)).elim)
    exact hvi (hs.symm.trans hvsum)
  have hsumcol (j : Fin 4) : (∑ i, v i * c i j) = 0 := calc
    _ = (η * ((∑ i, v i • a i) * b j)).re := by
      simp only [Complex.real_smul, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      change v i * (η * (a i * b j)).re = _
      rw [← Complex.re_ofReal_mul]
      congr 1
      ring
    _ = 0 := by rw [hvcomb, zero_mul, mul_zero, Complex.zero_re]
  let vr := ∑ i, v i * r i
  have hcolumn (j : Fin 4) : vr + v j * d j = 0 := by
    have hz := hsumcol j
    simp only [hentry, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
      ← Finset.sum_mul, hvsum, zero_mul, add_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hz
    exact hz
  have hcancel : (∑ j, v j ^ 2 * d j) = 0 := by
    have h : (∑ j, v j * (vr + v j * d j)) = ∑ j, v j * 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun q : ℝ => v j * q) (hcolumn j)
    simpa only [mul_add, mul_zero, Finset.sum_add_distrib, ← Finset.sum_mul, hvsum,
      zero_mul, zero_add, Finset.sum_const_zero, pow_two, mul_assoc] using h
  have hdz (i : Fin 4) (hvi : v i ≠ 0) : d i = 0 := by
    have hle : v i ^ 2 * d i ≤ ∑ j, v j ^ 2 * d j :=
      Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg _) (hdnonneg j)) (Finset.mem_univ i)
    rw [hcancel] at hle
    exact (mul_eq_zero.mp (le_antisymm hle (mul_nonneg (sq_nonneg _) (hdnonneg i)))).resolve_left
      (pow_ne_zero 2 hvi)
  have hrow (i : Fin 4) (hvi : v i ≠ 0) (j : Fin 4) : c i j = r i + s j := by
    by_cases h : i = j
    · subst j
      simpa only [hdz i hvi, ite_self, add_zero] using hentry i i
    · exact hadd i j h
  refine ⟨η * (a i - a j), mul_ne_zero hη (sub_ne_zero.mpr (fun h => hji (ha h).symm)),
    r i - r j, fun k => ?_⟩
  rw [show η * (a i - a j) * b k = η * (a i * b k) - η * (a j * b k) by ring,
    Complex.sub_re]
  change c i k - c j k = _
  rw [hrow i hvi, hrow j hvj]
  ring

private theorem derangements_minimize_of_trace_min (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hsupport : ∀ i j, i ≠ j → U i j ≠ 0) (η : ℂ)
    (hmin : ∀ σ : FourPerm, (η * (diagonal a * (U * diagonal b * Uᴴ)).trace).re ≤
      ∑ j, (η * (a (σ j) * b j)).re) (σ : FourPerm) (hσ : ∀ j, σ j ≠ j) :
    (∑ j, (η * (a (σ j) * b j)).re) = (η * (diagonal a * (U * diagonal b * Uᴴ)).trace).re := by
  classical
  let c (i j : Fin 4) := (η * (a i * b j)).re
  let D : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (fun j i => Complex.normSq (U i j))
  let F : Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] ℝ :=
    ∑ j : Fin 4, ∑ i : Fin 4, c i j • Matrix.entryLinearMap ℝ ℝ j i
  let m := (η * (diagonal a * (U * diagonal b * Uᴴ)).trace).re
  have hF (M : Matrix (Fin 4) (Fin 4) ℝ) : F M = ∑ j, ∑ i, c i j * M j i := by
    simp only [F, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.entryLinearMap_apply, smul_eq_mul]
  have hperm (τ : FourPerm) (j i : Fin 4) : τ.permMatrix ℝ j i = (if τ j = i then 1 else 0) := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]
  have hFp (τ : FourPerm) : F (τ.permMatrix ℝ) = ∑ j, c (τ j) j := by
    rw [hF]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hperm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hFD : F D = m := by
    rw [hF, Finset.sum_comm]
    simp only [m, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_apply]
    simp only [D, Matrix.of_apply, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [c]
    rw [mul_comm, ← Complex.re_ofReal_mul]
    congr 1
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
    ring
  have hD : D ∈ doublyStochastic ℝ (Fin 4) := normSq_transpose_doublyStochastic U hU
  have hminF (τ : FourPerm) : F D ≤ F (τ.permMatrix ℝ) := by
    rw [hFD, hFp]
    exact hmin τ
  have hpos (j : Fin 4) : 0 < D j (σ j) :=
    Complex.normSq_pos.mpr (hsupport _ _ (hσ j))
  have he := linearMap_eq_of_birkhoff_min hD F hminF σ hpos
  rwa [hFp, hFD] at he

/-- The trace-of-product point has a positive support margin in every unit
direction once all off-diagonal entries of the eigenbasis are nonzero,
the first spectrum is injective, and the second is noncollinear. -/
theorem four_trace_margin_of_off_diagonal_support (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hsupport : ∀ i j, i ≠ j → U i j ≠ 0) (ha : Function.Injective a)
    (hb : ∀ κ : ℂ, κ ≠ 0 → ¬ ∃ t : ℝ, ∀ j, (κ * b j).re = t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℂ, ‖η‖ = 1 → ∃ σ : FourPerm,
      δ ≤ (η * ((diagonal a * (U * diagonal b * Uᴴ)).trace - ∑ j, a (σ j) * b j)).re := by
  classical
  let diff (σ : FourPerm) := (diagonal a * (U * diagonal b * Uᴴ)).trace - ∑ j, a (σ j) * b j
  let f (σ : FourPerm) (η : ℂ) := (η * diff σ).re
  have hpos (η : ℂ) (hη : η ≠ 0) : ∃ σ : FourPerm, 0 < f σ η := by
    by_contra! h
    have hmin (σ : FourPerm) : (η * (diagonal a * (U * diagonal b * Uᴴ)).trace).re ≤
        ∑ j, (η * (a (σ j) * b j)).re := by
      have hs := h σ
      simp only [f, diff, mul_sub, Complex.sub_re, sub_nonpos, Finset.mul_sum, Complex.re_sum] at hs
      exact hs
    obtain ⟨κ, hκ, ht⟩ := second_spectrum_collinear_of_derangements_minimize a b η hη ha _ hmin
      (fun σ hσ => derangements_minimize_of_trace_min a b U hU hsupport η hmin σ hσ)
    exact hb κ hκ ht
  let G (η : ℂ) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun σ => f σ η)
  have hG : Continuous G := Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun σ _ => Complex.continuous_re.comp (continuous_id.mul continuous_const))
  have hS : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp [Metric.mem_sphere, dist_zero_right]⟩
  obtain ⟨η₀, hη₀, hmin⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMinOn hS hG.continuousOn
  have hη₀ne : η₀ ≠ 0 := by rintro rfl; simp [Metric.mem_sphere] at hη₀
  obtain ⟨σ₀, hσ₀⟩ := hpos η₀ hη₀ne
  have hGpos : 0 < G η₀ := hσ₀.trans_le (Finset.le_sup' (fun σ => f σ η₀) (Finset.mem_univ σ₀))
  refine ⟨G η₀, hGpos, fun η hη => ?_⟩
  have hSη : η ∈ Metric.sphere (0 : ℂ) 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hη
  have hle : G η₀ ≤ G η := hmin hSη
  obtain ⟨σ, _, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun σ => f σ η)
  change G η = f σ η at he
  rw [he] at hle
  exact ⟨σ, hle⟩

end

end MOC
