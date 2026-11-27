import MOC.Support
import MOC.Variational
import Mathlib.Topology.Order.Lattice

/-! The real determinant support test on a compact, anchored spectral domain. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
/-- The largest modulus among both spectral lists. -/
def spectralMaxNorm (a b : ι → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : ι ⊕ ι => ‖Sum.elim a b i‖

omit [DecidableEq ι] in
private theorem norm_le_spectralMaxNorm (a b : ι → ℂ) (i : ι ⊕ ι) :
    ‖Sum.elim a b i‖ ≤ spectralMaxNorm a b :=
  Finset.le_sup' (fun j : ι ⊕ ι => ‖Sum.elim a b j‖) (Finset.mem_univ i)

omit [DecidableEq ι] in
private theorem continuous_spectralMaxNorm :
    Continuous fun p : (ι → ℂ) × (ι → ℂ) => spectralMaxNorm p.1 p.2 := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  rintro (i | i) _ <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

/-- The anchored unit spectral boundary and the unitary group form a compact domain. -/
theorem isCompact_normalized_determinant_domain (j₀ : ι) :
    IsCompact ({p : (ι → ℂ) × (ι → ℂ) | p.2 j₀ = 0 ∧ spectralMaxNorm p.1 p.2 = 1} ×ˢ
      {U : Matrix ι ι ℂ | IsUnitary U}) := by
  let K : Set (ι → ℂ) := Set.univ.pi fun _ => Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hc : IsClosed {p : (ι → ℂ) × (ι → ℂ) |
      p.2 j₀ = 0 ∧ spectralMaxNorm p.1 p.2 = 1} :=
    (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq continuous_spectralMaxNorm continuous_const)
  refine ((hK.prod hK).of_isClosed_subset hc ?_).prod isCompact_setOf_isUnitary
  intro p hp
  refine ⟨Set.mem_pi.mpr fun i _ => ?_, Set.mem_pi.mpr fun i _ => ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_spectralMaxNorm p.1 p.2 (.inl i)).trans_eq hp.2
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_spectralMaxNorm p.1 p.2 (.inr i)).trans_eq hp.2

/-- A fixed partner entry can be set to zero and the largest spectral
modulus set to one in the real support test. -/
theorem conjecture_iff_anchored_unit_spectral_norm (j₀ : ι) :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      b j₀ = 0 → spectralMaxNorm a b = 1 →
      ∃ σ : Equiv.Perm ι, (determinantValue a b U).re ≤ (matchingProduct a b σ).re := by
  rw [conjecture_iff_real_bound]
  constructor
  · intro h a b U hU _ _
    exact h a b U hU
  · intro h a b U hU
    let x := fun i => a i + b j₀
    let y := fun i => b i - b j₀
    suffices ∃ σ : Equiv.Perm ι, (determinantValue x y U).re ≤ (matchingProduct x y σ).re by
      simpa only [x, y, determinantValue_shift a b hU, matchingProduct_shift] using this
    let r := spectralMaxNorm x y
    have hbound (i : ι ⊕ ι) : ‖Sum.elim x y i‖ ≤ r := norm_le_spectralMaxNorm x y i
    by_cases hr : r = 0
    · have hx (i : ι) : x i = 0 := norm_le_zero_iff.mp (hr ▸ hbound (.inl i))
      have hy (i : ι) : y i = 0 := norm_le_zero_iff.mp (hr ▸ hbound (.inr i))
      have hy' : y = 0 := funext hy
      have hd : Matrix.diagonal (0 : ι → ℂ) = (0 : Matrix ι ι ℂ) := Matrix.diagonal_zero
      refine ⟨1, ?_⟩
      unfold determinantValue
      simp only [hy', hd, Matrix.mul_zero,
        Matrix.zero_mul, add_zero, Matrix.det_diagonal]
      simp only [matchingProduct, hx, Pi.zero_apply, add_zero, le_refl]
    · have hrpos : 0 < r := lt_of_le_of_ne ((norm_nonneg _).trans (hbound (.inl j₀))) (Ne.symm hr)
      let x' := fun i => ((r⁻¹ : ℝ) : ℂ) * x i
      let y' := fun i => ((r⁻¹ : ℝ) : ℂ) * y i
      have hy₀ : y' j₀ = 0 := by simp only [y', y, sub_self, mul_zero]
      have hnorm (i : ι ⊕ ι) : ‖Sum.elim x' y' i‖ = r⁻¹ * ‖Sum.elim x y i‖ := by
        cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, x', y', norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos)]
      have hmax : spectralMaxNorm x' y' = 1 := by
        unfold spectralMaxNorm
        apply le_antisymm
        · apply Finset.sup'_le Finset.univ_nonempty
          intro i _
          rw [hnorm, ← inv_mul_cancel₀ hr]
          exact mul_le_mul_of_nonneg_left (hbound i) (inv_nonneg.mpr hrpos.le)
        · obtain ⟨i, _, hri⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
            (fun j : ι ⊕ ι => ‖Sum.elim x y j‖)
          have he : ‖Sum.elim x' y' i‖ = 1 := by
            rw [hnorm, ← hri]
            exact inv_mul_cancel₀ hr
          simpa only [he] using norm_le_spectralMaxNorm x' y' i
      obtain ⟨σ, hσ⟩ := h x' y' U hU hy₀ hmax
      rw [show determinantValue x' y' U = ((r⁻¹ : ℝ) : ℂ) ^ Fintype.card ι *
          determinantValue x y U from determinantValue_scale x y U _,
        show matchingProduct x' y' σ = ((r⁻¹ : ℝ) : ℂ) ^ Fintype.card ι *
          matchingProduct x y σ from matchingProduct_scale x y _ σ] at hσ
      simp only [← Complex.ofReal_pow, Complex.re_ofReal_mul] at hσ
      exact ⟨σ, (mul_le_mul_left (pow_pos (inv_pos.mpr hrpos) _)).mp hσ⟩

end
end MOC
