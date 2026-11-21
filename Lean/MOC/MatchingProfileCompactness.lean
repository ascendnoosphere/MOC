import MOC.Core
import MOC.MatchingPotential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix

/-! A normalized rank-two matching profile has a bounded kernel
representative, including when entries of the kernel are zero. -/

open BigOperators Matrix
open scoped NNReal

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product of kernel entries selected by a matching. -/
def kernelMatchingProduct (K : Matrix ι ι ℂ) (σ : Equiv.Perm ι) : ℂ :=
  ∏ j, K (σ j) j

/-- Rank at most two, expressed by the vanishing of all three-row minors. -/
def VanishingThreeMinors (K : Matrix ι ι ℂ) : Prop :=
  ∀ p q : Fin 3 → ι, (K.submatrix p q).det = 0

theorem threeMinors_reweight (K : Matrix ι ι ℂ) (a b : ι → ℂ)
    (hK : VanishingThreeMinors K) :
    VanishingThreeMinors (Matrix.of fun i j => a i * K i j * b j) := by
  intro p q
  let C : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun i j => b (q j) * K (p i) (q j)
  have he : (Matrix.of fun i j => a i * K i j * b j).submatrix p q =
      Matrix.of (fun i j => a (p i) * C i j) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, C]
    ring
  rw [he, Matrix.det_mul_column]
  have hc : C.det = 0 := by
    change (Matrix.of fun i j => b (q j) * (K.submatrix p q) i j).det = 0
    rw [Matrix.det_mul_row, hK p q, mul_zero]
  rw [hc, mul_zero]

/-- A largest matching equal to the diagonal permits a representative
in the closed unit disk in every entry. Diagonal similarity preserves all
matching products and all zero three-row minors. -/
theorem exists_bounded_kernel_of_normalized_profile (K : Matrix ι ι ℂ)
    (hd : ∀ i, K i i = 1) (hK : VanishingThreeMinors K)
    (hp : ∀ σ : Equiv.Perm ι, ‖kernelMatchingProduct K σ‖ ≤ 1) :
    ∃ M : Matrix ι ι ℂ, (∀ i j, ‖M i j‖ ≤ 1) ∧ (∀ i, M i i = 1) ∧
      VanishingThreeMinors M ∧ kernelMatchingProduct M = kernelMatchingProduct K := by
  have hp' (σ : Equiv.Perm ι) : ‖∏ i, K i (σ i)‖ ≤ 1 := by
    have he : (∏ i, K i (σ i)) = kernelMatchingProduct K σ.symm := by
      unfold kernelMatchingProduct
      rw [← Equiv.prod_comp σ (fun j => K (σ.symm j) j)]
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [he]
    exact hp _
  obtain ⟨s, hs, hsb⟩ := exists_matching_norm_potential K hd hp'
  let d (i : ι) : ℂ := (s i : ℝ)
  have hpos (i : ι) : 0 < (s i : ℝ) := zero_lt_one.trans_le (by exact_mod_cast hs i)
  have hd' (i : ι) : d i ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos i).ne'
  let M : Matrix ι ι ℂ := Matrix.of fun i j => (d i)⁻¹ * K i j * d j
  refine ⟨M, ?_, ?_, threeMinors_reweight K (fun i => (d i)⁻¹) d hK, ?_⟩
  · intro i j
    change ‖(d i)⁻¹ * K i j * d j‖ ≤ 1
    simp only [norm_mul, norm_inv, d, Complex.norm_real, Real.norm_of_nonneg (hpos _).le]
    rw [inv_mul_eq_div, div_mul_eq_mul_div]
    exact (div_le_one₀ (hpos i)).mpr (by exact_mod_cast hsb i j)
  · intro i
    change (d i)⁻¹ * K i i * d i = 1
    rw [hd, mul_one, inv_mul_cancel₀ (hd' i)]
  · funext σ
    simp only [kernelMatchingProduct, M, Matrix.of_apply, Finset.prod_mul_distrib,
      Equiv.prod_comp σ (fun i => (d i)⁻¹), Finset.prod_inv_distrib]
    have hnz : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hd' i
    rw [mul_right_comm, inv_mul_cancel₀ hnz, one_mul]

/-- Relative to a modulus-maximizing diagonal, the normalized rank-two
matching profiles form a compact set. -/
theorem isCompact_normalized_rankTwo_matching_profiles :
    IsCompact {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
      (∀ i, K i i = 1) ∧ VanishingThreeMinors K ∧
        (∀ σ, ‖p σ‖ ≤ 1) ∧ kernelMatchingProduct K = p} := by
  let C : Set (Matrix ι ι ℂ) := Set.univ.pi fun _ =>
    Set.univ.pi fun _ => Metric.closedBall 0 1
  let H : Set (Matrix ι ι ℂ) := {K | (∀ i, K i i = 1) ∧ VanishingThreeMinors K}
  have hC : IsCompact C := isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hH : IsClosed H := by
    have hd : IsClosed {K : Matrix ι ι ℂ | ∀ i, K i i = 1} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_eq (continuous_id.matrix_elem i i) continuous_const
    have hm : IsClosed {K : Matrix ι ι ℂ | VanishingThreeMinors K} := by
      unfold VanishingThreeMinors
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ continuous_const
      exact (continuous_id.matrix_submatrix a b).matrix_det
    exact hd.inter hm
  have hc : Continuous (kernelMatchingProduct (ι := ι)) := by
    apply continuous_pi
    intro σ
    exact continuous_finset_prod _ (fun j _ => continuous_id.matrix_elem (σ j) j)
  have himage : kernelMatchingProduct '' (C ∩ H) =
      {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
        (∀ i, K i i = 1) ∧ VanishingThreeMinors K ∧
          (∀ σ, ‖p σ‖ ≤ 1) ∧ kernelMatchingProduct K = p} := by
    ext p
    constructor
    · rintro ⟨K, ⟨hbound, hd, hK⟩, rfl⟩
      refine ⟨K, hd, hK, ?_, rfl⟩
      intro σ
      rw [kernelMatchingProduct, norm_prod]
      refine Finset.prod_le_one (fun j _ => norm_nonneg _) fun j _ => ?_
      have h := Set.mem_pi.mp (Set.mem_pi.mp hbound (σ j) (Set.mem_univ _))
        j (Set.mem_univ _)
      simpa only [Metric.mem_closedBall, dist_zero_right] using h
    · rintro ⟨K, hd, hK, hp, rfl⟩
      obtain ⟨M, hbound, hd', hM, hm⟩ := exists_bounded_kernel_of_normalized_profile K hd hK hp
      refine ⟨M, ⟨?_, hd', hM⟩, hm⟩
      refine Set.mem_pi.mpr fun i _ => Set.mem_pi.mpr fun j _ => ?_
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbound i j
  rw [← himage]
  exact (hC.inter_right hH).image hc

end MOC
