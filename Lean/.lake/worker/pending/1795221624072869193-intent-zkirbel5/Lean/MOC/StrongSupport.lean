import MOC.Geometry
import MOC.NormalOrbit
import Mathlib.Tactic.Linarith

/-! A strict support violation in a compact set admits a supporting disk.
Its tangent functional gives an exact quadratic penalty. -/

open Filter Matrix
open scoped ComplexConjugate Topology

namespace MOC

/-- A uniform strict gap from the test points can be preserved while choosing
a maximizer with a quadratic support penalty on the whole compact set. -/
theorem exists_quadratic_support {K P : Set ℂ} (hK : IsCompact K) (hP : P ⊆ K)
    {z₀ : ℂ} (hz₀ : z₀ ∈ K) (η : ℂ) (g : ℝ) (hg : 0 < g)
    (hgap : ∀ w ∈ P, g ≤ (η * z₀).re - (η * w).re) :
    ∃ z ∈ K, ∃ ξ : ℂ,
      (∀ w ∈ P, (η * w).re < (η * z).re) ∧
      (∀ w ∈ P, (ξ * (w - z)).re < 0) ∧
      ∀ w ∈ K, (ξ * (w - z)).re ≤ -Complex.normSq (w - z) / 2 := by
  obtain ⟨zmax, _, hbound⟩ :=
    hK.exists_isMaxOn ⟨z₀, hz₀⟩ Complex.continuous_normSq.continuousOn
  let M := Complex.normSq zmax
  let L := (M + 1) / (2 * g)
  have hL : 0 < L := div_pos
    (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg zmax) zero_lt_one) (by positivity)
  have hLg : 2 * L * g = M + 1 := calc
    _ = L * (2 * g) := by ring
    _ = _ := div_mul_cancel₀ (M + 1) (mul_ne_zero two_ne_zero hg.ne')
  let f (w : ℂ) : ℝ := Complex.normSq w + 2 * L * (η * w).re
  have hf : Continuous f := by
    dsimp [f]
    exact Complex.continuous_normSq.add (continuous_const.mul (by fun_prop))
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨z₀, hz₀⟩ hf.continuousOn
  let ξ := conj z + (L : ℂ) * η
  have hsep (w : ℂ) (hw : w ∈ P) : (η * w).re < (η * z).re := by
    by_contra! hb
    have hproj := (hgap w hw).trans (sub_le_sub_left hb (η * z₀).re)
    have hmul := mul_le_mul_of_nonneg_left hproj (show 0 ≤ 2 * L by positivity)
    have hfmax := hmax hz₀
    change Complex.normSq z₀ + 2 * L * (η * z₀).re ≤
      Complex.normSq z + 2 * L * (η * z).re at hfmax
    have hMz : Complex.normSq z ≤ M := hbound hz
    nlinarith only [hmul, hLg, hfmax, hMz, Complex.normSq_nonneg z₀]
  have hpenalty (w : ℂ) (hw : w ∈ K) :
      (ξ * (w - z)).re ≤ -Complex.normSq (w - z) / 2 := by
    have he : f w = f z + 2 * (ξ * (w - z)).re + Complex.normSq (w - z) := by
      simp only [f, ξ, Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hwmax := hmax hw
    change f w ≤ f z at hwmax
    rw [he] at hwmax
    linarith only [hwmax]
  refine ⟨z, hz, ξ, hsep, ?_, hpenalty⟩
  intro w hw
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr fun he =>
    (ne_of_lt (hsep w hw)) (congrArg (fun x : ℂ => (η * x).re) he)
  exact (hpenalty w (hP hw)).trans_lt (by linarith only [Complex.normSq_pos.mpr hwz])

/-- The quadratic penalty bounds the second-order support coefficient of a
curve in terms of its first derivative. -/
theorem second_order_le_of_quadratic_support (f : ℝ → ℂ) (z ξ d : ℂ) (q : ℝ)
    (hpenalty : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      (ξ * (f t - z)).re ≤ -Complex.normSq (f t - z) / 2)
    (hd : Tendsto (fun t : ℝ => (f t - z) / (t : ℂ)) (𝓝[≠] 0) (𝓝 d))
    (hq : Tendsto (fun t : ℝ => (ξ * (f t - z)).re / t ^ 2) (𝓝[≠] 0) (𝓝 q)) :
    q ≤ -Complex.normSq d / 2 := by
  have hr : Tendsto (fun t : ℝ => -Complex.normSq ((f t - z) / (t : ℂ)) / 2)
      (𝓝[≠] 0) (𝓝 (-Complex.normSq d / 2)) :=
    (Complex.continuous_normSq.continuousAt.tendsto.comp hd).neg.div_const 2
  refine le_of_tendsto_of_tendsto hq hr ?_
  filter_upwards [hpenalty] with t ht
  calc
    _ ≤ (-Complex.normSq (f t - z) / 2) / t ^ 2 :=
      div_le_div_of_nonneg_right ht (sq_nonneg t)
    _ = _ := by
      rw [Complex.normSq_div, Complex.normSq_ofReal, ← pow_two]
      ring

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem permMatrix_conjugates (σ : Equiv.Perm ι) (M : Matrix ι ι ℂ) :
    σ.permMatrix ℂ * M * (σ.permMatrix ℂ)ᴴ = M.submatrix σ σ := by
  rw [Matrix.conjTranspose_permMatrix]
  change (σ.toPEquiv.toMatrix : Matrix ι ι ℂ) * M * (σ⁻¹).toPEquiv.toMatrix = _
  simp only [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp,
    Equiv.Perm.inv_def, Equiv.symm_symm]

private theorem matchingProduct_mem_determinantRange (a b : ι → ℂ) (σ : Equiv.Perm ι) :
    matchingProduct a b σ ∈ determinantRange a b := by
  have hright (τ : Equiv.Perm ι) :
      τ.permMatrix ℂ * (τ.permMatrix ℂ)ᴴ = 1 := by
    simpa only [Matrix.mul_one, Matrix.submatrix_one_equiv] using
      permMatrix_conjugates τ (1 : Matrix ι ι ℂ)
  have hu (τ : Equiv.Perm ι) : IsUnitary (τ.permMatrix ℂ) := by
    refine ⟨hright τ, ?_⟩
    rw [Matrix.conjTranspose_permMatrix]
    simpa only [Matrix.conjTranspose_permMatrix, inv_inv] using hright τ⁻¹
  refine ⟨Equiv.Perm.permMatrix ℂ σ.symm, hu σ.symm, ?_⟩
  rw [determinantValue, permMatrix_conjugates, Matrix.submatrix_diagonal_equiv,
    Matrix.diagonal_add, Matrix.det_diagonal]
  simpa only [Function.comp_apply, Equiv.symm_symm] using (matchingProduct_inverse a b σ.symm).symm

/-- A determinant support violation has a unitary witness with a quadratic
support penalty. A Frobenius maximizer among its support ties retains that penalty. -/
theorem exists_quadratic_support_frobenius_maximizer (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ)
    (hsep : ∀ σ : Equiv.Perm ι,
      (η * matchingProduct a b σ).re < (η * determinantValue a b U).re) :
    ∃ V : Matrix ι ι ℂ, ∃ ξ : ℂ, IsUnitary V ∧
      (∀ σ : Equiv.Perm ι,
        (ξ * matchingProduct a b σ).re < (ξ * determinantValue a b V).re) ∧
      (∀ W : Matrix ι ι ℂ, IsUnitary W →
        (ξ * (determinantValue a b W - determinantValue a b V)).re ≤
        -Complex.normSq (determinantValue a b W - determinantValue a b V) / 2) ∧
      ∀ W : Matrix ι ι ℂ, IsUnitary W →
        (ξ * determinantValue a b W).re = (ξ * determinantValue a b V).re →
        frobeniusSq (diagonal a + W * diagonal b * Wᴴ) ≤
          frobeniusSq (diagonal a + V * diagonal b * Vᴴ) := by
  classical
  have hc : Continuous (determinantValue a b) := by unfold determinantValue; fun_prop
  have hK : IsCompact (determinantRange a b) :=
    isCompact_setOf_isUnitary.image hc
  have hP : Set.range (matchingProduct a b) ⊆ determinantRange a b := by
    rintro _ ⟨σ, rfl⟩
    exact matchingProduct_mem_determinantRange a b σ
  obtain ⟨σ₀, _, hσ₀⟩ := Finset.exists_max_image Finset.univ
    (fun σ : Equiv.Perm ι => (η * matchingProduct a b σ).re)
    ⟨Equiv.refl ι, Finset.mem_univ _⟩
  let z₀ := determinantValue a b U
  let g := (η * z₀).re - (η * matchingProduct a b σ₀).re
  have hg : 0 < g := sub_pos.mpr (hsep σ₀)
  have hgap : ∀ w ∈ Set.range (matchingProduct a b), g ≤ (η * z₀).re - (η * w).re := by
    rintro _ ⟨σ, rfl⟩
    exact sub_le_sub_left (hσ₀ σ (Finset.mem_univ _)) _
  obtain ⟨z, ⟨Z, hZ, rfl⟩, ξ, _, hstrict, hpenalty⟩ :=
    exists_quadratic_support hK hP ⟨U, hU, rfl⟩ η g hg hgap
  obtain ⟨V, hV, hmax, htie⟩ := exists_support_frobenius_maximizer a b ξ
  have heq : determinantValue a b V = determinantValue a b Z := by
    have hle := hpenalty _ ⟨V, hV, rfl⟩
    rw [mul_sub, Complex.sub_re] at hle
    have hz : Complex.normSq (determinantValue a b V - determinantValue a b Z) = 0 :=
      le_antisymm (by linarith only [hle, hmax Z hZ]) (Complex.normSq_nonneg _)
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)
  refine ⟨V, ξ, hV, ?_, ?_, htie⟩
  · intro σ
    rw [heq]
    have hs := hstrict (matchingProduct a b σ) ⟨σ, rfl⟩
    rw [mul_sub, Complex.sub_re] at hs
    exact sub_neg.mp hs
  · intro W hW
    rw [heq]
    exact hpenalty _ ⟨W, hW, rfl⟩

end

end MOC
