import MOC.TripleOrbit
import MOC.ProjectiveTransport
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix BigOperators ComplexOrder
namespace MOC
noncomputable section

/-- A regular projective change of the signed spectra preserves the
complete labelled bipartite graph of zero cross-sums. -/
theorem fractional_add_eq_zero_iff (α β γ δ x y : ℂ)
    (h : α * δ - β * γ ≠ 0)
    (hx : γ * x + δ ≠ 0) (hy : γ * (-y) + δ ≠ 0) :
    fractionalMap α β γ δ x + -fractionalMap α β γ δ (-y) = 0 ↔ x + y = 0 := by
  rw [← sub_neg_eq_add x y]
  simp only [← sub_eq_add_neg, sub_eq_zero]
  exact ⟨fun hxy => fractionalMap_injOn α β γ δ h hx hy hxy,
    fun hxy => congrArg (fractionalMap α β γ δ) hxy⟩

/-- Equal projective additive kernels have only the common scaling and
opposite-translation ambiguity. Both label sets must be inhabited. -/
theorem additive_kernel_scale_translation {ι κ : Type*}
    (i₀ : ι) (j₀ : κ) (a a' : ι → ℂ) (b b' : κ → ℂ) (c : ℂ)
    (h : ∀ i j, a' i + b' j = c * (a i + b j)) :
    ∃ t : ℂ, (∀ i, a' i = c * a i + t) ∧ (∀ j, b' j = c * b j - t) := by
  refine ⟨c * b j₀ - b' j₀, ?_, ?_⟩
  · intro i
    linear_combination h i j₀
  · intro j
    linear_combination h i₀ j - h i₀ j₀

private theorem psd_column_zero_of_diag_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (j : ι) (hj : A j j = 0) :
    ∀ i, A i j = 0 := by
  have hh := (hA.dotProduct_mulVec_zero_iff (Pi.single j 1)).mp (by
    simpa only [← Pi.single_star, star_one, mulVec_single_one, single_dotProduct, one_mul] using hj)
  intro i
  simpa only [mulVec_single_one, Pi.zero_apply] using congrFun hh i

/-- A tied reordering of a certified basis optimum pins every corresponding
slack row and column. The slack hypotheses are those of the trace-one
qutrit SDP dual (Oszmaniec et al., DOI: 10.1103/PhysRevLett.119.190501).
The theorem does not replace a matching tie by an orbit tie. -/
theorem dual_slack_columns_of_tied_reordering {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → Matrix ι ι ℂ) (Y : Matrix ι ι ℂ) (l : ι → ℂ)
    (p : Equiv.Perm ι)
    (hPSD : ∀ j, (Y + l j • 1 - H j).PosSemidef)
    (hPin : ∀ j, (Y + l j • 1 - H j) j j = 0)
    (hTie : ∑ j, H j (p j) (p j) = ∑ j, H j j j) :
    ∀ i j, (Y + l j • 1 - H j) i (p j) = 0 := by
  let S : ι → Matrix ι ι ℂ := fun j => Y + l j • 1 - H j
  have hd (i j : ι) : S j i i = Y i i + l j - H j i i := by
    simp [S, smul_eq_mul]
  have hSum : ∑ j, S j (p j) (p j) = 0 := by
    simp only [hd, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Equiv.sum_comp p (fun i => Y i i), hTie]
    have h : (∑ j, S j j j) = ∑ _ : ι, (0 : ℂ) := Finset.sum_congr rfl (fun j _ => hPin j)
    simpa only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← hd,
      Finset.sum_const_zero] using h
  have hRe : ∑ j, (S j (p j) (p j)).re = 0 := by
    simpa only [map_sum, Complex.zero_re] using congrArg Complex.reCLM hSum
  have hNN (j : ι) : 0 ≤ (S j (p j) (p j)).re := by
    simpa only [← Pi.single_star, star_one, mulVec_single_one, single_dotProduct, one_mul]
      using (hPSD j).re_dotProduct_nonneg (Pi.single (p j) 1)
  have hz (j : ι) : (S j (p j) (p j)).re = 0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hNN).mp hRe) j
  have hDiag (j : ι) : S j (p j) (p j) = 0 := by
    have hm := Complex.ext_iff.mp ((hPSD j).isHermitian.apply (p j) (p j))
    apply Complex.ext (hz j)
    have hIm : -(S j (p j) (p j)).im = (S j (p j) (p j)).im := by simpa only [S, Complex.star_def, Complex.conj_im] using hm.2
    rw [Complex.zero_im]
    linarith
  intro i j
  exact psd_column_zero_of_diag_zero (hPSD j) (p j) (hDiag j) i

/-- At a tied three-cycle, all three slot matrices have the same
off-diagonal entries. Thus the orthonormal-frame dependence of this
triple objective reduces to the diagonal assignment objective. -/
theorem triple_dual_tied_cycle_common_offDiag
    (H : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ) (Y : Matrix (Fin 3) (Fin 3) ℂ)
    (l : Fin 3 → ℂ) (p : Equiv.Perm (Fin 3)) (hCycle : ∀ j, p j ≠ j)
    (hPSD : ∀ j, (Y + l j • 1 - H j).PosSemidef)
    (hPin : ∀ j, (Y + l j • 1 - H j) j j = 0)
    (hTie : ∑ j, H j (p j) (p j) = ∑ j, H j j j) :
    ∀ j i k, i ≠ k → H j i k = Y i k := by
  have hp := dual_slack_columns_of_tied_reordering H Y l p hPSD hPin hTie
  intro j i k hik
  let S := Y + l j • 1 - H j
  have hj : ∀ r, S r j = 0 := psd_column_zero_of_diag_zero (hPSD j) j (hPin j)
  have h : S i k = 0 := by
    by_cases hkj : k = j
    · rw [hkj]; exact hj _
    by_cases hkp : k = p j
    · rw [hkp]; exact hp _ _
    have hi : i = j ∨ i = p j := by
      by_contra! hh
      have hc : ({i, k, j, p j} : Finset (Fin 3)).card ≤ (Finset.univ : Finset (Fin 3)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      simp [Finset.card_insert_of_not_mem, hik, hh.1, hh.2, hkj, hkp, Ne.symm (hCycle j)] at hc
    have hki : S k i = 0 := by
      rcases hi with rfl | rfl
      · exact hj _
      · exact hp _ _
    have hHerm : S.IsHermitian := (hPSD j).isHermitian
    rw [← hHerm.apply k i] at hki
    exact star_eq_zero.mp hki
  simpa [S, Matrix.one_apply_ne hik, sub_eq_zero, eq_comm] using h

/-- On an open reciprocal profile chart, equality up to a nonzero profile
scale forces equality up to one kernel scale. For each tested edge we need
only two coordinates using the same auxiliary matching. The auxiliary
product may depend on the tested edge. The explicit pivot lets the tested
edge itself be zero without any division by that edge. -/
theorem projective_partialKernel_ratio_recovery {ι κ : Type*}
    (i₀ : ι) (j₀ : κ) (a a' : ι → ℂ) (b b' : κ → ℂ)
    (μ : ℂ) (hμ : μ ≠ 0) (hpivot : a i₀ + b j₀ ≠ 0)
    (hProfile : ∀ i j, ∃ P P' : ℂ, P ≠ 0 ∧
      (a' i + b' j) * P' = μ * ((a i + b j) * P) ∧
      (a' i₀ + b' j₀) * P' = μ * ((a i₀ + b j₀) * P)) :
    ∃ c t : ℂ, c ≠ 0 ∧
      (∀ i, a' i = c * a i + t) ∧ (∀ j, b' j = c * b j - t) := by
  have hpivot' : a' i₀ + b' j₀ ≠ 0 := by
    obtain ⟨P, P', hP, _, h⟩ := hProfile i₀ j₀
    exact (mul_ne_zero_iff.mp (h ▸ mul_ne_zero hμ (mul_ne_zero hpivot hP))).1
  let c := (a' i₀ + b' j₀) / (a i₀ + b j₀)
  have hm (i j) : a' i + b' j = c * (a i + b j) := by
    obtain ⟨P, P', hP, hE, hF⟩ := hProfile i j
    have hP' : P' ≠ 0 := (mul_ne_zero_iff.mp (hF ▸ mul_ne_zero hμ (mul_ne_zero hpivot hP))).2
    apply (mul_right_cancel₀ hP')
    rw [hE]
    dsimp only [c]
    field_simp [hpivot]
    linear_combination -(a i + b j) * hF
  obtain ⟨t, ha, hb⟩ := additive_kernel_scale_translation i₀ j₀ a a' b b' c hm
  exact ⟨c, t, div_ne_zero hpivot' hpivot, ha, hb⟩

/-- Squared Euclidean energy on a coordinate block. -/
def blockEnergy {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

private theorem blockEnergy_sumElim {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℂ) (z : κ → ℂ) :
    blockEnergy (Sum.elim x z) = blockEnergy x + blockEnergy z := by
  simp only [blockEnergy, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Strict radial bounds transfer to the active block under exterior
diagonal feedback. Compare Redheffer (DOI: 10.1002/sapm19624111);
the proof uses only the block energy identity, and is valid even
when no inverse pivot has been chosen. -/
theorem blockEnergy_lt_of_exterior_diagonal_feedback
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ ι ℂ) (D : Matrix κ κ ℂ)
    (d : κ → ℂ) (ρ : ℝ)
    (hDisc : ∀ v : ι ⊕ κ → ℂ, v ≠ 0 →
      blockEnergy (fromBlocks A B C D *ᵥ v) < ρ * blockEnergy v)
    (hExterior : ∀ j, ρ ≤ Complex.normSq (d j))
    (x : ι → ℂ) (z : κ → ℂ) (hInput : Sum.elim x z ≠ 0)
    (hFeedback : C *ᵥ x + D *ᵥ z = -(diagonal d *ᵥ z)) :
    blockEnergy (A *ᵥ x + B *ᵥ z) < ρ * blockEnergy x := by
  have h := hDisc (Sum.elim x z) hInput
  have hl : Sum.elim x z ∘ Sum.inl = x := rfl
  have hr : Sum.elim x z ∘ Sum.inr = z := rfl
  rw [fromBlocks_mulVec, hl, hr, blockEnergy_sumElim, blockEnergy_sumElim, hFeedback,
    mul_add] at h
  have hExt : ρ * blockEnergy z ≤ blockEnergy (-(diagonal d *ᵥ z)) := by
    simp only [blockEnergy, Finset.mul_sum, Pi.neg_apply, Complex.normSq_neg, mulVec_diagonal,
      Complex.normSq_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hExterior j)
      (Complex.normSq_nonneg _)
  linarith

/-- Exterior feedback on a strictly contractive block has a nonsingular
spectator pivot, and its Schur complement inherits the same strict
energy bound. No normality is needed for this transfer itself. -/
theorem schur_disk_barrier_of_exterior_diagonal
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ ι ℂ) (D : Matrix κ κ ℂ)
    (d : κ → ℂ) (ρ : ℝ)
    (hDisc : ∀ v : ι ⊕ κ → ℂ, v ≠ 0 →
      blockEnergy (fromBlocks A B C D *ᵥ v) < ρ * blockEnergy v)
    (hExterior : ∀ j, ρ ≤ Complex.normSq (d j)) :
    let P := D + diagonal d
    IsUnit P.det ∧ ∀ x : ι → ℂ, x ≠ 0 →
      blockEnergy ((A - B * P⁻¹ * C) *ᵥ x) < ρ * blockEnergy x := by
  intro P
  have hp : IsUnit P.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]
    apply (Matrix.mulVec_injective_iff_isUnit (A := P)).mp
    intro z₁ z₂ h
    by_contra hne
    have hne' : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
    have hV : Sum.elim (0 : ι → ℂ) (z₁ - z₂) ≠ 0 := by
      intro hh
      exact hne' (congrArg (fun f => f ∘ Sum.inr) hh)
    have hz : P *ᵥ (z₁ - z₂) = 0 := by rw [mulVec_sub, h, sub_self]
    have hf : C *ᵥ (0 : ι → ℂ) + D *ᵥ (z₁ - z₂) =
        -(diagonal d *ᵥ (z₁ - z₂)) := by
      rw [mulVec_zero, zero_add, eq_neg_iff_add_eq_zero, ← add_mulVec]
      exact hz
    have h' := blockEnergy_lt_of_exterior_diagonal_feedback A B C D d ρ hDisc hExterior
      0 (z₁ - z₂) hV hf
    simp [blockEnergy] at h'
    exact (not_lt_of_ge (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)) h'
  refine ⟨hp, fun x hx => ?_⟩
  let z := -(P⁻¹ *ᵥ (C *ᵥ x))
  have hV : Sum.elim x z ≠ 0 := by
    intro hh
    exact hx (congrArg (fun f => f ∘ Sum.inl) hh)
  have hS : P *ᵥ z = -(C *ᵥ x) := by
    simp only [z, mulVec_neg, mulVec_mulVec, ← Matrix.mul_assoc, P.mul_nonsing_inv hp, Matrix.one_mul, one_mulVec]
  have hf : C *ᵥ x + D *ᵥ z = -(diagonal d *ᵥ z) := by
    rw [eq_neg_iff_add_eq_zero, add_assoc, ← add_mulVec]
    change C *ᵥ x + P *ᵥ z = 0
    rw [hS, add_neg_cancel]
  have ht := blockEnergy_lt_of_exterior_diagonal_feedback A B C D d ρ hDisc hExterior x z hV hf
  simpa only [z, mulVec_neg, ← mulVec_mulVec, sub_mulVec, sub_eq_add_neg, add_mulVec, neg_mulVec] using ht

/-- Algebraic circle completion for the nonnormal flat-pair test. The three
scalar coefficient equations specify the circle; the proof works for a
general matrix, not only for normal effective operators. -/
theorem flat_pair_quadratic_circle_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (a b g c : ℂ) (ρ : ℝ)
    (hp : g * a - star g * b = -(g - star g) * c)
    (hq : g * star b - star g * star a = -(g - star g) * star c)
    (hr : g * star b * a - star g * star a * b =
      (g - star g) * (star c * c - (ρ : ℂ))) :
    g • ((T + b • 1)ᴴ * (T + a • 1)) -
      star g • ((T + a • 1)ᴴ * (T + b • 1)) =
      (g - star g) • ((T - c • 1)ᴴ * (T - c • 1) - (ρ : ℂ) • 1) := by
  calc
    _ = (g - star g) • (Tᴴ * T) + (g * a - star g * b) • Tᴴ +
        (g * star b - star g * star a) • T +
        (g * star b * a - star g * star a * b) • (1 : Matrix ι ι ℂ) := by
      simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_one,
        Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
      module
    _ = _ := by
      rw [hp, hq, hr]
      simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_one,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
      module

private theorem ofReal_blockEnergy_eq_dotProduct {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (blockEnergy v : ℂ) = star v ⬝ᵥ v := by
  simp only [blockEnergy, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    dotProduct, Pi.star_apply, Complex.star_def]

private theorem isUnit_det_gram_sub_of_blockEnergy_lt
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ) (ρ : ℝ)
    (h : ∀ x, x ≠ 0 → blockEnergy (T *ᵥ x) < ρ * blockEnergy x) :
    IsUnit (Tᴴ * T - (ρ : ℂ) • 1).det := by
  let K := Tᴴ * T - (ρ : ℂ) • 1
  change IsUnit K.det
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  by_contra hne
  let z := x - y
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  have hk : K *ᵥ z = 0 := by rw [mulVec_sub, hxy, sub_self]
  have hf : (Tᴴ * T) *ᵥ z = (ρ : ℂ) • z := by
    simpa only [K, sub_mulVec, smul_mulVec_assoc, one_mulVec, sub_eq_zero] using hk
  have hq := congrArg (fun w => star z ⬝ᵥ w) hf
  dsimp only at hq
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star,
    dotProduct_smul, smul_eq_mul, ← ofReal_blockEnergy_eq_dotProduct,
    ← ofReal_blockEnergy_eq_dotProduct, ← Complex.ofReal_mul] at hq
  exact (ne_of_lt (h z hz)) (Complex.ofReal_injective hq)

/-- Strict disk containment rules out flat-pair couplings, for the
singular-value circle test rather than an eigenvalue-only condition. -/
theorem flat_pair_cross_zero_of_strict_disk
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) {a b d e : ℂ} (hab : a ≠ b) (hd : d ≠ 0) (he : e ≠ 0)
    (c : ℂ) (ρ : ℝ)
    (hp : let g := star d * e; g * a - star g * b = -(g - star g) * c)
    (hq : let g := star d * e; g * star b - star g * star a = -(g - star g) * star c)
    (hr : let g := star d * e; g * star b * a - star g * star a * b =
      (g - star g) * (star c * c - (ρ : ℂ)))
    (hg : star d * e - star (star d * e) ≠ 0)
    (hDisc : ∀ x, x ≠ 0 → blockEnergy ((T - c • 1) *ᵥ x) < ρ * blockEnergy x)
    (u v : ι → ℂ)
    (h₁ : let Y := T + b • (1 : Matrix ι ι ℂ)
      (d • Y) *ᵥ u + (star d • Yᴴ) *ᵥ v = 0)
    (h₂ : let X := T + a • (1 : Matrix ι ι ℂ)
      (e • X) *ᵥ u + (star e • Xᴴ) *ᵥ v = 0) :
    u = 0 ∧ v = 0 := by
  apply flat_pair_cross_zero_of_circle_test T hab hd he u v h₁ h₂
  dsimp only
  rw [flat_pair_quadratic_circle_factor T a b (star d * e) c ρ hp hq hr, Matrix.det_smul]
  exact ((isUnit_iff_ne_zero.mpr hg).pow _).mul
    (isUnit_det_gram_sub_of_blockEnergy_lt (T - c • 1) ρ hDisc)

/-- The center and radius for the noncollinear flat-pair test are
explicit. Its circle contains the point `-a`, so the squared radius is
`normSq (a+c)`. -/
theorem flat_pair_circle_coefficients (a b g : ℂ) (hg : g - star g ≠ 0) :
    let c := -(g * a - star g * b) / (g - star g)
    let ρ := Complex.normSq (a + c)
    g * a - star g * b = -(g - star g) * c ∧
    g * star b - star g * star a = -(g - star g) * star c ∧
    g * star b * a - star g * star a * b =
      (g - star g) * (star c * c - (ρ : ℂ)) := by
  intro c ρ
  have h₁ : g * a - star g * b = -(g - star g) * c := by
    symm
    dsimp only [c]
    calc
      _ = (g * a - star g * b) * ((g - star g) * (g - star g)⁻¹) := by
        rw [div_eq_mul_inv]
        ring
      _ = _ := by rw [mul_inv_cancel₀ hg, mul_one]
  have hs := congrArg star h₁
  simp only [star_sub, star_mul', star_star, star_neg] at hs
  have h₂ : g * star b - star g * star a = -(g - star g) * star c := by
    linear_combination -hs
  refine ⟨h₁, h₂, ?_⟩
  simp only [ρ, Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_add]
  linear_combination star a * h₁ + a * h₂

/-- A strict spectral-circle energy bound before elimination rules out
both flat-pair couplings after exterior spectator elimination. Here
`A,D` are blocks of the centered matrix, and `s` lists the shifted
spectator labels. Neither invertibility of the spectator pivot nor
normality of the effective matrix are hypotheses. -/
theorem flat_pair_cross_zero_of_exterior_schur_disk
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ ι ℂ) (D : Matrix κ κ ℂ)
    (s : κ → ℂ) {a b d e : ℂ} (hab : a ≠ b) (hd : d ≠ 0) (he : e ≠ 0)
    (hg : star d * e - star (star d * e) ≠ 0)
    (u v : ι → ℂ) :
    let g := star d * e
    let c := -(g * a - star g * b) / (g - star g)
    let ρ := Complex.normSq (a + c)
    let P := D + diagonal s
    let T := c • 1 + (A - B * P⁻¹ * C)
    (∀ w : ι ⊕ κ → ℂ, w ≠ 0 →
      blockEnergy (fromBlocks A B C D *ᵥ w) < ρ * blockEnergy w) →
    (∀ j, ρ ≤ Complex.normSq (s j)) →
    (let Y := T + b • (1 : Matrix ι ι ℂ);
      (d • Y) *ᵥ u + (star d • Yᴴ) *ᵥ v = 0) →
    (let X := T + a • (1 : Matrix ι ι ℂ);
      (e • X) *ᵥ u + (star e • Xᴴ) *ᵥ v = 0) →
    IsUnit P.det ∧ u = 0 ∧ v = 0 := by
  intro g c ρ P T hDisc hExterior h₁ h₂
  obtain ⟨hP, hT⟩ := schur_disk_barrier_of_exterior_diagonal A B C D s ρ hDisc hExterior
  have hc : T - c • 1 = A - B * P⁻¹ * C := by dsimp only [T]; abel
  obtain ⟨hp, hq, hr⟩ := flat_pair_circle_coefficients a b g hg
  refine ⟨hP, flat_pair_cross_zero_of_strict_disk T hab hd he c ρ hp hq hr hg ?_ u v h₁ h₂⟩
  rw [hc]
  exact hT

end
end MOC
