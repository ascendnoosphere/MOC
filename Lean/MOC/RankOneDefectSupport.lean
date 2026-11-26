import MOC.RankOneCompressionDisk
import MOC.Normal
import MOC.Support

/-! Exact support of a determinant as its one defective singular value varies. -/

namespace MOC

open Matrix

noncomputable section

private theorem disk_support_phase (d : ℂ) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ d * u = (‖d‖ : ℂ) := by
  by_cases hd : d = 0
  · exact ⟨1, norm_one, by simp [hd]⟩
  have hn : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have hc : (‖d‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  refine ⟨star d / (‖d‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.star_def, Complex.norm_conj, Complex.norm_of_nonneg (norm_nonneg d),
      div_self hn]
  rw [mul_div_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  apply (div_eq_iff hc).mpr
  push_cast <;> ring

/-- Maximize the real part of the complex linear term at each radius, then
maximize the resulting real quadratic on the unit interval. -/
theorem quadraticDiskSupport_max (p q : ℝ) (d : ℂ) :
    let F := fun z : ℂ => p + 2 * (d * z).re + q * ‖z‖ ^ 2
    let M := if -‖d‖ ≤ q then p + 2 * ‖d‖ + q else p + ‖d‖ ^ 2 / (-q)
    (∀ z : ℂ, ‖z‖ ≤ 1 → F z ≤ M) ∧
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ F z = M ∧ (-‖d‖ ≤ q → ‖z‖ = 1) := by
  intro F M
  obtain ⟨u, hu, hdu⟩ := disk_support_phase d
  let R := fun r : ℝ => p + 2 * ‖d‖ * r + q * r ^ 2
  have huR (r : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ) * u‖ = r ∧ F ((r : ℂ) * u) = R r := by
    have hnorm : ‖(r : ℂ) * u‖ = r := by
      rw [norm_mul, hu, Complex.norm_of_nonneg hr, mul_one]
    refine ⟨hnorm, ?_⟩
    unfold F R
    rw [hnorm, show d * ((r : ℂ) * u) = (r : ℂ) * (d * u) by ring, hdu,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have hle (z : ℂ) : F z ≤ R ‖z‖ := by
    have hdz : (d * z).re ≤ ‖d‖ * ‖z‖ := by
      simpa only [norm_mul] using Complex.re_le_norm (d * z)
    unfold F R
    linarith only [hdz]
  by_cases hq : -‖d‖ ≤ q
  · have hM : M = R 1 := by
      simp [M, R, hq]
    refine ⟨fun z hz => (hle z).trans ?_, ?_⟩
    · rw [hM]
      have hsum : 0 ≤ q + ‖d‖ := by linarith only [hq]
      have hprod := mul_nonneg (sub_nonneg.mpr hz)
        (add_nonneg (mul_nonneg hsum
          (add_nonneg zero_le_one (norm_nonneg z)))
          (mul_nonneg (norm_nonneg d) (sub_nonneg.mpr hz)))
      unfold R
      nlinarith only [hprod]
    · obtain ⟨hu', heq⟩ := huR 1 zero_le_one
      exact ⟨(1 : ℂ) * u, hu'.le, heq.trans hM.symm, fun _ => hu'⟩
  · have hnq : 0 < -q := by linarith only [lt_of_not_ge hq, norm_nonneg d]
    let r := ‖d‖ / (-q)
    have hr : 0 ≤ r := div_nonneg (norm_nonneg d) hnq.le
    have hr₁ : r ≤ 1 := (div_le_iff₀ hnq).mpr (by linarith only [lt_of_not_ge hq])
    have hM : M = p + ‖d‖ ^ 2 / (-q) := if_neg hq
    have hfactor (t : ℝ) : M - R t = (-q) * (t - r) ^ 2 := by
      rw [hM]
      dsimp only [R, r]
      field_simp [hnq.ne'] <;> ring
    refine ⟨fun z hz => (hle z).trans ?_, ?_⟩
    · have hnonneg : 0 ≤ M - R ‖z‖ := by
        rw [hfactor]
        exact mul_nonneg hnq.le (sq_nonneg _)
      exact sub_nonneg.mp hnonneg
    · obtain ⟨hu', heq⟩ := huR r hr
      have hzero := hfactor r
      have heqM : M = R r := sub_eq_zero.mp (by simpa only [sub_self, zero_pow
        (show (2 : ℕ) ≠ 0 by decide), mul_zero] using hzero)
      exact ⟨(r : ℂ) * u, hu'.le.trans hr₁, heq.trans heqM.symm, fun h => (hq h).elim⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Support of the rank-one phase determinant on its closed disk, including
the stationary interior branch and the singular bordered-minor case. -/
theorem rankOneCompressionDisk_support_max (A B : Matrix ι ι ℂ) (v : ι → ℂ) (η : ℂ) :
    let F := fun z : ℂ => (η * (A + rankOnePhase v z * B * (rankOnePhase v z)ᴴ).det).re
    let p := F 0
    let q := (F 1 + F (-1)) / 2 - p
    let d : ℂ := ⟨(F 1 - F (-1)) / 4, (F (-Complex.I) - F Complex.I) / 4⟩
    let M := if -‖d‖ ≤ q then p + 2 * ‖d‖ + q else p + ‖d‖ ^ 2 / (-q)
    (∀ z : ℂ, ‖z‖ ≤ 1 → F z ≤ M) ∧
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ F z = M ∧ (-‖d‖ ≤ q → ‖z‖ = 1) := by
  intro F p q d M
  have heval (z : ℂ) : F z = p + 2 * (d * z).re + q * ‖z‖ ^ 2 := by
    have h := rankOneCompressionDisk_support A B v η z
    change F z = F 0 + (F 1 - F (-1)) / 2 * z.re +
      (F Complex.I - F (-Complex.I)) / 2 * z.im + q * Complex.normSq z at h
    rw [h, Complex.normSq_eq_norm_sq, Complex.mul_re]
    dsimp only [d, p]
    ring
  obtain ⟨hle, z, hz, heq, hboundary⟩ := quadraticDiskSupport_max p q d
  exact ⟨fun z hz => (heval z).le.trans (hle z hz), z, hz, (heval z).trans heq, hboundary⟩

/-- The smaller-order conjecture proves the boundary branch for the
normal determinant. It remains to supply the interior quadratic inequality.
Any upper bound on the larger injection list is an admissible threshold `M`. -/
theorem rankOneCompressionDisk_support_le_of_interior
    (hSmall : Conjecture ι) (a b v : ι → ℂ) (W : Matrix ι ι ℂ) (hW : IsUnitary W)
    (hv : ∑ i, star (v i) * v i = 1) (η : ℂ) (M : ℝ)
    (hM : ∀ σ, (η * matchingProduct a b σ).re ≤ M) :
    let A := diagonal a
    let B := W * diagonal b * Wᴴ
    let F := fun z : ℂ => (η * (A + rankOnePhase v z * B * (rankOnePhase v z)ᴴ).det).re
    let p := F 0
    let q := (F 1 + F (-1)) / 2 - p
    let d : ℂ := ⟨(F 1 - F (-1)) / 4, (F (-Complex.I) - F Complex.I) / 4⟩
    (q < -‖d‖ → ‖d‖ ^ 2 ≤ (-q) * (M - p)) →
      ∀ z : ℂ, ‖z‖ ≤ 1 → F z ≤ M := by
  intro A B F p q d hinterior z hz
  let K := if -‖d‖ ≤ q then p + 2 * ‖d‖ + q else p + ‖d‖ ^ 2 / (-q)
  obtain ⟨hle, u, hu, heq, hb⟩ := rankOneCompressionDisk_support_max A B v η
  have hzK : F z ≤ K := hle z hz
  apply hzK.trans
  by_cases hq : -‖d‖ ≤ q
  · have huStar : u * star u = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hb hq, one_pow,
        Complex.ofReal_one]
    let D := rankOnePhase v u
    have hD : IsUnitary D := rankOnePhase_unitary v u hv huStar
    have hDW : IsUnitary (D * W) := by
      rw [IsUnitary, Matrix.conjTranspose_mul]
      constructor
      · rw [Matrix.mul_assoc D W (Wᴴ * Dᴴ), ← Matrix.mul_assoc W Wᴴ Dᴴ, hW.1,
          Matrix.one_mul, hD.1]
      · rw [Matrix.mul_assoc Wᴴ Dᴴ (D * W), ← Matrix.mul_assoc Dᴴ D W, hD.2,
          Matrix.one_mul, hW.2]
    have hval : F u = (η * determinantValue a b (D * W)).re := by
      change (η * (diagonal a + D * (W * diagonal b * Wᴴ) * Dᴴ).det).re = _
      simp only [determinantValue, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b (D * W)).mp (hSmall a b _ hDW) η
    exact heq.symm.le.trans (hval.le.trans (hσ.trans (hM σ)))
  · have hq' : q < -‖d‖ := lt_of_not_ge hq
    have hnq : 0 < -q := by linarith only [hq', norm_nonneg d]
    have hdiv : ‖d‖ ^ 2 / (-q) ≤ M - p :=
      (div_le_iff₀ hnq).mpr (by simpa only [mul_comm] using hinterior hq')
    simp only [K, if_neg hq]
    linarith only [hdiv]

end

end MOC
