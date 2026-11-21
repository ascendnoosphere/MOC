import MOC.Support
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Linarith

/-! First variation of the smallest support deficit over a finite set of matchings. -/

open BigOperators Filter Matrix
open scoped ComplexConjugate InnerProductSpace Topology

namespace MOC

noncomputable section

/-- At a local maximum of a finite minimum, zero belongs to the convex hull of the
active gradients. The curves can be chosen in a constraint set, with gradients
represented in the Hilbert space of permissible velocities. -/
theorem zero_mem_convexHull_of_active_gradients
    {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Finite J]
    (value : J → ℝ) (gradient : J → E) (curveValues : J → E → ℝ → ℝ) (g : ℝ)
    (hmin : ∀ j, g ≤ value j)
    (hvalue : ∀ j v, curveValues j v 0 = value j)
    (hderiv : ∀ j v, HasDerivAt (curveValues j v) (⟪gradient j, v⟫_ℝ) 0)
    (hmax : ∀ v, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ j, curveValues j v t ≤ g) :
    (0 : E) ∈ convexHull ℝ (Set.range fun j : {j // value j = g} => gradient j) := by
  let S : Set E := Set.range fun j : {j // value j = g} => gradient j
  change (0 : E) ∈ convexHull ℝ S
  by_contra hn
  have hclosed : IsClosed (convexHull ℝ S) := (Set.finite_range _).isClosed_convexHull
  obtain ⟨L, r, h0, hsep⟩ :=
    geometric_hahn_banach_point_closed (convex_convexHull ℝ S) hclosed hn
  let v := (InnerProductSpace.toDual ℝ E).symm L
  have hgradient (j : J) (hj : value j = g) : 0 < ⟪gradient j, v⟫_ℝ := by
    rw [real_inner_comm v (gradient j)]
    change 0 < ⟪(InnerProductSpace.toDual ℝ E).symm L, gradient j⟫_ℝ
    rw [InnerProductSpace.toDual_symm_apply]
    have hr : 0 < r := by simpa only [map_zero] using h0
    exact hr.trans (hsep _ (subset_convexHull ℝ S ⟨⟨j, hj⟩, rfl⟩))
  have hstrict (j : J) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g < curveValues j v t := by
    by_cases hj : value j = g
    · have hslope := (hderiv j v).tendsto_slope_zero_right (Ioi_mem_nhds (hgradient j hj))
      filter_upwards [hslope, self_mem_nhdsWithin] with t ht htpos
      change 0 < t at htpos
      change 0 < t⁻¹ • (curveValues j v (0 + t) - curveValues j v 0) at ht
      rw [zero_add, smul_eq_mul, hvalue j v, hj] at ht
      exact sub_pos.mp ((mul_pos_iff_of_pos_left (inv_pos.mpr htpos)).mp ht)
    · have hgt : g < curveValues j v 0 := by
        rw [hvalue]
        exact lt_of_le_of_ne (hmin j) hj.symm
      exact ((hderiv j v).continuousAt.eventually_mem (Ioi_mem_nhds hgt)).filter_mono
        nhdsWithin_le_nhds
  obtain ⟨t, hgt, j, hle⟩ := ((Filter.eventually_all.mpr hstrict).and (hmax v)).exists
  exact hle.not_gt (hgt j)

variable {ι : Type*} [Fintype ι]

/-- The squared Euclidean norm of the pair of spectra. -/
def spectralEnergy (a b : ι → ℂ) : ℝ :=
  (∑ i, Complex.normSq (a i)) + ∑ j, Complex.normSq (b j)

theorem spectralEnergy_shift (a b : ι → ℂ) (t : ℂ) :
    spectralEnergy (fun i => a i + t) (fun i => b i - t) =
      spectralEnergy a b + 2 * (Fintype.card ι : ℝ) * Complex.normSq t +
        2 * (((∑ i, a i) - ∑ i, b i) * star t).re := by
  have hre (c : ι → ℂ) :
      (∑ i, (c i * conj t).re) = ((∑ i, c i) * conj t).re := by
    rw [Finset.sum_mul]
    change (∑ i, Complex.reLm (c i * conj t)) = Complex.reLm (∑ i, c i * conj t)
    exact (map_sum Complex.reLm (fun i : ι => c i * conj t) Finset.univ).symm
  simp only [spectralEnergy, Complex.normSq_add, Complex.normSq_sub, Complex.star_def,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, hre, sub_mul, Complex.sub_re] <;> ring

theorem spectralEnergy_scale (a b : ι → ℂ) (r : ℝ) :
    spectralEnergy (fun i => (r : ℂ) * a i) (fun i => (r : ℂ) * b i) =
      r ^ 2 * spectralEnergy a b := by
  simp only [spectralEnergy, Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum] <;> ring

variable [DecidableEq ι] [Nonempty ι]

/-- An opposite shift and a common real dilation improve a positive maximal support
gap unless the two traces agree. The maximization here is over the spectral unit ball. -/
theorem equal_trace_of_positive_support_gap_maximizer
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (g : ℝ)
    (henergy : spectralEnergy a b ≤ 1) (hg : 0 < g)
    (hgap : ∀ σ : Equiv.Perm ι,
      g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re)
    (hmax : ∀ (c d : ι → ℂ), spectralEnergy c d ≤ 1 →
      ∃ σ : Equiv.Perm ι, (η * (determinantValue c d U - matchingProduct c d σ)).re ≤ g) :
    (∑ i, a i) = ∑ i, b i := by
  by_contra htrace
  let n : ℕ := Fintype.card ι
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  let s : ℂ := (∑ i, a i) - ∑ i, b i
  let t : ℂ := -s / (2 * (n : ℂ))
  let c (i : ι) := a i + t
  let d (i : ι) := b i - t
  have hs : s = -(2 * (n : ℂ)) * t := by
    dsimp only [t]
    field_simp [hnC] <;> ring
  have ht : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr htrace))
    (mul_ne_zero two_ne_zero hnC)
  have hproduct : (s * star t).re = -(2 * (n : ℝ)) * Complex.normSq t := by
    rw [hs, mul_assoc, Complex.star_def, Complex.mul_conj]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, sub_zero, zero_mul, add_zero]
  have hrlt : spectralEnergy c d < 1 := by
    change spectralEnergy (fun i => a i + t) (fun i => b i - t) < 1
    rw [spectralEnergy_shift]
    change spectralEnergy a b + 2 * (n : ℝ) * Complex.normSq t + 2 * (s * star t).re < 1
    rw [hproduct]
    have hpos := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hnR) (Complex.normSq_pos.mpr ht)
    linarith
  let e := spectralEnergy c d
  let r : ℝ := (3 - e) / 2
  have hr : 1 < r := by dsimp [r, e]; linarith
  have hallow : spectralEnergy (fun i => (r : ℂ) * c i) (fun i => (r : ℂ) * d i) ≤ 1 := by
    rw [spectralEnergy_scale]
    change r ^ 2 * e ≤ 1
    have hid : 1 - r ^ 2 * e = (1 - e) ^ 2 * (4 - e) / 4 := by dsimp [r]; ring
    have hep : 0 ≤ (1 - e) ^ 2 * (4 - e) / 4 := by
      exact div_nonneg (mul_nonneg (sq_nonneg _) (by dsimp [e]; linarith)) (by norm_num)
    linarith
  obtain ⟨σ, hσ⟩ := hmax _ _ hallow
  have heval :
      (η * (determinantValue (fun i => (r : ℂ) * c i) (fun i => (r : ℂ) * d i) U -
          matchingProduct (fun i => (r : ℂ) * c i) (fun i => (r : ℂ) * d i) σ)).re =
        r ^ n * (η * (determinantValue a b U - matchingProduct a b σ)).re := by
    rw [determinantValue_scale, matchingProduct_scale, ← mul_sub, mul_left_comm η,
      ← Complex.ofReal_pow]
    dsimp only [c, d]
    rw [determinantValue_shift a b hU t, matchingProduct_shift a b t]
    simp only [n, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [heval] at hσ
  have hrpow : 1 < r ^ n := one_lt_pow₀ hr hn
  have hrg := mul_lt_mul_of_pos_right hrpow hg
  have hle := mul_le_mul_of_nonneg_left (hgap σ) (le_trans zero_le_one hrpow.le)
  exact (lt_irrefl g) (by simpa only [one_mul] using hrg.trans_le (hle.trans hσ))

end

end MOC
