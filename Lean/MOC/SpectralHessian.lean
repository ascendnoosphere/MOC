import MOC.SpectralGap
import Mathlib.Algebra.GeomSum

/-! Mixed spectral curvature at a gap maximum with a common active matching edge. -/

open BigOperators Filter Matrix
open scoped ComplexConjugate Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Add one complex increment to a selected spectral coordinate. -/
def shiftCoordinate (a : ι → ℂ) (i : ι) (z : ℂ) (k : ι) : ℂ :=
  if k = i then a k + z else a k

@[simp] theorem shiftCoordinate_zero (a : ι → ℂ) (i : ι) :
    shiftCoordinate a i 0 = a := by
  funext k
  by_cases h : k = i <;> simp [shiftCoordinate, h]

private theorem continuous_shiftCoordinate (a : ι → ℂ) (i : ι) :
    Continuous (shiftCoordinate a i) := by
  apply continuous_pi
  intro k
  by_cases h : k = i
  · simpa only [shiftCoordinate, if_pos h] using continuous_const.add continuous_id
  · simpa only [shiftCoordinate, if_neg h] using (continuous_const : Continuous (fun _ : ℂ => a k))

/-- The mixed coefficient from changing one coordinate on each side of a matching. -/
def matchingMixedCoefficient (a b : ι → ℂ) (i j : ι) (σ : Equiv.Perm ι) : ℂ :=
  if σ j = i then 0
  else ∏ k ∈ (Finset.univ.erase j).erase (σ.symm i), (a (σ k) + b k)

/-- The coefficient of the product of two increments, one to entry `a i` and
one to entry `b j`, in the determinant. -/
def determinantMixedCoefficient (a b : ι → ℂ) (U : Matrix ι ι ℂ) (i j : ι) : ℂ :=
  ∑ σ : Equiv.Perm ι, signedWeight U σ * matchingMixedCoefficient a b i j σ

theorem matchingProduct_shift_of_edge (a b : ι → ℂ) (i j : ι) (σ : Equiv.Perm ι)
    (h : σ j = i) (z : ℂ) :
    matchingProduct (shiftCoordinate a i z) (shiftCoordinate b j (-z)) σ =
      matchingProduct a b σ := by
  unfold matchingProduct
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : k = j
  · subst k
    simp [shiftCoordinate, h] <;> ring
  · have hi : σ k ≠ i := fun e => hk (σ.injective (e.trans h.symm))
    simp only [shiftCoordinate, if_neg hk, if_neg hi]

private theorem matchingProduct_shift_of_nonedge (a b : ι → ℂ) (i j : ι) (σ : Equiv.Perm ι)
    (h : σ j ≠ i) (z : ℂ) :
    matchingProduct (shiftCoordinate a i z) (shiftCoordinate b j (-z)) σ =
      (a (σ j) + b j - z) * ((a i + b (σ.symm i) + z) *
        matchingMixedCoefficient a b i j σ) := by
  let k := σ.symm i
  let f (l : ι) := shiftCoordinate a i z (σ l) + shiftCoordinate b j (-z) l
  have hσk : σ k = i := σ.apply_symm_apply i
  have hk : k ≠ j := fun e => h (e ▸ hσk)
  have hkj : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩
  have hf_j : f j = a (σ j) + b j - z := by
    simp [f, shiftCoordinate, h] <;> ring
  have hf_k : f k = a i + b (σ.symm i) + z := by
    change f k = a i + b k + z
    simp [f, shiftCoordinate, hσk, hk] <;> ring
  have hf_rest : (∏ l ∈ (Finset.univ.erase j).erase k, f l) =
      matchingMixedCoefficient a b i j σ := by
    simp only [matchingMixedCoefficient, if_neg h]
    apply Finset.prod_congr rfl
    intro l hl
    obtain ⟨hlk, hlj⟩ := Finset.mem_erase.mp hl
    have hi : σ l ≠ i := fun e => hlk (σ.injective (e.trans hσk.symm))
    simp only [f, shiftCoordinate, if_neg hi, if_neg (Finset.mem_erase.mp hlj).1]
  change (∏ l, f l) = _
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j),
    ← Finset.mul_prod_erase (Finset.univ.erase j) f hkj, hf_j, hf_k, hf_rest]

/-- Each matching is quadratic under opposite changes, with zero curvature
when the two selected coordinates are matched to each other. -/
theorem matchingProduct_oppositeShift_quadratic (a b : ι → ℂ) (i j : ι)
    (σ : Equiv.Perm ι) (z : ℂ) :
    let f (t : ℂ) := matchingProduct (shiftCoordinate a i t) (shiftCoordinate b j (-t)) σ
    let m := matchingMixedCoefficient a b i j σ
    f z = f 0 + z * (f 1 - f 0 + m) - z ^ 2 * m := by
  dsimp only
  by_cases h : σ j = i
  · simp only [matchingProduct_shift_of_edge a b i j σ h, matchingMixedCoefficient, if_pos h,
      sub_self, add_zero, mul_zero, sub_zero]
  · simp only [matchingProduct_shift_of_nonedge a b i j σ h]
    ring

private theorem matchingProduct_shift_symmetric (a b : ι → ℂ) (i j : ι)
    (σ : Equiv.Perm ι) (z : ℂ) :
    matchingProduct (shiftCoordinate a i z) (shiftCoordinate b j (-z)) σ +
        matchingProduct (shiftCoordinate a i (-z)) (shiftCoordinate b j z) σ -
        2 * matchingProduct a b σ = -2 * z ^ 2 * matchingMixedCoefficient a b i j σ := by
  have h₁ := matchingProduct_oppositeShift_quadratic a b i j σ z
  have h₂ := matchingProduct_oppositeShift_quadratic a b i j σ (-z)
  dsimp only at h₁ h₂
  simp only [neg_zero, neg_neg, shiftCoordinate_zero] at h₁ h₂
  rw [h₁, h₂]
  ring

/-- The determinant's opposite spectral shift is quadratic, with its mixed
coefficient given by the signed matching expansion. -/
theorem determinantValue_oppositeShift_quadratic (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (i j : ι) (z : ℂ) :
    let f (t : ℂ) := determinantValue (shiftCoordinate a i t) (shiftCoordinate b j (-t)) U
    let m := determinantMixedCoefficient a b U i j
    f z = f 0 + z * (f 1 - f 0 + m) - z ^ 2 * m := by
  dsimp only
  simp only [← signed_determinant _ _ U hU, determinantMixedCoefficient,
    mul_add, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  have he := matchingProduct_oppositeShift_quadratic a b i j σ z
  dsimp only at he
  rw [he]
  ring

private theorem determinantValue_shift_symmetric (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (i j : ι) (z : ℂ) :
    determinantValue (shiftCoordinate a i z) (shiftCoordinate b j (-z)) U +
        determinantValue (shiftCoordinate a i (-z)) (shiftCoordinate b j z) U -
        2 * determinantValue a b U = -2 * z ^ 2 * determinantMixedCoefficient a b U i j := by
  let L (σ : Equiv.Perm ι) := matchingProduct (shiftCoordinate a i z) (shiftCoordinate b j (-z)) σ
  let R (σ : Equiv.Perm ι) := matchingProduct (shiftCoordinate a i (-z)) (shiftCoordinate b j z) σ
  let S (σ : Equiv.Perm ι) := matchingProduct a b σ
  rw [← signed_determinant (shiftCoordinate a i z) (shiftCoordinate b j (-z)) U hU,
    ← signed_determinant (shiftCoordinate a i (-z)) (shiftCoordinate b j z) U hU,
    ← signed_determinant a b U hU]
  change (∑ σ, signedWeight U σ * L σ) + (∑ σ, signedWeight U σ * R σ) -
    2 * (∑ σ, signedWeight U σ * S σ) = _
  calc
    _ = ∑ σ, signedWeight U σ * (L σ + R σ - 2 * S σ) := by
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, mul_left_comm (signedWeight U _) 2]
    _ = _ := by
      simp only [L, R, S, matchingProduct_shift_symmetric, determinantMixedCoefficient,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring

private theorem sum_normSq_shiftCoordinate (a : ι → ℂ) (i : ι) (z : ℂ) :
    (∑ k, Complex.normSq (shiftCoordinate a i z k)) =
      (∑ k, Complex.normSq (a k)) + Complex.normSq z + 2 * (a i * conj z).re := by
  let f (k : ι) := Complex.normSq (shiftCoordinate a i z k)
  let g (k : ι) := Complex.normSq (a k)
  have hf : f i = g i + Complex.normSq z + 2 * (a i * conj z).re := by
    simp [f, g, shiftCoordinate, Complex.normSq_add]
  have hrest : (∑ k ∈ Finset.univ.erase i, f k) = ∑ k ∈ Finset.univ.erase i, g k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [f, g, shiftCoordinate, if_neg (Finset.mem_erase.mp hk).1]
  change (∑ k, f k) = (∑ k, g k) + _ + _
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ g (Finset.mem_univ i), hf, hrest]
  ring

private theorem sum_shiftCoordinate (a : ι → ℂ) (i : ι) (z : ℂ) :
    (∑ k, shiftCoordinate a i z k) = (∑ k, a k) + z := by
  have hrest : (∑ k ∈ Finset.univ.erase i, shiftCoordinate a i z k) =
      ∑ k ∈ Finset.univ.erase i, a k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [shiftCoordinate, if_neg (Finset.mem_erase.mp hk).1]
  rw [← Finset.add_sum_erase Finset.univ (shiftCoordinate a i z) (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ a (Finset.mem_univ i), hrest]
  simp [shiftCoordinate] <;> ring

private theorem spectralEnergy_opposite_shifts (a b : ι → ℂ) (i j : ι) (p : ℂ)
    (henergy : spectralEnergy a b = 1) (htan : ((a i - b j) * conj p).re = 0) (t : ℝ) :
    spectralEnergy (shiftCoordinate a i ((t : ℂ) * p)) (shiftCoordinate b j (-((t : ℂ) * p))) =
      1 + 2 * (t ^ 2 * Complex.normSq p) := by
  let z := (t : ℂ) * p
  have hcross : ((a i - b j) * conj z).re = 0 := by
    simp only [z, map_mul, Complex.conj_ofReal]
    rw [show (a i - b j) * ((t : ℂ) * conj p) = (t : ℂ) * ((a i - b j) * conj p) by ring,
      Complex.re_ofReal_mul, htan, mul_zero]
  have hn : Complex.normSq z = t ^ 2 * Complex.normSq p := by
    simp only [z, Complex.normSq_mul, Complex.normSq_ofReal, pow_two]
  change spectralEnergy (shiftCoordinate a i z) (shiftCoordinate b j (-z)) = _
  simp only [spectralEnergy, sum_normSq_shiftCoordinate, Complex.normSq_neg, map_neg,
    mul_neg, Complex.neg_re, hn] at ⊢
  simp only [spectralEnergy] at henergy
  simp only [sub_mul, Complex.sub_re] at hcross
  linarith only [henergy, hcross]

/-- At a trace-balanced, normalized support gap maximum, a matched pair shared
by all active matchings bounds the determinant's mixed coefficient. Centering
the tangent opposite shift preserves every determinant and matching value. -/
theorem mixed_curvature_le_of_common_active_edge
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (g : ℝ)
    (henergy : spectralEnergy a b = 1)
    (htrace : (∑ i, a i) = ∑ i, b i)
    (hgap : ∀ σ : Equiv.Perm ι, g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re)
    (hmax : ∀ (c d : ι → ℂ), spectralEnergy c d ≤ 1 →
      ∃ σ : Equiv.Perm ι, (η * (determinantValue c d U - matchingProduct c d σ)).re ≤ g)
    (i j : ι) (hedge : ∀ σ : Equiv.Perm ι,
      (η * (determinantValue a b U - matchingProduct a b σ)).re = g → σ j = i)
    (p : ℂ) (htan : ((a i - b j) * conj p).re = 0) :
    -(η * p ^ 2 * determinantMixedCoefficient a b U i j).re ≤
      ((Fintype.card ι : ℝ) - 1) * g * Complex.normSq p := by
  letI : Nonempty ι := ⟨i⟩
  let n := Fintype.card ι
  let q := (1 - (n : ℝ)⁻¹) * Complex.normSq p
  let A (t : ℝ) := shiftCoordinate a i ((t : ℂ) * p)
  let B (t : ℝ) := shiftCoordinate b j (-((t : ℂ) * p))
  let S (t : ℝ) : ℂ := (∑ k, A t k) - ∑ k, B t k
  let s (t : ℝ) : ℂ := -S t / ((2 * (n : ℝ) : ℝ) : ℂ)
  let A₀ (t : ℝ) (k : ι) := A t k + s t
  let B₀ (t : ℝ) (k : ι) := B t k - s t
  let R (t : ℝ) := 1 + t ^ 2 * q
  let F (σ : Equiv.Perm ι) (t : ℝ) :=
    (η * (determinantValue (A t) (B t) U - matchingProduct (A t) (B t) σ)).re
  let D (t : ℝ) := (η * (determinantValue (A t) (B t) U - determinantValue a b U)).re
  have hA₀ : A 0 = a := by simp [A]
  have hB₀ : B 0 = b := by simp [B]
  have hA : Continuous A :=
    (continuous_shiftCoordinate a i).comp (Complex.continuous_ofReal.mul continuous_const)
  have hB : Continuous B :=
    (continuous_shiftCoordinate b j).comp (Complex.continuous_ofReal.mul continuous_const).neg
  have hn : 0 < n := Fintype.card_pos
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hn₀ : (n : ℝ) ≠ 0 := by linarith only [hn₁]
  have hq : 0 ≤ q := mul_nonneg
    (sub_nonneg.mpr (inv_le_one_of_one_le₀ hn₁)) (Complex.normSq_nonneg p)
  have hR (t : ℝ) : 0 < R t :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (sq_nonneg t) hq)
  have hcenter (t : ℝ) : spectralEnergy (A₀ t) (B₀ t) = 1 + 2 * (t ^ 2 * q) := by
    have hS : S t = 2 * ((t : ℂ) * p) := by
      dsimp only [S, A, B]
      rw [sum_shiftCoordinate, sum_shiftCoordinate, htrace]
      ring
    have he := spectralEnergy_centering (A t) (B t)
    change spectralEnergy (A₀ t) (B₀ t) =
      spectralEnergy (A t) (B t) - Complex.normSq (S t) / (2 * (n : ℝ)) at he
    rw [he, hS, Complex.normSq_mul,
      show Complex.normSq (2 : ℂ) = 4 by norm_num [Complex.normSq_apply],
      Complex.normSq_mul, Complex.normSq_ofReal]
    change spectralEnergy (shiftCoordinate a i ((t : ℂ) * p))
      (shiftCoordinate b j (-((t : ℂ) * p))) - 4 * ((t * t) * Complex.normSq p) /
        (2 * (n : ℝ)) = _
    rw [spectralEnergy_opposite_shifts a b i j p henergy htan]
    dsimp only [q]
    field_simp [hn₀] <;> ring
  have hcontrol (t : ℝ) : ∃ σ : Equiv.Perm ι, F σ t ≤ g * R t ^ n := by
    have hscale : spectralEnergy (fun k => (((R t)⁻¹ : ℝ) : ℂ) * A₀ t k)
        (fun k => (((R t)⁻¹ : ℝ) : ℂ) * B₀ t k) ≤ 1 := by
      rw [spectralEnergy_scale, hcenter, inv_pow, ← div_eq_inv_mul]
      apply (div_le_iff₀ (sq_pos_of_pos (hR t))).mpr
      change 1 + 2 * (t ^ 2 * q) ≤ 1 * (1 + t ^ 2 * q) ^ 2
      nlinarith only [sq_nonneg (t ^ 2 * q)]
    obtain ⟨σ, hσ⟩ := hmax _ _ hscale
    rw [determinantValue_scale, matchingProduct_scale, show determinantValue (A₀ t) (B₀ t) U =
      determinantValue (A t) (B t) U from determinantValue_shift (A t) (B t) hU (s t),
      show matchingProduct (A₀ t) (B₀ t) σ = matchingProduct (A t) (B t) σ from
        matchingProduct_shift (A t) (B t) (s t) σ, ← mul_sub, mul_left_comm η,
      ← Complex.ofReal_pow, Complex.re_ofReal_mul, inv_pow] at hσ
    refine ⟨σ, ?_⟩
    change (R t ^ n)⁻¹ * F σ t ≤ g at hσ
    rw [← div_eq_inv_mul] at hσ
    exact (div_le_iff₀ (pow_pos (hR t) n)).mp hσ
  have hRcont : Continuous R := by unfold R; fun_prop
  have hFcont (σ : Equiv.Perm ι) : Continuous (F σ) := by
    have hUconst : Continuous (fun _ : ℝ => U) := continuous_const
    have hUstar : Continuous (fun _ : ℝ => Uᴴ) := continuous_const
    have hdet : Continuous (fun t => determinantValue (A t) (B t) U) := by
      exact (hA.matrix_diagonal.add
        ((hUconst.matrix_mul hB.matrix_diagonal).matrix_mul hUstar)).matrix_det
    have hprod : Continuous (fun t => matchingProduct (A t) (B t) σ) := by
      unfold matchingProduct
      exact continuous_finset_prod _ fun k _ =>
        ((continuous_apply (σ k)).comp hA).add ((continuous_apply k).comp hB)
    exact Complex.continuous_re.comp (continuous_const.mul (hdet.sub hprod))
  have hnear (σ : Equiv.Perm ι) : ∀ᶠ t in 𝓝 (0 : ℝ), F σ t ≤ g * R t ^ n → F σ 0 = g := by
    by_cases heq : F σ 0 = g
    · exact Eventually.of_forall fun _ _ => heq
    · have hg₀ : g ≤ F σ 0 := by simpa only [F, hA₀, hB₀] using hgap σ
      have hpositive : 0 < F σ 0 - g * R 0 ^ n := by
        simpa only [R, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero,
          one_pow, mul_one, sub_pos] using (lt_of_le_of_ne hg₀ (Ne.symm heq))
      have hcont : Continuous (fun t => F σ t - g * R t ^ n) :=
        (hFcont σ).sub (continuous_const.mul (hRcont.pow n))
      filter_upwards [hcont.continuousAt.eventually_mem (Ioi_mem_nhds hpositive)] with t ht ht'
      exact False.elim (not_lt_of_ge ht' (sub_pos.mp ht))
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ), D t ≤ g * (R t ^ n - 1) := by
    filter_upwards [Filter.eventually_all.mpr hnear] with t ht
    obtain ⟨σ, hσ⟩ := hcontrol t
    have hbase : (η * (determinantValue a b U - matchingProduct a b σ)).re = g := by
      simpa only [F, hA₀, hB₀] using ht σ hσ
    have hmatch : matchingProduct (A t) (B t) σ = matchingProduct a b σ :=
      matchingProduct_shift_of_edge a b i j σ (hedge σ hbase) ((t : ℂ) * p)
    simp only [F, hmatch, mul_sub, Complex.sub_re] at hσ
    simp only [mul_sub, Complex.sub_re] at hbase
    unfold D
    simp only [mul_sub, Complex.sub_re, mul_one]
    linarith only [hσ, hbase]
  have hsymm (t : ℝ) :
      D t + D (-t) = 2 * t ^ 2 * (-(η * p ^ 2 * determinantMixedCoefficient a b U i j).re) := by
    have hdet : determinantValue (A t) (B t) U + determinantValue (A (-t)) (B (-t)) U -
        2 * determinantValue a b U =
          -2 * (((t : ℂ) * p) ^ 2) * determinantMixedCoefficient a b U i j := by
      simpa only [A, B, Complex.ofReal_neg, neg_mul, neg_neg] using
        determinantValue_shift_symmetric a b U hU i j ((t : ℂ) * p)
    have he := congrArg (fun w : ℂ => (η * w).re) hdet
    have he' : D t + D (-t) =
        (η * (-2 * (((t : ℂ) * p) ^ 2) * determinantMixedCoefficient a b U i j)).re := by
      simp only [D, mul_sub, Complex.sub_re]
      have htwo (x : ℂ) : (η * (2 * x)).re = 2 * (η * x).re := by
        rw [mul_left_comm η]
        simpa only [Complex.ofReal_ofNat] using Complex.re_ofReal_mul 2 (η * x)
      change (η * (_ + _ - 2 * determinantValue a b U)).re = _ at he
      simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_re, htwo] at he
      linarith only [he]
    rw [he']
    rw [show η * (-2 * ((t : ℂ) * p) ^ 2 * determinantMixedCoefficient a b U i j) =
      ((-2 * t ^ 2 : ℝ) : ℂ) * (η * p ^ 2 * determinantMixedCoefficient a b U i j) by
        push_cast
        ring]
    rw [Complex.re_ofReal_mul]
    ring
  let G (t : ℝ) := g * q * ∑ k ∈ Finset.range n, R t ^ k
  have hG : Continuous G := by
    unfold G
    exact continuous_const.mul (continuous_finset_sum _ fun k _ => hRcont.pow k)
  have hquot : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      -(η * p ^ 2 * determinantMixedCoefficient a b U i j).re ≤ G t := by
    have hnegt : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using
        (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
    have hneg : ∀ᶠ t in 𝓝 (0 : ℝ), D (-t) ≤ g * (R (-t) ^ n - 1) :=
      hnegt.eventually hbound
    filter_upwards [hbound.filter_mono nhdsWithin_le_nhds, hneg.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht hnt hne
    have hRneg : R (-t) = R t := by simp [R]
    have hGmul : t ^ 2 * G t = g * (R t ^ n - 1) := by
      rw [← geom_sum_mul]
      dsimp only [G, R]
      ring
    rw [hRneg, ← hGmul] at hnt
    rw [← hGmul] at ht
    have hsum := add_le_add ht hnt
    rw [hsymm] at hsum
    apply (mul_le_mul_iff_of_pos_left (mul_pos (by norm_num : (0 : ℝ) < 2)
      (sq_pos_of_ne_zero hne))).mp
    linarith only [hsum]
  have hG₀ : G 0 = (n : ℝ) * g * q := by
    simp only [G, R, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_one]
    ring
  have hG₀' : G 0 = ((n : ℝ) - 1) * g * Complex.normSq p := by
    rw [hG₀]
    dsimp only [q]
    field_simp [hn₀] <;> ring
  rw [← hG₀']
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hquot

/-- The opposite shift perpendicular to the two entries' difference gives a
direct test using the entries themselves. -/
theorem mixed_curvature_perpendicular_le_of_common_active_edge
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (g : ℝ)
    (henergy : spectralEnergy a b = 1)
    (htrace : (∑ i, a i) = ∑ i, b i)
    (hgap : ∀ σ : Equiv.Perm ι, g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re)
    (hmax : ∀ (c d : ι → ℂ), spectralEnergy c d ≤ 1 →
      ∃ σ : Equiv.Perm ι, (η * (determinantValue c d U - matchingProduct c d σ)).re ≤ g)
    (i j : ι) (hedge : ∀ σ : Equiv.Perm ι,
      (η * (determinantValue a b U - matchingProduct a b σ)).re = g → σ j = i) :
    (η * (a i - b j) ^ 2 * determinantMixedCoefficient a b U i j).re ≤
      ((Fintype.card ι : ℝ) - 1) * g * Complex.normSq (a i - b j) := by
  let d := a i - b j
  have htan : (d * conj (Complex.I * d)).re = 0 := by
    rw [map_mul, show d * (conj Complex.I * conj d) = (d * conj d) * conj Complex.I by ring,
      Complex.mul_conj, Complex.re_ofReal_mul, Complex.conj_re, Complex.I_re, mul_zero]
  have h := mixed_curvature_le_of_common_active_edge a b U hU η g henergy htrace hgap hmax i j
    hedge (Complex.I * d) htan
  rw [mul_pow, Complex.I_sq, neg_one_mul, Complex.normSq_mul, Complex.normSq_I, one_mul] at h
  simpa only [mul_neg, neg_mul, Complex.neg_re, neg_neg] using h

end

end MOC
