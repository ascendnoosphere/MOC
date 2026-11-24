import MOC.Reformulations.FirstGeometric
import MOC.Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecificLimits.Basic

/-! Atlas 117: actual multiplicative characters of a common one-parameter
complex torus. Integer weights, including negative ones, remain integral;
there is no relabelling by an arbitrary complex-valued function. -/

open Matrix Filter
open scoped Topology

namespace MOC.Reformulations.NativeLinksB

noncomputable section

/-- The torus element is shared by the two representations. -/
def TorusCharacterForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℤ) (z : ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    z ≠ 0 → IsUnitary U → Holds (fun j => z ^ a j) (fun j => z ^ b j) U

private def floorRatio (x : ℝ) (m : ℕ) : ℝ :=
  (⌊(m : ℝ) * x⌋ : ℝ) / m

private theorem tendsto_floorRatio (x : ℝ) : Tendsto (floorRatio x) atTop (𝓝 x) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun m : ℕ => x - (m : ℝ)⁻¹) atTop (𝓝 x) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hp : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    unfold floorRatio
    apply (le_div_iff₀ hp).mpr
    have he := Int.lt_floor_add_one ((m : ℝ) * x)
    rw [sub_mul, inv_mul_cancel₀ hp.ne']
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hp : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    unfold floorRatio
    apply (div_le_iff₀ hp).mpr
    simpa only [mul_comm] using Int.floor_le ((m : ℝ) * x)

private def torusStep (m : ℕ) : ℂ :=
  (m : ℂ)⁻¹ ^ 2 + (2 * Real.pi * Complex.I) / m

private def torusWeight (w : ℂ) (m : ℕ) : ℤ :=
  m * ⌊(m : ℝ) * w.re⌋ + ⌊(m : ℝ) * (w.im / (2 * Real.pi))⌋

private theorem tendsto_character_exp (w : ℂ) :
    Tendsto (fun m : ℕ => Complex.exp (torusStep m) ^ torusWeight w m)
      atTop (𝓝 (Complex.exp w)) := by
  let c : ℝ := 2 * Real.pi
  let x : ℕ → ℝ := floorRatio w.re
  let y : ℕ → ℝ := floorRatio (w.im / c)
  have hc : c ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hx : Tendsto x atTop (𝓝 w.re) := tendsto_floorRatio _
  have hy : Tendsto y atTop (𝓝 (w.im / c)) := tendsto_floorRatio _
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hre : Tendsto (fun m => x m + y m * (m : ℝ)⁻¹) atTop (𝓝 w.re) := by
    simpa only [mul_zero, add_zero] using hx.add (hy.mul hi)
  have him : Tendsto (fun m => y m * c) atTop (𝓝 w.im) := by
    simpa only [div_mul_cancel₀ _ hc] using hy.mul (tendsto_const_nhds (x := c))
  have hv : Tendsto (fun m => ((x m + y m * (m : ℝ)⁻¹ : ℝ) : ℂ) +
      (y m * c : ℝ) * Complex.I) atTop (𝓝 w) := by
    rw [← Complex.re_add_im w]
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hre).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp him).mul tendsto_const_nhds)
  refine (Complex.continuous_exp.continuousAt.tendsto.comp hv).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  let k : ℤ := ⌊(m : ℝ) * w.re⌋
  let j : ℤ := ⌊(m : ℝ) * (w.im / c)⌋
  have he :
      (torusWeight w m : ℂ) * torusStep m =
        (((x m + y m * (m : ℝ)⁻¹ : ℝ) : ℂ) + (y m * c : ℝ) * Complex.I) +
          (k : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [x, y, c, floorRatio, torusWeight, torusStep, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
    field_simp
    ring
  rw [← Complex.exp_int_mul, he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rfl

theorem torusCharacterForm_iff : TorusCharacterForm ↔ MOCIsTrue := by
  classical
  constructor
  · intro h
    apply moc_iff_nonzeroSpectra.mpr
    intro n a b U hU ha hb
    by_contra hf
    rw [holds_iff_directional] at hf
    push_neg at hf
    obtain ⟨η, hstrict⟩ := hf
    let a' (m : ℕ) (j : Fin n) := Complex.exp (torusStep m) ^ torusWeight (Complex.log (a j)) m
    let b' (m : ℕ) (j : Fin n) := Complex.exp (torusStep m) ^ torusWeight (Complex.log (b j)) m
    have hA : Tendsto a' atTop (𝓝 a) :=
      tendsto_pi_nhds.mpr fun j => by
        simpa only [Complex.exp_log (ha j)] using tendsto_character_exp (Complex.log (a j))
    have hB : Tendsto b' atTop (𝓝 b) :=
      tendsto_pi_nhds.mpr fun j => by
        simpa only [Complex.exp_log (hb j)] using tendsto_character_exp (Complex.log (b j))
    let O (σ : Equiv.Perm (Fin n)) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
      {x | (η * matchingProduct x.1 x.2 σ).re < (η * determinantValue x.1 x.2 U).re}
    have ho (σ : Equiv.Perm (Fin n)) : IsOpen (O σ) := by
      unfold O matchingProduct determinantValue
      apply isOpen_lt <;> fun_prop
    have ht : Tendsto (fun m => (a' m, b' m)) atTop (𝓝 (a, b)) := hA.prodMk_nhds hB
    obtain ⟨m, hm⟩ := (ht.eventually_mem
      ((isOpen_iInter_of_finite ho).mem_nhds (Set.mem_iInter.mpr hstrict))).exists
    obtain ⟨σ, hσ⟩ := (holds_iff_directional _ _ _).mp
      (h n (fun j => torusWeight (Complex.log (a j)) m)
        (fun j => torusWeight (Complex.log (b j)) m) (Complex.exp (torusStep m)) U
        (Complex.exp_ne_zero _) hU) η
    exact (not_le_of_gt (Set.mem_iInter.mp hm σ)) hσ
  · intro h n a b z U _ hU
    exact h n _ _ U hU

end

end MOC.Reformulations.NativeLinksB
