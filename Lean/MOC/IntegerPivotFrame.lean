import MOC.IntegerRayCut

/-! Pivot values give both a linear reconstruction formula and the initial
nonnegative ray expansion. -/

open BigOperators

namespace MOC.IntegerRayCut

structure PivotFrame (n d : ℕ) where
  pivot : Fin n → Fin d
  ray : Fin n → Fin d → ℤ
  factor : Fin n → ℤ
  scale : ℤ
  scale_pos : 0 < scale
  factor_nonneg : ∀ k, 0 ≤ factor k

namespace PivotFrame
noncomputable section
variable {n d : ℕ} (F : PivotFrame n d)

def space : Submodule ℝ (Fin d → ℝ) where
  carrier := {v | ∀ i, (F.scale : ℝ) * v i =
    ∑ k, v (F.pivot k) * (F.factor k : ℝ) * (F.ray k i : ℝ)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw i
    change (F.scale : ℝ) * (v i + w i) = ∑ k, (v (F.pivot k) + w (F.pivot k)) * _ * _
    simp only [add_mul, mul_add, Finset.sum_add_distrib, hv i, hw i]
  smul_mem' := by
    intro c v hv i
    change (F.scale : ℝ) * (c * v i) = ∑ k, (c * v (F.pivot k)) * _ * _
    calc
      (F.scale : ℝ) * (c * v i) = c * ((F.scale : ℝ) * v i) := by ring
      _ = c * ∑ k, v (F.pivot k) * (F.factor k : ℝ) * (F.ray k i : ℝ) := by rw [hv i]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

theorem mem_of_reconstruction (r : Fin d → ℤ)
    (h : ∀ i, F.scale * r i = ∑ k, r (F.pivot k) * F.factor k * F.ray k i) :
    realRow r ∈ F.space := by
  intro i
  change (F.scale : ℝ) * (r i : ℝ) = ∑ k, (r (F.pivot k) : ℝ) * _ * _
  exact_mod_cast h i

theorem score_mem {m : ℕ} (point : Fin d → Fin m → ℤ)
    (hp : ∀ k i, F.scale * point i k = ∑ j, point (F.pivot j) k * F.factor j * F.ray j i)
    (w : Fin m → ℝ) : (fun i => ∑ k, w k * (point i k : ℝ)) ∈ F.space := by
  have he : (fun i => ∑ k, w k * (point i k : ℝ)) = ∑ k, w k • (fun i => (point i k : ℝ)) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact F.space.sum_mem fun k _ => F.space.smul_mem _ (F.mem_of_reconstruction _ (hp k))

theorem initial_covered (s : Finset (Fin d)) (h : ∀ k, F.pivot k ∈ s) :
    Covered F.space ⟨n, F.ray, s⟩ := by
  have hs : (0 : ℝ) < F.scale := by exact_mod_cast F.scale_pos
  constructor
  · intro v hv hz
    have hzero (k : Fin n) : v (F.pivot k) = 0 := hz _ (h k)
    funext i
    change v i = 0
    have hh := hv i
    simp only [hzero, zero_mul, Finset.sum_const_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left hs.ne'
  · intro v hv hn
    let w (k : Fin n) := v (F.pivot k) * (F.factor k : ℝ) / (F.scale : ℝ)
    refine ⟨w, fun k => div_nonneg (mul_nonneg (hn _ (h k))
      (by exact_mod_cast F.factor_nonneg k)) hs.le, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRow, w]
    change v i = ∑ k, v (F.pivot k) * (F.factor k : ℝ) / (F.scale : ℝ) * (F.ray k i : ℝ)
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    apply (eq_div_iff hs.ne').mpr
    rw [mul_comm (v i) (F.scale : ℝ)]
    exact hv i

end
end PivotFrame
end MOC.IntegerRayCut
