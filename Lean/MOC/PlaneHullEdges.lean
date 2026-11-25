import MOC.Support

/-! Directed edges and finite supporting projections in the complex plane. -/

namespace MOC

noncomputable section

/-- The oriented area form for two vectors in the complex plane. -/
def planeCross (u v : ℂ) : ℝ :=
  u.re * v.im - u.im * v.re

theorem planeCross_edge_direction (a b z : ℂ) :
    planeCross (b - a) (z - a) =
      ((⟨-(b - a).im, -(b - a).re⟩ : ℂ) * z).re -
        ((⟨-(b - a).im, -(b - a).re⟩ : ℂ) * a).re := by
  simp only [planeCross, Complex.sub_re, Complex.sub_im, Complex.mul_re]
  ring

/-- At a projection-maximizing vertex with a positive turn, its two incident
edge inequalities bound that projection of the test point. -/
private theorem planeProjection_le_of_incident_edges (u v w z η : ℂ)
    (ht : 0 < planeCross (v - u) (w - v))
    (hin : 0 ≤ planeCross (v - u) (z - u))
    (hout : 0 ≤ planeCross (w - v) (z - v))
    (hu : (η * u).re ≤ (η * v).re) (hw : (η * w).re ≤ (η * v).re) :
    (η * z).re ≤ (η * v).re := by
  let d := u - v
  let e := w - v
  let y := z - v
  have hdet : planeCross e d = planeCross (v - u) (w - v) := by
    simp only [e, d, planeCross, Complex.sub_re, Complex.sub_im]
    ring
  have hbefore : -planeCross d y = planeCross (v - u) (z - u) := by
    simp only [d, y, planeCross, Complex.sub_re, Complex.sub_im]
    ring
  have hleft : 0 ≤ -planeCross d y := hbefore.symm ▸ hin
  have hd : (η * d).re ≤ 0 := by
    simpa only [d, mul_sub, Complex.sub_re, sub_nonpos] using hu
  have he : (η * e).re ≤ 0 := by
    simpa only [e, mul_sub, Complex.sub_re, sub_nonpos] using hw
  have hidentity : planeCross e d * (η * y).re =
      planeCross e y * (η * d).re + (-planeCross d y) * (η * e).re := by
    simp only [planeCross, Complex.mul_re]
    ring
  have hmul : planeCross e d * (η * y).re ≤ planeCross e d * 0 := by
    rw [hidentity, mul_zero]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hout hd)
      (mul_nonpos_of_nonneg_of_nonpos hleft he)
  have hy := (mul_le_mul_left (hdet.symm ▸ ht)).mp hmul
  simpa only [y, mul_sub, Complex.sub_re, sub_nonpos] using hy

/-- If each vertex has two incident supporting edges with positive turn,
meeting all their half-planes suffices for membership in the vertex hull. -/
theorem mem_planeHull_of_edges {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℂ) (prev next : ι → ι) (z : ℂ) (hcycle : ∀ i, next (prev i) = i)
    (hturn : ∀ i, 0 < planeCross (v i - v (prev i)) (v (next i) - v i))
    (hedge : ∀ i, 0 ≤ planeCross (v (next i) - v i) (z - v i)) :
    z ∈ convexHull ℝ (Set.range v) := by
  apply mem_hull_of_directional_bound v z
  intro η
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => (η * v i).re) Finset.univ_nonempty
  have hin := hedge (prev i)
  rw [hcycle i] at hin
  exact ⟨i, planeProjection_le_of_incident_edges (v (prev i)) (v i) (v (next i)) z η
    (hturn i) hin (hedge i) (hmax (prev i) (Finset.mem_univ _)) (hmax (next i) (Finset.mem_univ _))⟩

end

end MOC
