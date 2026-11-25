import MOC.ProjectiveTransport
import MOC.SpectralKKT

/-! A finite, pole-free replacement for projective three-point normalization.
For applying the fractional covariance to MOC, see Drury,
DOI: 10.13001/1081-3810.1239. -/

open Set Filter
open scoped Topology

namespace MOC

/-- Three distinct signed spectral entries can be sent to (0,1,R)
with arbitrarily large real (R), without putting a pole on any of a
prescribed finite set of complex points. No determinant transform is
taken at an input pole. -/
theorem exists_pole_avoiding_three_point_approximation
    (S : Set ℂ) (hS : S.Finite) (x y z : ℂ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (M : ℝ) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧
      (∀ s ∈ S, γ * s + δ ≠ 0) ∧
      fractionalMap α β γ δ x = 0 ∧ fractionalMap α β γ δ y = 1 ∧
      ∃ R : ℝ, M < R ∧ fractionalMap α β γ δ z = (R : ℂ) := by
  classical
  let N (s : ℂ) := (s - x) * (y - z)
  let D (s : ℂ) := (s - z) * (y - x)
  let F : Set ℝ := (fun t : ℝ => (t : ℂ)) ⁻¹' ((fun s => -(D s) / N s) '' S)
  have hF : F.Finite := (hS.image _).preimage Complex.ofReal_injective.injOn
  let B : ℝ := |M| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hInt : (Ioo (0 : ℝ) B⁻¹).Infinite := Set.Ioo_infinite (inv_pos.mpr hB)
  have hnempty : (Ioo (0 : ℝ) B⁻¹ \ F).Nonempty := (hInt.diff hF).nonempty
  obtain ⟨t,⟨ht,htB⟩,htF⟩ := hnempty
  let e : ℂ := (t : ℂ)
  have he : e ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have he1 : 1 + e ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re, e, Complex.ofReal_re] at hh
    linarith
  let α : ℂ := (1 + e) * (y - z)
  let β : ℂ := -α * x
  let γ : ℂ := (y - x) + e * (y - z)
  let δ : ℂ := -(y - x) * z - e * (y - z) * x
  have hden (s : ℂ) : γ * s + δ = D s + e * N s := by simp only [γ,δ,D,N]; ring
  have hnum (s : ℂ) : α * s + β = (1 + e) * N s := by simp only [α,β,N]; ring
  have hdet : α * δ - β * γ ≠ 0 := by
    have heq : α * δ - β * γ = α * (y - x) * (x - z) := by simp only [β,γ,δ]; ring
    rw [heq]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero he1 (sub_ne_zero.mpr hyz))
      (sub_ne_zero.mpr hxy.symm)) (sub_ne_zero.mpr hxz)
  have hnD (s : ℂ) (hs : s ∈ S) : γ * s + δ ≠ 0 := by
    rw [hden]
    intro h
    by_cases hn : N s = 0
    · have hxs : s = x := sub_eq_zero.mp ((mul_eq_zero.mp hn).resolve_right (sub_ne_zero.mpr hyz))
      have hz : D s = 0 := by simpa only [hn,mul_zero,add_zero] using h
      exact (mul_ne_zero (sub_ne_zero.mpr hxz) (sub_ne_zero.mpr hxy.symm))
        (by simpa only [D,hxs] using hz)
    · have heq : e = -(D s) / N s := (eq_div_iff hn).mpr (eq_neg_of_add_eq_zero_right h)
      exact htF ⟨s,hs,heq.symm⟩
  refine ⟨α,β,γ,δ,hdet,hnD,?_,?_,1+t⁻¹,?_,?_⟩
  · unfold fractionalMap
    rw [hnum]
    simp [N]
  · unfold fractionalMap
    rw [hnum,hden, show D y = N y by simp only [D,N]; ring, show N y + e * N y = (1+e) * N y by ring]
    exact div_self (mul_ne_zero he1 (mul_ne_zero (sub_ne_zero.mpr hxy.symm) (sub_ne_zero.mpr hyz)))
  · have hinv : B < t⁻¹ := (lt_inv_comm₀ hB ht).mpr htB
    have hm : M ≤ |M| := le_abs_self _
    dsimp only [B] at hinv
    linarith
  · unfold fractionalMap
    rw [hnum,hden, show D z = 0 by simp [D],zero_add, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_inv]
    change (1 + e) * N z / (e * N z) = 1 + e⁻¹
    have hn : N z ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hxz.symm) (sub_ne_zero.mpr hyz)
    field_simp [he,hn]
    <;> ring

end MOC
