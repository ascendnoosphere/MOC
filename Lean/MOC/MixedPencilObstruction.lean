import MOC.Support

namespace MOC

noncomputable section

/-- Coefficients in the order (1,t,u,tu). -/
abbrev BilinearCoefficients := Fin 4 → ℂ

def evalBilinear (a : BilinearCoefficients) (t u : ℂ) : ℂ :=
  a 0 + a 1 * t + a 2 * u + a 3 * (t * u)

private abbrev Slot := Sum Unit Bool

private def zeroTraceBasis : Slot → BilinearCoefficients
  | .inl _ => ![1, 0, 0, -1]
  | .inr false => ![0, 1, 0, 0]
  | .inr true => ![0, 0, 1, 0]

private def corner (b c : Bool) : ℂ :=
  (if b then 1 else -1) - (if c then 1 else -1) * Complex.I

private def pencilVertices (j : Slot × Bool × Bool) : BilinearCoefficients :=
  (3 * corner j.2.1 j.2.2) • zeroTraceBasis j.1

private def pencilTarget : BilinearCoefficients := ![1, 0, 0, 1]

private theorem exists_corner_ge_norm (z : ℂ) :
    ∃ b c, ‖z‖ ≤ (corner b c * z).re := by
  let b := decide (0 ≤ z.re)
  let c := decide (0 ≤ z.im)
  refine ⟨b, c, ?_⟩
  have h : (corner b c * z).re = |z.re| + |z.im| := by
    dsimp [b, c, corner]
    by_cases hb : 0 ≤ z.re <;> by_cases hc : 0 ≤ z.im <;>
      simp [hb, hc, abs_of_nonneg, abs_of_neg, lt_of_not_ge,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
  rw [h]
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hv : 0 ≤ |z.re| * |z.im| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [sq_abs z.re, sq_abs z.im, norm_nonneg z, abs_nonneg z.re, abs_nonneg z.im]

private theorem bilinear_eval_identity (v w : ℂ)
    (k : ℂ) :
    (k * (1 + v*w)) ^ 2 = (k * (1 - v*w)) ^ 2 + 4 * (k*v) * (k*w) := by
  ring

/-- Even a finite simultaneous hull cannot be tested by evaluations in two
complex variables. This is an abstract counterexample, not a matching-product
or determinant counterexample. -/
theorem exists_pointwise_bilinear_not_coefficient_hull :
    ∃ (J : Type) (_ : Fintype J) (v : J → BilinearCoefficients)
      (z : BilinearCoefficients),
      (∀ t u, evalBilinear z t u ∈
        convexHull ℝ (Set.range (fun j => evalBilinear (v j) t u))) ∧
      z ∉ convexHull ℝ (Set.range v) := by
  classical
  refine ⟨Slot × Bool × Bool, inferInstance, pencilVertices, pencilTarget, ?_, ?_⟩
  · intro t u
    refine mem_hull_of_directional_bound _ _ (fun k => ?_)
    let q (s : Slot) := evalBilinear (zeroTraceBasis s) t u
    have hq0 : q (.inl ()) = 1 - t*u := by simp [q, zeroTraceBasis, evalBilinear, sub_eq_add_neg]
    have hq1 : q (.inr false) = t := by simp [q, zeroTraceBasis, evalBilinear]
    have hq2 : q (.inr true) = u := by simp [q, zeroTraceBasis, evalBilinear]
    obtain ⟨s, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset Slot)
      (fun s => ‖k * q s‖) Finset.univ_nonempty
    let m := ‖k * q s‖
    have h0 : ‖k * (1 - t*u)‖ ≤ m := by
      simpa only [hq0] using hmax (.inl ()) (Finset.mem_univ _)
    have h1 : ‖k * t‖ ≤ m := by
      simpa only [hq1] using hmax (.inr false) (Finset.mem_univ _)
    have h2 : ‖k * u‖ ≤ m := by
      simpa only [hq2] using hmax (.inr true) (Finset.mem_univ _)
    have hsq : ‖k * (1+t*u)‖ ^ 2 ≤ ‖k * (1-t*u)‖ ^ 2 + 4 * ‖k*t‖ * ‖k*u‖ := by
      calc
        _ = ‖(k * (1 - t*u)) ^ 2 + 4 * (k*t) * (k*u)‖ := by
          rw [← norm_pow, bilinear_eval_identity]
        _ ≤ _ := by
          have h := norm_add_le ((k * (1 - t*u)) ^ 2) ((4 : ℂ) * (k*t) * (k*u))
          rw [norm_pow, norm_mul ((4 : ℂ) * (k*t)), norm_mul (4 : ℂ)] at h
          simpa using h
    have hbound : ‖k * (1+t*u)‖ ≤ 3*m := by
      have hSq0 : ‖k * (1-t*u)‖ ^ 2 ≤ m^2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) h0 _
      have hMul : ‖k*t‖ * ‖k*u‖ ≤ m*m :=
        mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
      nlinarith [norm_nonneg (k * (1+t*u)), norm_nonneg (k * q s)]
    obtain ⟨b, c, hb⟩ := exists_corner_ge_norm (k * q s)
    refine ⟨(s,b,c), ?_⟩
    have hv : evalBilinear (pencilVertices (s,b,c)) t u = 3 * corner b c * q s := by
      unfold pencilVertices q evalBilinear
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hv]
    have hcom : k * (3 * corner b c * q s) = 3 * (corner b c * (k * q s)) := by ring
    rw [hcom]
    have hz : evalBilinear pencilTarget t u = 1+t*u := by simp [pencilTarget, evalBilinear]
    rw [hz]
    exact (Complex.re_le_norm _).trans (hbound.trans (by simpa [Complex.mul_re, m] using mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ 3)))
  · intro h
    let trC : BilinearCoefficients →ₗ[ℂ] ℂ :=
      (LinearMap.proj (0 : Fin 4) : BilinearCoefficients →ₗ[ℂ] ℂ) +
      (LinearMap.proj (3 : Fin 4) : BilinearCoefficients →ₗ[ℂ] ℂ)
    let tr := trC.restrictScalars ℝ
    have hs : Set.range pencilVertices ⊆ LinearMap.ker tr := by
      rintro _ ⟨⟨s,b,c⟩, rfl⟩
      have hzero : trC (zeroTraceBasis s) = 0 := by
        rcases s with x | x
        · simp [trC, zeroTraceBasis]
        · cases x <;> simp [trC, zeroTraceBasis]
      change trC ((3 * corner b c) • zeroTraceBasis s) = 0
      rw [map_smul, hzero, smul_zero]
    have h' := convexHull_min hs (LinearMap.ker tr).convex h
    have hneq : tr pencilTarget ≠ 0 := by
      simp [tr, trC, pencilTarget, LinearMap.restrictScalars_apply]
    exact hneq h'

end
end MOC
