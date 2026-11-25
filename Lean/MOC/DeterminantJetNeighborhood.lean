import MOC.AntipodalKernelJet
import MOC.SpectralAffineContact
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Algebra.Polynomial

/-! An interior leading-jet certificate gives the actual matching-hull
inclusion on a sufficiently short affine spectral path. Boundary jets do
not meet the hypothesis. -/

open BigOperators Matrix Polynomial Filter
open scoped Topology

namespace MOC
noncomputable section

private theorem eventually_mem_hull_of_continuous {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ → ℂ) (p : ℂ → ℂ)
    (hv : ∀ j, ContinuousAt (v j) 0) (hp : ContinuousAt p 0)
    (hin : 0 ∈ interior (convexHull ℝ (Set.range fun j => v j 0 - p 0))) :
    ∀ᶠ t in 𝓝 (0 : ℂ), p t ∈ convexHull ℝ (Set.range fun j => v j t) := by
  let s (j : J) := v j 0 - p 0
  obtain ⟨δ, hδ, hmargin⟩ := affine_margin_of_zero_mem_interior s hin
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ j, ‖v j t - p t - s j‖ < δ := by
    apply Filter.eventually_all.mpr
    intro j
    have hh : ContinuousAt (fun t => v j t - p t - s j) (0 : ℂ) :=
      ((hv j).sub hp).sub continuousAt_const
    have he := hh.norm.eventually_lt (show ContinuousAt (fun _ : ℂ => δ) 0 from continuousAt_const)
      (by simpa [s] using hδ)
    exact he
  filter_upwards [hnear] with t ht
  apply mem_hull_of_directional_bound
  intro k
  obtain ⟨j, hj⟩ := hmargin k
  refine ⟨j, ?_⟩
  have hneg : -(‖k‖ * δ) ≤ (k * (v j t - p t - s j)).re := by
    calc
      -(‖k‖ * δ) ≤ -‖k * (v j t - p t - s j)‖ := by
        rw [norm_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_left (ht j).le (norm_nonneg k))
      _ ≤ _ := (abs_le.mp (Complex.abs_re_le_norm _)).1
  rw [mul_sub, mul_sub, Complex.sub_re, Complex.sub_re] at hneg
  rw [mul_comm ‖k‖ δ] at hneg
  rw [mul_comm (s j) k] at hj
  linarith only [hj, hneg]

/-- The rescaled polynomial jets are continuous even at zero. A uniform
support margin at that point rules out a strict gap nearby. -/
theorem eventually_polynomial_hull_of_interior_jet {J : Type*} [Fintype J] [Nonempty J]
    (f : J → ℂ[X]) (p : ℂ[X]) (r : ℕ) (v : J → ℂ[X]) (q : ℂ[X])
    (hf : ∀ j, f j = X ^ r * v j) (hp : p = X ^ r * q)
    (hin : 0 ∈ interior (convexHull ℝ (Set.range fun j => (v j).coeff 0 - q.coeff 0))) :
    ∀ᶠ t in 𝓝 (0 : ℂ), p.eval t ∈ convexHull ℝ (Set.range fun j => (f j).eval t) := by
  have hh := eventually_mem_hull_of_continuous (fun j t => (v j).eval t) q.eval
    (fun j => (v j).continuous.continuousAt) q.continuous.continuousAt
    (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hin)
  filter_upwards [hh] with t ht
  let L : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ (t ^ r)
  have hl : L (q.eval t) = p.eval t := by simp [L, hp]
  rw [← hl]
  have he (j : J) : L ((v j).eval t) = (f j).eval t := by simp [L, hf]
  have hset : (Set.range fun j => (f j).eval t) =
      L '' (Set.range fun j => (v j).eval t) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, he j⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (he j).symm⟩
  rw [hset, ← L.image_convexHull]
  exact ⟨_, ht, rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matching product along an affine variation of both spectra. -/
def affineMatchingPoly (a b v w : ι → ℂ) (σ : Equiv.Perm ι) : ℂ[X] :=
  ∏ j, (C (a (σ j) + b j) + X * C (v (σ j) + w j))

omit [DecidableEq ι] in
theorem affineMatchingPoly_eval (a b v w : ι → ℂ) (σ : Equiv.Perm ι) (t : ℂ) :
    (affineMatchingPoly a b v w σ).eval t =
      matchingProduct (fun i => a i + t * v i) (fun j => b j + t * w j) σ := by
  unfold affineMatchingPoly matchingProduct
  rw [← Polynomial.coe_evalRingHom, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  ring

omit [DecidableEq ι] in
/-- Each canceled matched sum contributes one factor of the parameter.
The coefficient at exactly that order multiplies the uncanceled center
factors and the velocities in the canceled slots. -/
theorem affineMatchingPoly_zero_slots (a b v w : ι → ℂ) (σ : Equiv.Perm ι) :
    let Z := Finset.univ.filter (fun j => a (σ j) + b j = 0)
    let r := Z.card
    (∀ k < r, (affineMatchingPoly a b v w σ).coeff k = 0) ∧
      (affineMatchingPoly a b v w σ).coeff r =
        (∏ j ∈ Z, (v (σ j) + w j)) *
          (∏ j ∈ Finset.univ.filter (fun j => a (σ j) + b j ≠ 0), (a (σ j) + b j)) := by
  classical
  intro Z r
  let N := Finset.univ.filter (fun j => a (σ j) + b j ≠ 0)
  let u (j : ι) := a (σ j) + b j
  let s (j : ι) := v (σ j) + w j
  let f (j : ι) : ℂ[X] := C (u j) + X * C (s j)
  let q : ℂ[X] := (∏ j ∈ Z, C (s j)) * ∏ j ∈ N, f j
  have hz : (∏ j ∈ Z, f j) = ∏ j ∈ Z, X * C (s j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have h : u j = 0 := (Finset.mem_filter.mp hj).2
    simp [f, h]
  have hf : affineMatchingPoly a b v w σ = X ^ r * q := by
    change (∏ j, f j) = _
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => u j = 0) f]
    change (∏ j ∈ Z, f j) * (∏ j ∈ N, f j) = _
    rw [hz, Finset.prod_mul_distrib, Finset.prod_const, mul_assoc]
  refine ⟨Polynomial.X_pow_dvd_iff.mp ⟨q, hf⟩, ?_⟩
  rw [hf, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom]
  change Polynomial.evalRingHom 0 ((∏ j ∈ Z, C (s j)) * ∏ j ∈ N, f j) =
    (∏ j ∈ Z, s j) * ∏ j ∈ N, u j
  simp only [map_mul, map_prod, Polynomial.coe_evalRingHom, f, Polynomial.eval_C,
    Polynomial.eval_X, zero_mul, add_zero, Polynomial.eval_add, Polynomial.eval_mul]


theorem affineDetPoly_eval (S H : Matrix ι ι ℂ) (t : ℂ) :
    (affineDetPoly S H).eval t = (S + t • H).det := by
  rw [affineDetPoly, ← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, add_right_inj]

/-- A finite subfamily of matchings with the same vanishing order suffices.
If its leading-coefficient hull contains the determinant coefficient in
its interior, that affine spectral path satisfies the full conjecture
for every sufficiently small parameter, not just in the limit. -/
theorem eventually_holds_affine_of_interior_jet {J : Type*} [Fintype J] [Nonempty J]
    (a b v w : ι → ℂ) (U : Matrix ι ι ℂ) (σ : J → Equiv.Perm ι) (r : ℕ)
    (hdet : ∀ k < r, (affineDetPoly (diagonal a + U * diagonal b * Uᴴ)
      (diagonal v + U * diagonal w * Uᴴ)).coeff k = 0)
    (hm : ∀ j k, k < r → (affineMatchingPoly a b v w (σ j)).coeff k = 0)
    (hin : 0 ∈ interior (convexHull ℝ (Set.range fun j =>
      (affineMatchingPoly a b v w (σ j)).coeff r -
        (affineDetPoly (diagonal a + U * diagonal b * Uᴴ)
          (diagonal v + U * diagonal w * Uᴴ)).coeff r))) :
    ∀ᶠ t in 𝓝 (0 : ℂ), Holds (fun i => a i + t * v i) (fun j => b j + t * w j) U := by
  classical
  let p := affineDetPoly (diagonal a + U * diagonal b * Uᴴ)
    (diagonal v + U * diagonal w * Uᴴ)
  let f (j : J) := affineMatchingPoly a b v w (σ j)
  obtain ⟨q, hq⟩ : X ^ r ∣ p := Polynomial.X_pow_dvd_iff.mpr hdet
  have hv (j : J) : ∃ Q, f j = X ^ r * Q := Polynomial.X_pow_dvd_iff.mpr (hm j)
  choose V hV using hv
  have hlower (l : ℂ[X]) (L : ℂ[X]) (h : l = X ^ r * L) :
      l.coeff r = L.coeff 0 := by
    rw [h, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
  have he := eventually_polynomial_hull_of_interior_jet f p r V q hV hq (by
    change 0 ∈ interior (convexHull ℝ (Set.range fun j => (f j).coeff r - p.coeff r)) at hin
    have hq0 : p.coeff r = q.coeff 0 := hlower p q hq
    have hV0 (j : J) : (f j).coeff r = (V j).coeff 0 := hlower (f j) (V j) (hV j)
    simp_rw [← hq0, ← hV0]
    exact hin)
  filter_upwards [he] with t ht
  have hmat (x y : ι → ℂ) :
      diagonal (fun i => x i + t * y i) = diagonal x + t • diagonal y := by
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul, h]
  have hvalue : p.eval t =
      determinantValue (fun i => a i + t * v i) (fun j => b j + t * w j) U := by
    dsimp only [p]
    rw [affineDetPoly_eval, determinantValue, hmat, hmat, Matrix.mul_add,
      Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, smul_add]
    abel_nf
  rw [hvalue] at ht
  apply convexHull_mono ?_ ht
  rintro _ ⟨j, rfl⟩
  exact ⟨σ j, (affineMatchingPoly_eval a b v w (σ j) t).symm⟩

end
end MOC
