import MOC.Geometry
import MOC.Support
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Tactic.LinearCombination

/-! The homogeneous matching incidence before passage to projective topology. -/

open BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A homogeneous two-coordinate representative of a projective point. -/
abbrev MatchingSpinor := ℂ × ℂ

/-- The bracket is the determinant of two spinors. -/
def matchingSpinorBracket (v w : MatchingSpinor) : ℂ := v.1 * w.2 - v.2 * w.1

def spinorMatchingProduct (v w : ι → MatchingSpinor) (σ : Equiv.Perm ι) : ℂ :=
  ∏ j, matchingSpinorBracket (v (σ j)) (w j)

def spinorDeterminant (U : Matrix ι ι ℂ) (v w : ι → MatchingSpinor) : ℂ :=
  ∑ σ, signedWeight U σ * spinorMatchingProduct v w σ

/-- The set of probability weights in the fiber over the given spinors. -/
def spinorIncidenceFiber (U : Matrix ι ι ℂ) (v w : ι → MatchingSpinor) :
    Set (Equiv.Perm ι → ℝ) :=
  {p ∈ stdSimplex ℝ (Equiv.Perm ι) |
    (∑ σ, (p σ : ℂ) * spinorMatchingProduct v w σ) = spinorDeterminant U v w}

private theorem mem_hull_iff_exists_simplex_weights {J : Type*} [Fintype J]
    (f : J → ℂ) (z : ℂ) :
    z ∈ convexHull ℝ (Set.range f) ↔
      ∃ p ∈ stdSimplex ℝ J, (∑ j, (p j : ℂ) * f j) = z := by
  classical
  constructor
  · intro h
    obtain ⟨κ, inst, a, y, ha, ha₁, hy, hsum⟩ := mem_convexHull_iff_exists_fintype.mp h
    letI : Fintype κ := inst
    have hy' (i : κ) : ∃ j, f j = y i := hy i
    choose j hj using hy'
    let p (k : J) : ℝ := ∑ i, if j i = k then a i else 0
    refine ⟨p, ⟨fun k => Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [ha]), ?_⟩, ?_⟩
    · unfold p
      rw [Finset.sum_comm]
      simpa using ha₁
    · calc
        _ = ∑ i, (a i : ℂ) * f (j i) := by
          simp_rw [p, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero,
            Finset.sum_mul, ite_mul, zero_mul]
          rw [Finset.sum_comm]
          simp
        _ = z := by simpa only [hj, Complex.real_smul] using hsum
  · rintro ⟨p, hp, he⟩
    exact mem_convexHull_of_exists_fintype p f hp.1 hp.2 (fun j => ⟨j, rfl⟩)
      (by simpa only [Complex.real_smul] using he)

theorem spinorIncidenceFiber_nonempty_iff (U : Matrix ι ι ℂ) (v w : ι → MatchingSpinor) :
    (spinorIncidenceFiber U v w).Nonempty ↔
      spinorDeterminant U v w ∈ convexHull ℝ (Set.range (spinorMatchingProduct v w)) :=
  (mem_hull_iff_exists_simplex_weights _ _).symm

/-- The fiber is an intersection of the simplex with a linear equation. -/
theorem convex_spinorIncidenceFiber (U : Matrix ι ι ℂ) (v w : ι → MatchingSpinor) :
    Convex ℝ (spinorIncidenceFiber U v w) := by
  let L : (Equiv.Perm ι → ℝ) →ₗ[ℝ] ℂ :=
    ∑ σ, (LinearMap.proj σ).smulRight (spinorMatchingProduct v w σ)
  have hL (p : Equiv.Perm ι → ℝ) :
      L p = ∑ σ, (p σ : ℂ) * spinorMatchingProduct v w σ := by
    simp only [L, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Complex.real_smul]
  have hf : spinorIncidenceFiber U v w =
      stdSimplex ℝ (Equiv.Perm ι) ∩ L ⁻¹' {spinorDeterminant U v w} := by
    ext p
    simp [spinorIncidenceFiber, hL]
  rw [hf]
  exact (convex_stdSimplex ℝ _).inter ((convex_singleton _).linear_preimage L)

theorem contractibleSpace_spinorIncidenceFiber (U : Matrix ι ι ℂ)
    (v w : ι → MatchingSpinor) (h : (spinorIncidenceFiber U v w).Nonempty) :
    ContractibleSpace (spinorIncidenceFiber U v w) :=
  (convex_spinorIncidenceFiber U v w).contractibleSpace h

/-- Independently rescaling each homogeneous representative by a nonzero
scalar does not change the incidence fiber. -/
theorem spinorIncidenceFiber_scale (U : Matrix ι ι ℂ) (v w : ι → MatchingSpinor)
    (x y : ι → ℂ) (hx : ∀ i, x i ≠ 0) (hy : ∀ j, y j ≠ 0) :
    spinorIncidenceFiber U (fun i => x i • v i) (fun j => y j • w j) =
      spinorIncidenceFiber U v w := by
  let c := (∏ i, x i) * (∏ j, y j)
  have hc : c ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => hx i)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hy j)
  have hbracket (i j : ι) :
      matchingSpinorBracket (x i • v i) (y j • w j) =
        (x i * y j) * matchingSpinorBracket (v i) (w j) := by
    simp only [matchingSpinorBracket, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hprod (σ : Equiv.Perm ι) :
      spinorMatchingProduct (fun i => x i • v i) (fun j => y j • w j) σ =
        c * spinorMatchingProduct v w σ := by
    simp only [spinorMatchingProduct, hbracket, c, Finset.prod_mul_distrib]
    rw [Equiv.prod_comp σ x]
  ext p
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [spinorIncidenceFiber, spinorDeterminant, hprod]
  simp_rw [mul_left_comm _ c (_ : ℂ)]
  simp only [← Finset.mul_sum, mul_right_inj' hc]

private def shearSpinor (t : ℂ) (v : MatchingSpinor) : MatchingSpinor :=
  (v.1, v.2 + t * v.1)

private theorem shearSpinor_bracket (t : ℂ) (v w : MatchingSpinor) :
    matchingSpinorBracket (shearSpinor t v) (shearSpinor t w) = matchingSpinorBracket v w := by
  simp only [matchingSpinorBracket, shearSpinor]
  ring

private theorem exists_spinor_affine_chart (v w : ι → MatchingSpinor)
    (hv : ∀ i, v i ≠ 0) (hw : ∀ j, w j ≠ 0) :
    ∃ t : ℂ, (∀ i, (shearSpinor t (v i)).2 ≠ 0) ∧
      (∀ j, (shearSpinor t (w j)).2 ≠ 0) := by
  classical
  let pole (x : MatchingSpinor) := -x.2 / x.1
  obtain ⟨t, ht⟩ := Infinite.exists_not_mem_finset
    ((Finset.univ.image fun i => pole (v i)) ∪ (Finset.univ.image fun i => pole (w i)))
  have hchart (x : MatchingSpinor) (hx : x ≠ 0) (hp : t ≠ pole x) :
      (shearSpinor t x).2 ≠ 0 := by
    intro hz
    change x.2 + t * x.1 = 0 at hz
    by_cases hx₁ : x.1 = 0
    · have hx₂ : x.2 = 0 := by simpa [hx₁] using hz
      exact hx (Prod.ext hx₁ hx₂)
    · apply hp
      exact (eq_div_iff hx₁).2 (by linear_combination hz)
  refine ⟨t, fun i => hchart (v i) (hv i) ?_, fun j => hchart (w j) (hw j) ?_⟩
  · intro h
    exact ht (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩))
  · intro h
    exact ht (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm⟩))

/-- For fixed relative eigenbases, the incidence with nonempty fibers over
all nonzero homogeneous representatives is equivalent to MOC. -/
theorem spinorIncidence_surjective_iff (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (∀ v w : ι → MatchingSpinor, (∀ i, v i ≠ 0) → (∀ j, w j ≠ 0) →
      (spinorIncidenceFiber U v w).Nonempty) ↔ ∀ a b : ι → ℂ, Holds a b U := by
  constructor
  · intro h a b
    let v (i : ι) : MatchingSpinor := (a i, 1)
    let w (j : ι) : MatchingSpinor := (-b j, 1)
    obtain ⟨p, hp, he⟩ := h v w (by intro i; simp [v]) (by intro j; simp [w])
    have hprod (σ : Equiv.Perm ι) : spinorMatchingProduct v w σ = matchingProduct a b σ := by
      simp [spinorMatchingProduct, matchingSpinorBracket, matchingProduct, v, w]
    apply holds_of_weights p hp.1 hp.2
    simpa only [spinorDeterminant, hprod, signed_determinant a b U hU] using he
  · intro h v w hv hw
    obtain ⟨t, hvt, hwt⟩ := exists_spinor_affine_chart v w hv hw
    let x := shearSpinor t ∘ v
    let y := shearSpinor t ∘ w
    let a (i : ι) := (x i).1 / (x i).2
    let b (j : ι) := -((y j).1 / (y j).2)
    let c := (∏ i, (x i).2) * (∏ j, (y j).2)
    have hprod (σ : Equiv.Perm ι) :
        spinorMatchingProduct v w σ = c * matchingProduct a b σ := by
      have hfactor (i j : ι) :
          matchingSpinorBracket (v i) (w j) = ((x i).2 * (y j).2) * (a i + b j) := by
        rw [← shearSpinor_bracket t (v i) (w j)]
        change (x i).1 * (y j).2 - (x i).2 * (y j).1 =
          ((x i).2 * (y j).2) * ((x i).1 / (x i).2 + -((y j).1 / (y j).2))
        field_simp [hvt i, hwt j] <;> ring
      simp only [spinorMatchingProduct, matchingProduct, c, hfactor, Finset.prod_mul_distrib]
      rw [Equiv.prod_comp σ (fun i => (x i).2)]
    have hdet : spinorDeterminant U v w = c * determinantValue a b U := by
      simp only [spinorDeterminant, hprod]
      simp_rw [mul_left_comm (signedWeight U _) c]
      rw [← Finset.mul_sum, signed_determinant a b U hU]
    exact (spinorIncidenceFiber_nonempty_iff _ _ _).mpr
      (hull_of_common_factor hdet hprod (h a b))

end

end MOC
