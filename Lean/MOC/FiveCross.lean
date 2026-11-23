import MOC.Geometry
import MOC.Support
import MOC.TwoValues
import Mathlib.Data.Fintype.Perm
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The order-five square and its center. One spectrum is a real dilation
of the other. Four support bounds hold for every relative unitary. -/

open BigOperators Matrix

namespace MOC

namespace FiveCross

private def mark : Fin 5 → GaussianInt := ![0, 1, -1, ⟨0, 1⟩, ⟨0, -1⟩]

/-- The origin and the four fourth roots of unity, in the stated order. -/
def spectrum (j : Fin 5) : ℂ := GaussianInt.toComplex (mark j)

-- Coefficients of the matching product in the dilation parameter.
private def coeff (σ : Equiv.Perm (Fin 5)) (k : Fin 5) : GaussianInt :=
  let x := fun j => mark (σ j)
  let a := x 1 * x 2
  let b := x 1 * mark 2 + x 2 * mark 1
  let c := mark 1 * mark 2
  let d := x 3 * x 4
  let e := x 3 * mark 4 + x 4 * mark 3
  let f := mark 3 * mark 4
  x 0 * ![a*d, a*e+b*d, a*f+b*e+c*d, b*f+c*e, c*f] k

private theorem matching_eq (σ : Equiv.Perm (Fin 5)) (t : ℝ) :
    matchingProduct spectrum (fun j => (t : ℂ) * spectrum j) σ =
      ∑ k : Fin 5, (t : ℂ) ^ k.val * GaussianInt.toComplex (coeff σ k) := by
  simp [matchingProduct, Fin.prod_univ_succ, Fin.sum_univ_succ, coeff, spectrum,
    show mark 0 = 0 from rfl, map_mul, map_add]
  ring

private def radiusCoeff : Fin 5 → ℤ := ![0,1,3,3,1]

private theorem radius_eq (t : ℝ) :
    t * (1+t)^3 = ∑ k : Fin 5, t ^ k.val * (radiusCoeff k : ℝ) := by
  simp [Fin.sum_univ_succ, radiusCoeff]
  ring

private def direction : Fin 4 → GaussianInt :=
  ![⟨-1,-1⟩, ⟨-1,1⟩, ⟨1,-1⟩, ⟨1,1⟩]

private abbrev Term := Finset (Fin 5) × Finset (Fin 5) × ℕ
private def zeroTerm : Term := (∅, ∅, 0)

-- Each entry gives a row set, a column set and an integer coefficient.
private def terms : Fin 4 → Fin 5 → Fin 13 → Term :=
  ![![
    fun _ => zeroTerm,
    fun k => (![ ({0}, {0}, 1), ({0}, {1}, 2), ({0}, {4}, 2), zeroTerm ] : Fin 4 → Term) ⟨min k.val 3, by omega⟩,
    ![({0}, {0}, 3), ({0, 1}, {1, 4}, 2), ({0, 1}, {2, 3}, 2), ({0, 1}, {3, 4}, 2), ({0, 2}, {1, 2}, 2), ({0, 2}, {1, 3}, 2), ({0, 2}, {2, 4}, 2), ({0, 3}, {1, 3}, 2), ({0, 3}, {2, 4}, 2), ({0, 3}, {3, 4}, 2), ({0, 4}, {1, 2}, 2), ({0, 4}, {1, 4}, 2), ({0, 4}, {2, 3}, 2)],
    ![({0}, {0}, 3), ({0, 1}, {2, 4}, 2), ({0, 2}, {2, 4}, 2), ({0, 3}, {1, 3}, 2), ({0, 4}, {1, 3}, 2), ({1, 3}, {0, 2}, 2), ({1, 3}, {0, 3}, 2), ({1, 4}, {0, 1}, 2), ({1, 4}, {0, 4}, 2), ({2, 3}, {0, 1}, 2), ({2, 3}, {0, 4}, 2), ({2, 4}, {0, 2}, 2), ({2, 4}, {0, 3}, 2)],
    fun k => (![ ({0}, {0}, 1), ({1}, {0}, 2), ({4}, {0}, 2), zeroTerm ] : Fin 4 → Term) ⟨min k.val 3, by omega⟩
  ],
  ![
    fun _ => zeroTerm,
    fun k => (![ ({0}, {0}, 1), ({0}, {1}, 2), ({0}, {3}, 2), zeroTerm ] : Fin 4 → Term) ⟨min k.val 3, by omega⟩,
    ![({0}, {0}, 3), ({0, 1}, {1, 3}, 2), ({0, 1}, {2, 4}, 2), ({0, 1}, {3, 4}, 2), ({0, 2}, {1, 2}, 2), ({0, 2}, {1, 4}, 2), ({0, 2}, {2, 3}, 2), ({0, 3}, {1, 2}, 2), ({0, 3}, {1, 3}, 2), ({0, 3}, {2, 4}, 2), ({0, 4}, {1, 4}, 2), ({0, 4}, {2, 3}, 2), ({0, 4}, {3, 4}, 2)],
    ![({0}, {0}, 3), ({0, 1}, {2, 3}, 2), ({0, 2}, {2, 3}, 2), ({0, 3}, {1, 4}, 2), ({0, 4}, {1, 4}, 2), ({1, 3}, {0, 1}, 2), ({1, 3}, {0, 3}, 2), ({1, 4}, {0, 2}, 2), ({1, 4}, {0, 4}, 2), ({2, 3}, {0, 2}, 2), ({2, 3}, {0, 4}, 2), ({2, 4}, {0, 1}, 2), ({2, 4}, {0, 3}, 2)],
    fun k => (![ ({0}, {0}, 1), ({1}, {0}, 2), ({3}, {0}, 2), zeroTerm ] : Fin 4 → Term) ⟨min k.val 3, by omega⟩
  ],
  ![
    fun _ => zeroTerm,
    fun k => (![ ({0}, {0}, 1), ({0}, {2}, 2), ({0}, {4}, 2), zeroTerm ] : Fin 4 → Term) ⟨min k.val 3, by omega⟩,
    ![({0}, {0}, 3), ({0, 1}, {1, 2}, 2), ({0, 1}, {1, 4}, 2), ({0, 1}, {2, 3}, 2), ({0, 2}, {1, 3}, 2), ({0, 2}, {2, 4}, 2), ({0, 2}, {3, 4}, 2), ({0, 3}, {1, 4}, 2), ({0, 3}, {2, 3}, 2), ({0, 3}, {3, 4}, 2), ({0, 4}, {1, 2}, 2), ({0, 4}, {1, 3}, 2), ({0, 4}, {2, 4}, 2)],
    ![({0}, {0}, 3), ({0, 1}, {1, 4}, 2), ({0, 2}, {1, 4}, 2), ({0, 3}, {2, 3}, 2), ({0, 4}, {2, 3}, 2), ({1, 3}, {0, 2}, 2), ({1, 3}, {0, 4}, 2), ({1, 4}, {0, 1}, 2), ({1, 4}, {0, 3}, 2), ({2, 3}, {0, 1}, 2), ({2, 3}, {0, 3}, 2), ({2, 4}, {0, 2}, 2), ({2, 4}, {0, 4}, 2)],
    fun k => (![ ({0}, {0}, 1), ({2}, {0}, 2), ({4}, {0}, 2), zeroTerm ] : Fin 4 → Term) ⟨min k.val 3, by omega⟩
  ],
  ![
    fun _ => zeroTerm,
    fun k => (![ ({0}, {0}, 1), ({0}, {2}, 2), ({0}, {3}, 2), zeroTerm ] : Fin 4 → Term) ⟨min k.val 3, by omega⟩,
    ![({0}, {0}, 3), ({0, 1}, {1, 2}, 2), ({0, 1}, {1, 3}, 2), ({0, 1}, {2, 4}, 2), ({0, 2}, {1, 4}, 2), ({0, 2}, {2, 3}, 2), ({0, 2}, {3, 4}, 2), ({0, 3}, {1, 2}, 2), ({0, 3}, {1, 4}, 2), ({0, 3}, {2, 3}, 2), ({0, 4}, {1, 3}, 2), ({0, 4}, {2, 4}, 2), ({0, 4}, {3, 4}, 2)],
    ![({0}, {0}, 3), ({0, 1}, {1, 3}, 2), ({0, 2}, {1, 3}, 2), ({0, 3}, {2, 4}, 2), ({0, 4}, {2, 4}, 2), ({1, 3}, {0, 1}, 2), ({1, 3}, {0, 4}, 2), ({1, 4}, {0, 2}, 2), ({1, 4}, {0, 3}, 2), ({2, 3}, {0, 2}, 2), ({2, 3}, {0, 3}, 2), ({2, 4}, {0, 1}, 2), ({2, 4}, {0, 4}, 2)],
    fun k => (![ ({0}, {0}, 1), ({2}, {0}, 2), ({3}, {0}, 2), zeroTerm ] : Fin 4 → Term) ⟨min k.val 3, by omega⟩
  ]]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem certificate : ∀ (j : Fin 4) (d : Fin 5) (σ : Equiv.Perm (Fin 5)),
    radiusCoeff d + (direction j * coeff σ d).re =
      ∑ k : Fin 13, if (terms j d k).2.1.map σ.toEmbedding = (terms j d k).1
        then ((terms j d k).2.2 : ℤ) else 0 := by
  letI := fintypePerm (α := Fin 5)
  decide +kernel

private theorem bound (t : ℝ) (ht : 0 ≤ t) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : IsUnitary U) (j : Fin 4) :
    -(t*(1+t)^3) ≤
      (GaussianInt.toComplex (direction j) *
        determinantValue spectrum (fun i => (t : ℂ) * spectrum i) U).re := by
  apply support_of_minor_gap_decomposition spectrum _ _ _ U hU
    (fun p : Fin 5 × Fin 13 => (terms j p.1 p.2).1)
    (fun p => (terms j p.1 p.2).2.1)
    (fun p => t ^ p.1.val * ((terms j p.1 p.2).2.2 : ℝ))
  · intro p
    exact mul_nonneg (pow_nonneg ht _) (Nat.cast_nonneg _)
  · intro σ
    rw [matching_eq, radius_eq, sub_neg_eq_add, Finset.mul_sum, Complex.re_sum,
      Fintype.sum_prod_type]
    simp_rw [← Complex.ofReal_pow, mul_left_comm (GaussianInt.toComplex (direction j)),
      Complex.re_ofReal_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [← mul_add, add_comm]
    have hc := congrArg (fun z : ℤ => (z : ℝ)) (certificate j d σ)
    simp only [Int.cast_add, Int.cast_sum, Int.cast_ite, Int.cast_zero, Int.cast_natCast,
      GaussianInt.to_real_re, map_mul] at hc
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp_all

private def vertex : Fin 4 → GaussianInt := ![1,-1,⟨0,1⟩,⟨0,-1⟩]
private def swapIndex : Fin 4 → Fin 5 := ![2,1,4,3]

private theorem vertex_coeff : ∀ (j : Fin 4) (d : Fin 5),
    coeff (Equiv.swap 0 (swapIndex j)) d = (radiusCoeff d : GaussianInt) * vertex j := by
  decide +kernel

private theorem vertex_mem (t : ℝ) (j : Fin 4) :
    (↑(t*(1+t)^3) : ℂ) * GaussianInt.toComplex (vertex j) ∈
      Set.range (matchingProduct spectrum (fun i => (t : ℂ) * spectrum i)) := by
  refine ⟨Equiv.swap 0 (swapIndex j), ?_⟩
  rw [matching_eq, radius_eq, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  simp [vertex_coeff, map_mul, mul_assoc]

/-- The diamond with vertices at the four axis intercepts contains each
point that satisfies the four supporting inequalities. -/
private theorem diamond {R : ℝ} (hR : 0 < R) (z : ℂ)
    (h : ∀ k : Fin 4, -R ≤ (GaussianInt.toComplex (direction k) * z).re) :
    z ∈ convexHull ℝ (Set.range (fun j : Fin 4 => (R : ℂ) * GaussianInt.toComplex (vertex j))) := by
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  norm_num [direction, Complex.mul_re] at h₀ h₁ h₂ h₃
  let a := R + z.re + z.im
  let b := R + z.re - z.im
  let c := R - z.re + z.im
  let d := R - z.re - z.im
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hd : 0 ≤ d := by dsimp [d]; linarith
  let w : Fin 4 → ℝ := ![a*b, c*d, a*c, b*d]
  let μ : Fin 4 → ℝ := fun j => w j / (4*R^2)
  have hw : ∀ j, 0 ≤ μ j := by
    intro j
    apply div_nonneg _ (by positivity)
    fin_cases j <;> simp [w] <;> positivity
  have hs : ∑ j, μ j = 1 := by
    simp [μ, w, Fin.sum_univ_succ, a, b, c, d]
    field_simp [ne_of_gt hR] <;> ring
  refine mem_convexHull_of_exists_fintype μ _ hw hs (fun j => ⟨j, rfl⟩) ?_
  apply Complex.ext <;>
    simp [μ, w, Fin.sum_univ_succ, vertex, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, a, b, c, d] <;> field_simp [ne_of_gt hR] <;> ring

/-- Each nonnegative real dilation of the five-point cross satisfies MOC
for every relative unitary. -/
theorem holds_dilation (t : ℝ) (ht : 0 ≤ t) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : IsUnitary U) : Holds spectrum (fun i => (t : ℂ) * spectrum i) U := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    exact holds_of_two_values spectrum _ U hU 0 0 (fun j => Or.inl (by simp))
  · unfold Holds
    refine convexHull_mono ?_ (diamond (R := t*(1+t)^3) (by positivity) _ (bound t ht U hU))
    rintro y ⟨j, rfl⟩
    exact vertex_mem t j

/-- Apply a common complex scale, then translate the two spectra by
opposite amounts. The relative unitary remains arbitrary. -/
theorem holds_affine_dilation (s c : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    Holds (fun i => s * spectrum i + c)
      (fun i => s * ((t : ℂ) * spectrum i) - c) U := by
  apply (holds_shift_iff _ _ hU c).mpr
  exact hull_of_common_factor (determinantValue_scale spectrum _ U s)
    (matchingProduct_scale spectrum _ s) (holds_dilation t ht U hU)

end FiveCross

end MOC
