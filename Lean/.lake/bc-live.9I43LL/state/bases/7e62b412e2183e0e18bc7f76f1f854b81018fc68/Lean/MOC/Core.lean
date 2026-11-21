import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The spectral formulation of the Marcus–de Oliveira conjecture.
A permutation sends a column label of the second spectrum to a row label of the first.
Taking inverse permutations recovers the usual ordering of the products. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matchingProduct (a b : ι → ℂ) (σ : Equiv.Perm ι) : ℂ :=
  ∏ j, (a (σ j) + b j)

def determinantValue (a b : ι → ℂ) (U : Matrix ι ι ℂ) : ℂ :=
  (diagonal a + U * diagonal b * Uᴴ).det

def IsUnitary (U : Matrix ι ι ℂ) : Prop :=
  U * Uᴴ = 1 ∧ Uᴴ * U = 1

def Holds (a b : ι → ℂ) (U : Matrix ι ι ℂ) : Prop :=
  determinantValue a b U ∈ convexHull ℝ (Set.range (matchingProduct a b))

def Conjecture (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U → Holds a b U

omit [DecidableEq ι] in
theorem matchingProduct_inverse (a b : ι → ℂ) (σ : Equiv.Perm ι) :
    matchingProduct a b σ.symm = ∏ i, (a i + b (σ i)) := by
  unfold matchingProduct
  rw [← Equiv.prod_comp σ (fun j => a (σ.symm j) + b j)]
  simp

omit [DecidableEq ι] in
theorem matchingProduct_mem_hull (a b : ι → ℂ) (σ : Equiv.Perm ι) :
    matchingProduct a b σ ∈ convexHull ℝ (Set.range (matchingProduct a b)) :=
  subset_convexHull ℝ _ ⟨σ, rfl⟩

theorem holds_of_weights {a b : ι → ℂ} {U : Matrix ι ι ℂ}
    (w : Equiv.Perm ι → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hs : ∑ σ, w σ = 1)
    (hv : ∑ σ, (w σ : ℂ) * matchingProduct a b σ = determinantValue a b U) :
    Holds a b U := by
  unfold Holds
  refine mem_convexHull_of_exists_fintype w (matchingProduct a b) hw hs (fun σ => ⟨σ, rfl⟩) ?_
  simpa [Complex.real_smul] using hv

theorem det_ne_zero_of_unitary {U : Matrix ι ι ℂ} (h : IsUnitary U) : U.det ≠ 0 := by
  have hd : U.det * Uᴴ.det = 1 := by rw [← Matrix.det_mul, h.1, Matrix.det_one]
  intro hz
  simp [hz] at hd

theorem det_unitary_conjugation (U M : Matrix ι ι ℂ) (h : IsUnitary U) :
    (U * M * Uᴴ).det = M.det := by
  have hd : U.det * Uᴴ.det = 1 := by rw [← Matrix.det_mul, h.1, Matrix.det_one]
  simp only [Matrix.det_mul]
  rw [mul_right_comm, hd, one_mul]

/-- The determinant expression in the two independently chosen eigenbases. -/
theorem determinantValue_relative (a b : ι → ℂ) (V W : Matrix ι ι ℂ) (hV : IsUnitary V) :
    (V * diagonal a * Vᴴ + W * diagonal b * Wᴴ).det = determinantValue a b (Vᴴ * W) := by
  have hV' : IsUnitary Vᴴ := ⟨by simpa using hV.2, by simpa using hV.1⟩
  have ha : Vᴴ * (V * diagonal a * Vᴴ) * V = diagonal a := by
    calc
      _ = (Vᴴ * V) * diagonal a * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by simp [hV.2]
  rw [← det_unitary_conjugation Vᴴ (V * diagonal a * Vᴴ + W * diagonal b * Wᴴ) hV']
  rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul, ha]
  simp only [determinantValue, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem relative_unitary (V W : Matrix ι ι ℂ) (hV : IsUnitary V) (hW : IsUnitary W) :
    IsUnitary (Vᴴ * W) := by
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Vᴴ * (W * Wᴴ) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hW.1, Matrix.mul_one, hV.2]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Wᴴ * (V * Vᴴ) * W := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV.1, Matrix.mul_one, hW.2]

theorem holds_of_diagonal_conjugation (a b : ι → ℂ) (U : Matrix ι ι ℂ) (σ : Equiv.Perm ι)
    (h : U * diagonal b * Uᴴ = diagonal (fun i => b (σ.symm i))) : Holds a b U := by
  unfold Holds determinantValue
  rw [h, Matrix.diagonal_add, Matrix.det_diagonal, ← matchingProduct_inverse]
  simpa using matchingProduct_mem_hull a b σ

theorem holds_identity (a b : ι → ℂ) : Holds a b (1 : Matrix ι ι ℂ) := by
  apply holds_of_diagonal_conjugation a b 1 (Equiv.refl ι)
  simp

theorem holds_of_commute (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hc : Commute U (diagonal b)) : Holds a b U := by
  apply holds_of_diagonal_conjugation a b U (Equiv.refl ι)
  rw [hc.eq, Matrix.mul_assoc, hU.1, Matrix.mul_one]
  rfl

omit [DecidableEq ι] in
theorem matchingProduct_shift (a b : ι → ℂ) (t : ℂ) (σ : Equiv.Perm ι) :
    matchingProduct (fun i => a i + t) (fun i => b i - t) σ = matchingProduct a b σ := by
  unfold matchingProduct
  apply Finset.prod_congr rfl
  intro j _
  ring

theorem determinantValue_shift (a b : ι → ℂ) {U : Matrix ι ι ℂ} (h : IsUnitary U) (t : ℂ) :
    determinantValue (fun i => a i + t) (fun i => b i - t) U = determinantValue a b U := by
  have ht : diagonal (fun _ : ι => t) = t • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hmul : U * diagonal (fun _ : ι => t) * Uᴴ = diagonal (fun _ : ι => t) := by
    rw [ht, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h.1]
  unfold determinantValue
  rw [← Matrix.diagonal_add a (fun _ => t), ← Matrix.diagonal_sub b (fun _ => t),
    Matrix.mul_sub, Matrix.sub_mul, hmul]
  congr 1
  abel

theorem holds_shift_iff (a b : ι → ℂ) {U : Matrix ι ι ℂ} (h : IsUnitary U) (t : ℂ) :
    Holds (fun i => a i + t) (fun i => b i - t) U ↔ Holds a b U := by
  unfold Holds
  rw [determinantValue_shift a b h]
  have hprod : matchingProduct (fun i => a i + t) (fun i => b i - t) = matchingProduct a b :=
    funext (matchingProduct_shift a b t)
  rw [hprod]

/-- Case D. The equal-trace hypothesis can be imposed by opposite shifts. -/
theorem conjecture_iff_equal_trace [Nonempty ι] :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      (∑ i, a i) = (∑ i, b i) → Holds a b U := by
  constructor
  · intro h a b U hu _
    exact h a b U hu
  · intro h a b U hu
    have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    let t : ℂ := ((∑ i, b i) - ∑ i, a i) / (2 * Fintype.card ι)
    apply (holds_shift_iff a b hu t).mp
    apply h _ _ U hu
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, nsmul_eq_mul, t]
    field_simp
    ring

end

end MOC
