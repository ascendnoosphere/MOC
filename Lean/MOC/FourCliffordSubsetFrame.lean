import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Signed permutation matrices for the Euclidean Clifford algebra of order four. -/

open Matrix BigOperators

namespace MOC.FourCliffordFrame

def xorMask (a b : Fin 16) : Fin 16 :=
  ⟨a.val ^^^ b.val, by have h := Nat.xor_lt_two_pow (n := 4) a.isLt b.isLt; exact h⟩

private def boolParity (b : Bool) : ZMod 2 := if b then 1 else 0

private def bitParity (a : Fin 16) (i : ℕ) : ZMod 2 := boolParity (a.val.testBit i)

private def crossingParity (a b : Fin 16) : ZMod 2 :=
  bitParity a 1 * bitParity b 0 + bitParity a 2 * (bitParity b 0 + bitParity b 1) +
    bitParity a 3 * (bitParity b 0 + bitParity b 1 + bitParity b 2)

private def paritySign (p : ZMod 2) : ℤ := if p = 0 then 1 else -1

def sign (a b : Fin 16) : ℤ := paritySign (crossingParity a b)

private theorem boolParity_xor (a b : Bool) : boolParity (Bool.xor a b) =
    boolParity a + boolParity b := by cases a <;> cases b <;> decide

private theorem bitParity_xor (a b : Fin 16) (i : ℕ) : bitParity (xorMask a b) i =
    bitParity a i + bitParity b i := by
  simp only [bitParity, xorMask, Nat.testBit_xor, boolParity_xor]

private theorem paritySign_add (a b : ZMod 2) : paritySign (a + b) =
    paritySign a * paritySign b := by fin_cases a <;> fin_cases b <;> decide

theorem sign_explicit (a b : Fin 16) : sign a b =
    if Bool.xor (a.val.testBit 1 && b.val.testBit 0)
      (Bool.xor (a.val.testBit 2 && Bool.xor (b.val.testBit 0) (b.val.testBit 1))
        (a.val.testBit 3 && Bool.xor (b.val.testBit 0)
          (Bool.xor (b.val.testBit 1) (b.val.testBit 2)))) then -1 else 1 := by
  unfold sign paritySign crossingParity bitParity
  generalize a.val.testBit 1 = x₁, a.val.testBit 2 = x₂, a.val.testBit 3 = x₃
  generalize b.val.testBit 0 = y₀, b.val.testBit 1 = y₁, b.val.testBit 2 = y₂
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y₀ <;> cases y₁ <;> cases y₂ <;> decide

private def singletonMask (i : Fin 4) : Fin 16 := ⟨2 ^ i.val, by decide +revert⟩

/-- Left multiplication by the increasing product for a subset mask. -/
noncomputable def blade (a : Fin 16) : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => if i = xorMask a j then (sign a j : ℝ) else 0

private theorem xorMask_assoc (a b c : Fin 16) :
    xorMask a (xorMask b c) = xorMask (xorMask a b) c := by
  apply Fin.ext
  exact (Nat.xor_assoc _ _ _).symm

private theorem sign_cocycle (a b c : Fin 16) :
    sign a (xorMask b c) * sign b c = sign a b * sign (xorMask a b) c := by
  simp only [sign, ← paritySign_add]
  congr 1
  simp only [crossingParity, bitParity_xor]
  ring

private theorem xorMask_zero (i : Fin 16) : xorMask 0 i = i := Fin.ext (Nat.zero_xor _)

private theorem xorMask_self (i : Fin 16) : xorMask i i = 0 := Fin.ext (Nat.xor_self _)

private theorem sign_zero : ∀ i : Fin 16, sign 0 i = 1 := by decide +kernel

private theorem sign_sq (a b : Fin 16) : sign a b ^ 2 = 1 := by
  unfold sign paritySign
  split <;> decide

@[simp] theorem blade_zero : blade 0 = 1 := by
  ext i j
  simp only [blade, Matrix.of_apply, xorMask_zero, sign_zero, Int.cast_one, Matrix.one_apply]

/-- Multiplication of subset blades follows symmetric difference. -/
theorem blade_mul (a b : Fin 16) : blade a * blade b = (sign a b : ℝ) • blade (xorMask a b) := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (xorMask b j)]
  · simp only [blade, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, if_pos rfl,
      xorMask_assoc]
    split_ifs
    · exact_mod_cast sign_cocycle a b j
    · simp only [zero_mul, mul_zero]
  · intro c _ h
    simp only [blade, Matrix.of_apply, if_neg h, mul_zero]
  · simp

private theorem xorMask_involutive (i j : Fin 16) : xorMask i (xorMask i j) = j := by
  rw [xorMask_assoc, xorMask_self, xorMask_zero]

/-- Reversal of a subset blade is the matrix transpose. -/
theorem blade_transpose (a : Fin 16) : (blade a)ᵀ = (sign a a : ℝ) • blade a := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, blade, Matrix.of_apply]
  have he : j = xorMask a i ↔ i = xorMask a j := by
    constructor <;> intro h <;> rw [h, xorMask_involutive]
  by_cases hi : i = xorMask a j
  · rw [if_pos (he.mpr hi), if_pos hi, hi]
    have h := sign_cocycle a a j
    rw [xorMask_self, sign_zero, mul_one] at h
    have hh := congrArg (fun u => u * sign a j) h
    dsimp only at hh
    rw [mul_assoc, ← pow_two, sign_sq, mul_one] at hh
    exact_mod_cast hh
  · rw [if_neg (mt he.mp hi), if_neg hi, mul_zero]

private theorem singleton_data : ∀ i j : Fin 4,
    (i = j → sign (singletonMask i) (singletonMask j) = 1) ∧
    (i ≠ j → sign (singletonMask i) (singletonMask j) =
      - sign (singletonMask j) (singletonMask i)) := by
  decide +kernel

/-- The four generating Clifford matrices square to the identity or anticommute. -/
theorem blade_generator_anticommutator (i j : Fin 4) :
    blade (singletonMask i) * blade (singletonMask j) +
      blade (singletonMask j) * blade (singletonMask i) =
        if i = j then (2 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) else 0 := by
  have hx (a b : Fin 16) : xorMask a b = xorMask b a := Fin.ext (Nat.xor_comm _ _)
  have hz (a : Fin 16) : xorMask a a = 0 := Fin.ext (Nat.xor_self _)
  by_cases h : i = j
  · subst j
    simp only [if_true, blade_mul, (singleton_data i i).1 rfl, Int.cast_one,
      one_smul, hz, blade_zero, two_smul]
  · rw [if_neg h, blade_mul, blade_mul, hx (singletonMask j) (singletonMask i),
      (singleton_data i j).2 h, Int.cast_neg, neg_smul, neg_add_cancel]

/-- The Clifford matrix of one column of a real matrix. -/
noncomputable def generator (O : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    Matrix (Fin 16) (Fin 16) ℝ :=
  ∑ i, O i j • blade (singletonMask i)

@[simp] theorem generator_transpose (O : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    (generator O j)ᵀ = generator O j := by
  simp only [generator, Matrix.transpose_sum, Matrix.transpose_smul,
    blade_transpose, (singleton_data _ _).1 rfl, Int.cast_one, one_smul]

/-- Orthogonality of columns is the generator relation for the second frame. -/
theorem generator_anticommutator (O : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    generator O i * generator O j + generator O j * generator O i =
      (2 * (Oᵀ * O) i j) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  let X (a : Fin 4) := O a i • blade (singletonMask a)
  let Y (a : Fin 4) := O a j • blade (singletonMask a)
  have hf (a b : Fin 4) : X a * Y b + Y b * X a =
      if a = b then (2 * (O a i * O b j)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) else 0 := by
    simp only [X, Y, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_comm (O b j) (O a i), ← smul_add, blade_generator_anticommutator]
    split
    · rw [smul_smul, mul_comm (O a i * O b j) (2 : ℝ)]
    · rw [smul_zero]
  change (∑ a, X a) * (∑ b, Y b) + (∑ b, Y b) * (∑ a, X a) = _
  rw [Matrix.sum_mul, Matrix.mul_sum Finset.univ X (∑ b, Y b)]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, hf]
  rw [Matrix.mul_apply, Finset.mul_sum]
  simp only [Matrix.transpose_apply]
  ext r s
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hab
    simp [hab.symm]
  · simp

/-- Distinct frame generators anticommute when the columns are orthonormal. -/
theorem generator_mul_swap (O : Matrix (Fin 4) (Fin 4) ℝ) (hO : Oᵀ * O = 1)
    (i j : Fin 4) (hij : i ≠ j) : generator O i * generator O j =
      -(generator O j * generator O i) := by
  have h := generator_anticommutator O i j
  rw [hO, Matrix.one_apply_ne hij, mul_zero, zero_smul] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Each frame generator is an involution when the columns are orthonormal. -/
theorem generator_sq (O : Matrix (Fin 4) (Fin 4) ℝ) (hO : Oᵀ * O = 1)
    (i : Fin 4) : generator O i * generator O i = 1 := by
  have h := generator_anticommutator O i i
  rw [hO, Matrix.one_apply_eq, mul_one, two_smul] at h
  ext a b
  have hentry := congrArg (fun (A : Matrix (Fin 16) (Fin 16) ℝ) => A a b) h
  simp only [Matrix.add_apply] at hentry
  linarith only [hentry]

private theorem trace_blade (a : Fin 16) : (blade a).trace = if a = 0 then 16 else 0 := by
  by_cases h : a = 0
  · rw [h, blade_zero, if_pos rfl]
    norm_num [Matrix.trace_one]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    change (if i = xorMask a i then (sign a i : ℝ) else 0) = 0
    rw [if_neg]
    intro hi
    apply h
    have he := congrArg (fun u => xorMask u i) hi
    have hr : xorMask a 0 = a := Fin.ext (Nat.xor_zero _)
    dsimp only at he
    rw [xorMask_self, ← xorMask_assoc, xorMask_self, hr] at he
    exact he.symm

/-- The sixteen subset blades are orthogonal for the matrix trace inner product. -/
theorem trace_transpose_blade_mul (a b : Fin 16) :
    ((blade a)ᵀ * blade b).trace = if a = b then 16 else 0 := by
  rw [blade_transpose, Matrix.smul_mul, blade_mul, Matrix.trace_smul, Matrix.trace_smul]
  by_cases h : a = b
  · subst b
    rw [if_pos rfl, xorMask_self, trace_blade, if_pos rfl, smul_eq_mul, smul_eq_mul]
    have hs : (sign a a : ℝ) ^ 2 = 1 := by exact_mod_cast sign_sq a a
    calc
      _ = (sign a a : ℝ) ^ 2 * 16 := by ring
      _ = 16 := by rw [hs, one_mul]
  · rw [if_neg h, trace_blade, if_neg]
    · simp
    · intro he
      have hs := congrArg (fun u => xorMask a u) he
      have hr : xorMask a 0 = a := Fin.ext (Nat.xor_zero _)
      dsimp only at hs
      rw [xorMask_involutive, hr] at hs
      exact h hs.symm

/-- The coordinate of a Clifford matrix along a standard subset blade. -/
noncomputable def bladeCoefficient (a : Fin 16) (A : Matrix (Fin 16) (Fin 16) ℝ) : ℝ :=
  ((blade a)ᵀ * A).trace / 16

@[simp] theorem bladeCoefficient_smul (a : Fin 16) (c : ℝ)
    (A : Matrix (Fin 16) (Fin 16) ℝ) : bladeCoefficient a (c • A) = c * bladeCoefficient a A := by
  simp only [bladeCoefficient, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

@[simp] theorem bladeCoefficient_sum {ι : Type*} (a : Fin 16) (s : Finset ι)
    (A : ι → Matrix (Fin 16) (Fin 16) ℝ) :
    bladeCoefficient a (∑ i ∈ s, A i) = ∑ i ∈ s, bladeCoefficient a (A i) := by
  simp only [bladeCoefficient, Matrix.mul_sum, Matrix.trace_sum, div_eq_mul_inv, Finset.sum_mul]

@[simp] theorem bladeCoefficient_blade (a b : Fin 16) :
    bladeCoefficient a (blade b) = if a = b then 1 else 0 := by
  simp only [bladeCoefficient, trace_transpose_blade_mul]
  split <;> norm_num

def smallMask (a : Fin 8) : Fin 16 := Fin.castLE (by decide) a

def xorSmall (a b : Fin 8) : Fin 8 :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 3) a.isLt b.isLt⟩

private def smallXorTable : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 0, 3, 2, 5, 4, 7, 6],
    ![2, 3, 0, 1, 6, 7, 4, 5],
    ![3, 2, 1, 0, 7, 6, 5, 4],
    ![4, 5, 6, 7, 0, 1, 2, 3],
    ![5, 4, 7, 6, 1, 0, 3, 2],
    ![6, 7, 4, 5, 2, 3, 0, 1],
    ![7, 6, 5, 4, 3, 2, 1, 0]]

private def smallReverseSign : Fin 8 → Fin 8 → ℤ :=
  ![![1, 1, 1, -1, 1, -1, -1, -1],
    ![1, 1, 1, -1, 1, -1, -1, -1],
    ![1, -1, 1, 1, 1, 1, -1, 1],
    ![1, -1, 1, 1, 1, 1, -1, 1],
    ![1, -1, -1, -1, 1, 1, 1, -1],
    ![1, -1, -1, -1, 1, 1, 1, -1],
    ![1, 1, -1, 1, 1, -1, 1, 1],
    ![1, 1, -1, 1, 1, -1, 1, 1]]

private theorem smallXorTable_eq : ∀ a b, xorSmall a b = smallXorTable a b := by decide +kernel

private theorem smallReverseSign_eq : ∀ a b,
    sign (smallMask a) (smallMask b) * sign (smallMask b) (smallMask b) =
      smallReverseSign a b := by decide +kernel

/-- The eight products formed from the first three generators of a frame. -/
noncomputable def smallFrame (O : Matrix (Fin 4) (Fin 4) ℝ) : Fin 8 → Matrix (Fin 16) (Fin 16) ℝ :=
  let g := generator O
  ![1, g 0, g 1, g 0 * g 1, g 2, g 0 * g 2, g 1 * g 2, g 0 * g 1 * g 2]

theorem smallFrame_one (a : Fin 8) : smallFrame 1 a = blade (smallMask a) := by
  have hg (i : Fin 4) : generator 1 i = blade (singletonMask i) := by
    rw [generator, Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro j _ hj
      rw [Matrix.one_apply_ne hj, zero_smul]
    · simp
  have hm (a b c : Fin 16) (h : sign a b = 1) (hc : xorMask a b = c) :
      blade a * blade b = blade c := by rw [blade_mul, h, hc, Int.cast_one, one_smul]
  have h01 := hm (singletonMask 0) (singletonMask 1) 3 (by decide) (by decide)
  have h02 := hm (singletonMask 0) (singletonMask 2) 5 (by decide) (by decide)
  have h12 := hm (singletonMask 1) (singletonMask 2) 6 (by decide) (by decide)
  have h012 := hm 3 (singletonMask 2) 7 (by decide) (by decide)
  fin_cases a <;> simp only [smallFrame, Matrix.cons_val, hg, h01, h02, h12, h012]
  · change 1 = blade 0
    rw [blade_zero]
  all_goals rfl

set_option maxHeartbeats 900000 in
/-- Products with one reversed small blade reduce by symmetric difference. -/
theorem smallFrame_mul_transpose (O : Matrix (Fin 4) (Fin 4) ℝ) (hO : Oᵀ * O = 1)
    (a b : Fin 8) : smallFrame O a * (smallFrame O b)ᵀ =
      ((sign (smallMask a) (smallMask b) * sign (smallMask b) (smallMask b) : ℤ) : ℝ) •
        smallFrame O (xorSmall a b) := by
  have h10 := generator_mul_swap O hO 1 0 (by decide)
  have h20 := generator_mul_swap O hO 2 0 (by decide)
  have h21 := generator_mul_swap O hO 2 1 (by decide)
  have hsq0 := generator_sq O hO 0
  have hsq1 := generator_sq O hO 1
  have hsq2 := generator_sq O hO 2
  have slide {A B : Matrix (Fin 16) (Fin 16) ℝ} (h : A * B = -(B * A))
      (X : Matrix (Fin 16) (Fin 16) ℝ) : X * A * B = -(X * B * A) := by
    rw [Matrix.mul_assoc, h, mul_neg, Matrix.mul_assoc]
  have cancel {A : Matrix (Fin 16) (Fin 16) ℝ} (h : A * A = 1)
      (X : Matrix (Fin 16) (Fin 16) ℝ) : X * A * A = X := by
    rw [Matrix.mul_assoc, h, mul_one]
  fin_cases a <;> fin_cases b <;>
    norm_num [smallFrame, smallXorTable_eq, smallReverseSign_eq, smallXorTable, smallReverseSign, Matrix.transpose_mul] <;>
    simp only [← Matrix.mul_assoc, h10, h20, h21, hsq0, hsq1, hsq2, slide h10, slide h20,
      slide h21, cancel hsq0, cancel hsq1, cancel hsq2, mul_one, one_mul, neg_mul, mul_neg,
      neg_neg, neg_smul, one_smul, Matrix.cons_val] <;> rfl

private theorem smallMask_xorSmall (a b : Fin 8) :
    smallMask (xorSmall a b) = xorMask (smallMask a) (smallMask b) := rfl

/-- The normalised trace inner product of two mixed-frame blades reduces to
one coefficient of a single frame blade. -/
theorem trace_mixed_smallFrame (O : Matrix (Fin 4) (Fin 4) ℝ) (hO : Oᵀ * O = 1)
    (a b c d : Fin 8) :
    ((((blade (smallMask a))ᵀ * smallFrame O b)ᵀ *
        ((blade (smallMask c))ᵀ * smallFrame O d)).trace / 16) =
      ((sign (smallMask a) (smallMask c) * sign (smallMask c) (smallMask c) *
        sign (smallMask d) (smallMask b) * sign (smallMask b) (smallMask b) *
        sign (smallMask (xorSmall a c)) (smallMask (xorSmall a c)) : ℤ) : ℝ) *
        bladeCoefficient (smallMask (xorSmall a c)) (smallFrame O (xorSmall d b)) := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hcycle : (((smallFrame O b)ᵀ * blade (smallMask a)) *
      ((blade (smallMask c))ᵀ * smallFrame O d)).trace =
      (((blade (smallMask a)) * (blade (smallMask c))ᵀ) *
        (smallFrame O d * (smallFrame O b)ᵀ)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm (smallFrame O b)ᵀ]
    simp only [Matrix.mul_assoc]
  rw [hcycle, ← smallFrame_one a, ← smallFrame_one c,
    smallFrame_mul_transpose 1 (by simp), smallFrame_mul_transpose O hO,
    smallFrame_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [bladeCoefficient, blade_transpose, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Int.cast_mul]
  have hs : (sign (smallMask (xorSmall a c)) (smallMask (xorSmall a c)) : ℝ) ^ 2 = 1 := by
    exact_mod_cast sign_sq (smallMask (xorSmall a c)) (smallMask (xorSmall a c))
  linear_combination -(sign (smallMask a) (smallMask c) : ℝ) *
    (sign (smallMask c) (smallMask c) : ℝ) * (sign (smallMask d) (smallMask b) : ℝ) *
    (sign (smallMask b) (smallMask b) : ℝ) *
    ((blade (smallMask (xorSmall a c)) * smallFrame O (xorSmall d b)).trace / 16) * hs

end MOC.FourCliffordFrame
