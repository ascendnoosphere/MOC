import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! An order-four signed subset-action table that is nonnegative in every
degree and violates the determinant support bound on a rank-two kernel. -/

namespace MOC

open Matrix
open scoped ComplexOrder

/-- The signed permutation probabilities multiplied by six. Each list gives
the images of the four labels in order, starting at zero. -/
def exteriorRelaxationCoefficient (σ : Equiv.Perm (Fin 4)) : ℤ :=
  let p := [σ 0, σ 1, σ 2, σ 3]
  if p ∈ [[0, 1, 3, 2], [0, 2, 1, 3], [1, 0, 2, 3], [1, 3, 0, 2],
          [2, 0, 3, 1], [2, 3, 1, 0], [3, 2, 0, 1]] then 1
  else if p = [3, 1, 2, 0] then -1 else 0

/-- The subset transition entries multiplied by six. -/
def exteriorRelaxationEntry (I J : Finset (Fin 4)) : ℤ :=
  ∑ σ : Equiv.Perm (Fin 4),
    if I.map σ.toEmbedding = J then exteriorRelaxationCoefficient σ else 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- All exterior blocks are nonnegative, each row and column has mass six,
and complementing both subsets preserves the entries. Entries between
different degrees vanish. The signed action has total mass six. -/
theorem exteriorRelaxationEntry_properties :
    (∑ σ : Equiv.Perm (Fin 4), exteriorRelaxationCoefficient σ) = 6 ∧
    (∀ I J, 0 ≤ exteriorRelaxationEntry I J) ∧
    (∀ I J : Finset (Fin 4), I.card ≠ J.card → exteriorRelaxationEntry I J = 0) ∧
    (∀ I : Finset (Fin 4), (∑ J : Finset (Fin 4), exteriorRelaxationEntry I J) = 6) ∧
    (∀ J : Finset (Fin 4), (∑ I : Finset (Fin 4), exteriorRelaxationEntry I J) = 6) ∧
    (∀ I J, exteriorRelaxationEntry Iᶜ Jᶜ = exteriorRelaxationEntry I J) := by
  decide +kernel

/-- The singleton and pair transition blocks in the stated subset order.
Their entries are scaled by six. -/
theorem exteriorRelaxation_small_blocks :
    let S : Fin 6 → Finset (Fin 4) := ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]
    (Matrix.of fun i j : Fin 4 => exteriorRelaxationEntry {i} {j}) =
      !![2, 2, 2, 0; 2, 0, 2, 2; 2, 2, 0, 2; 0, 2, 2, 2] ∧
    (Matrix.of fun i j : Fin 6 => exteriorRelaxationEntry (S i) (S j)) =
      !![2, 2, 0, 0, 0, 2; 2, 0, 2, 2, 0, 0; 0, 2, 0, 2, 2, 0;
         0, 2, 2, 0, 2, 0; 0, 0, 2, 2, 0, 2; 2, 0, 0, 0, 2, 2] := by
  intro S
  constructor <;> (ext i j; revert i j; decide +kernel)

/-- The rank-two kernel has Gaussian integer entries. -/
def exteriorRelaxationKernel : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![⟨-3, -1⟩, ⟨12, -11⟩, ⟨2, -3⟩, ⟨-7, -9⟩;
     ⟨3, -1⟩, ⟨18, -11⟩, ⟨8, -3⟩, ⟨-1, -9⟩;
     ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩;
     ⟨-12, 2⟩, ⟨3, -8⟩, ⟨-7, 0⟩, ⟨-16, -6⟩]

private def exteriorRelaxationProduct (σ : Equiv.Perm (Fin 4)) : GaussianInt :=
  ∏ i, exteriorRelaxationKernel i (σ i)

private theorem exteriorRelaxationProduct_arithmetic :
    (∀ σ, (exteriorRelaxationProduct σ).re ≤ 154) ∧
    (∃ σ, (exteriorRelaxationProduct σ).re = 154) ∧
    (∑ σ : Equiv.Perm (Fin 4),
      (exteriorRelaxationCoefficient σ : GaussianInt) * exteriorRelaxationProduct σ) =
      ⟨932, -3524⟩ := by
  decide +kernel

private theorem exteriorRelaxationKernel_factorization :
    exteriorRelaxationKernel =
      (!![1, 0; 1, 6; 0, ⟨-1, 1⟩; 1, ⟨-9, 3⟩] : Matrix (Fin 4) (Fin 2) GaussianInt) *
      (!![⟨-3, -1⟩, ⟨12, -11⟩, ⟨2, -3⟩, ⟨-7, -9⟩; 1, 1, 1, 1] :
        Matrix (Fin 2) (Fin 4) GaussianInt) := by
  ext i j
  revert i j
  decide +kernel

/-- The signed action exceeds the largest real matching value on a complex
kernel of rank at most two. The displayed signed sum is scaled by six. -/
theorem exteriorRelaxation_rank_two_violation :
    let C := exteriorRelaxationKernel.map GaussianInt.toComplex
    let P := fun σ : Equiv.Perm (Fin 4) => ∏ i, C i (σ i)
    C.rank ≤ 2 ∧ (∀ σ, (P σ).re ≤ 154) ∧ (∃ σ, (P σ).re = 154) ∧
      (∑ σ : Equiv.Perm (Fin 4), (exteriorRelaxationCoefficient σ : ℂ) * P σ) =
        932 - 3524 * Complex.I := by
  intro C P
  let f := GaussianInt.toComplex
  have hP (σ : Equiv.Perm (Fin 4)) : P σ = f (exteriorRelaxationProduct σ) := by
    simp only [P, C, f, exteriorRelaxationProduct, Matrix.map_apply, map_prod]
  have hreal (σ : Equiv.Perm (Fin 4)) : (P σ).re = (exteriorRelaxationProduct σ).re := by
    rw [hP]
    exact (GaussianInt.to_real_re _).symm
  obtain ⟨hle, ⟨σ, hσ⟩, hsum⟩ := exteriorRelaxationProduct_arithmetic
  refine ⟨?_, fun p => by rw [hreal]; exact_mod_cast hle p,
    ⟨σ, by rw [hreal]; exact_mod_cast hσ⟩, ?_⟩
  · dsimp only [C]
    rw [exteriorRelaxationKernel_factorization, Matrix.map_mul]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · simp only [hP, ← map_intCast f, ← map_mul, ← map_sum, hsum]
    apply Complex.ext <;>
      norm_num [f, GaussianInt.toComplex_re, GaussianInt.toComplex_im, Complex.mul_re, Complex.mul_im]

/-- The relaxation example fails the interference Gram constraint for
the first two rows. All subset entries in the two equations are divided
by six before they are used as probabilities. -/
theorem exteriorRelaxation_no_interference_gram :
    let p := fun i j : Fin 4 => (exteriorRelaxationEntry {i} {j} : ℂ) / 6
    ¬ ∃ G : Matrix (Fin 4) (Fin 4) ℂ, G.PosSemidef ∧
      G 3 3 = p 0 3 * p 1 3 ∧
      (exteriorRelaxationEntry {0, 1} {0, 3} : ℂ) / 6 =
        p 0 0 * p 1 3 + p 0 3 * p 1 0 - 2 * G 0 3 := by
  intro p
  rintro ⟨G, hG, hdiag, hminor⟩
  have h03 : exteriorRelaxationEntry {0} {3} = 0 := by decide +kernel
  have h13 : exteriorRelaxationEntry {1} {3} = 2 := by decide +kernel
  have h00 : exteriorRelaxationEntry {0} {0} = 2 := by decide +kernel
  have hpair : exteriorRelaxationEntry {0, 1} {0, 3} = 0 := by decide +kernel
  have hz : G 3 3 = 0 := by
    simpa only [p, h03, Int.cast_zero, zero_div, zero_mul] using hdiag
  have hcol := (hG.dotProduct_mulVec_zero_iff (Pi.single 3 1)).mp (by
    simpa only [← Pi.single_star, star_one, mulVec_single_one, single_dotProduct, one_mul] using hz)
  have hG03 : G 0 3 = 0 := by
    simpa only [mulVec_single_one, Pi.zero_apply] using congrFun hcol 0
  norm_num [p, h03, h13, h00, hpair, hG03] at hminor

end MOC
