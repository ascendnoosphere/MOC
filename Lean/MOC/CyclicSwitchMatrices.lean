import MOC.BalancedGateProducts
import MOC.CyclicSwitchEvents
import MOC.FourMinorTransport
import MOC.Small
import MOC.WeightedPermutationCycle

/-! Block gate matrices and the two-term determinant for transversals. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The signed cross term at the two all-false transversals. -/
def cyclicGateInterference (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ) : ℝ :=
  ((s.sign : ℤ) : ℝ) *
    (∏ k, (L k false false * star (L k false true)) *
      (R k false false * star (R k true false))).re

theorem cyclicGateInterference_bound (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, BalancedGate (L k)) (hR : ∀ k, BalancedGate (R k)) :
    |cyclicGateInterference s L R| ≤ (1/2 : ℝ)^(Fintype.card κ + Fintype.card κ) := by
  rcases Int.units_eq_one_or s.sign with h | h <;>
    simpa [cyclicGateInterference, h] using balancedGate_interference_bound L R hL hR

private theorem gate_mixed_norm_le_half {a b : ℂ} (h : Complex.normSq a + Complex.normSq b = 1) :
    ‖a * star b‖ ≤ 1 / 2 := by
  rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj]
  rw [← Complex.sq_norm, ← Complex.sq_norm] at h
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem cyclic_interference_le_half_pow (s : Equiv.Perm κ)
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) :
    |cyclicGateInterference s L R| ≤ (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ) := by
  have hb (k : κ) :
      ‖(L k false false * star (L k false true)) * (R k false false * star (R k true false))‖
        ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) := by
    rw [Complex.norm_mul]
    exact mul_le_mul (gate_mixed_norm_le_half (gate_row_probability (L k) (hL k) false))
      (gate_mixed_norm_le_half (gate_column_probability (R k) (hR k) false)) (norm_nonneg _) (by norm_num)
  have hp : ‖∏ k, (L k false false * star (L k false true)) *
      (R k false false * star (R k true false))‖ ≤ (1 / 2 : ℝ) ^ Fintype.card (κ ⊕ κ) := by
    rw [Complex.norm_prod, Fintype.card_sum, pow_add, ← mul_pow, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hb k)
  rcases Int.units_eq_one_or s.sign with hs | hs <;>
    simpa [cyclicGateInterference, hs] using (Complex.abs_re_le_norm _).trans hp

def cyclicIndependentWeight (L R : κ → Matrix Bool Bool ℂ) (x : κ ⊕ κ → Bool) : ℝ :=
  (∏ k, gateSwitchProbability (L k) (x (Sum.inl k))) *
    (∏ k, gateSwitchProbability (R k) (x (Sum.inr k)))

omit [DecidableEq κ] in
theorem cyclicIndependentWeight_balanced (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, BalancedGate (L k)) (hR : ∀ k, BalancedGate (R k)) (x : κ ⊕ κ → Bool) :
    cyclicIndependentWeight L R x = (1 / 2 : ℝ) ^ (Fintype.card κ + Fintype.card κ) := by
  simp only [cyclicIndependentWeight, gateSwitchProbability, fun k => (hL k).2,
    fun k => (hR k).2, Finset.prod_const, Finset.card_univ, pow_add]

theorem cyclic_two_products_independent_normSq (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k)) (x y : κ → Bool) :
    Complex.normSq ((∏ l, L l (x l) false * R l false (y l)) +
      ((s.sign : ℤ) : ℂ) * ∏ l, L (s l) (x (s l)) true * R l true (y l)) =
      cyclicIndependentWeight L R (Sum.elim x y) +
      cyclicIndependentWeight L R (fun z => !(Sum.elim x y z)) +
      2 * switchParity x * switchParity y * cyclicGateInterference s L R := by
  let A := ∏ k, L k (x k) false * R k false (y k)
  let B := ∏ k, L k (x k) true * R k true (y k)
  let C := ∏ k, (L k false false * star (L k false true)) *
      (R k false false * star (R k true false))
  have hB : (∏ k, L (s k) (x (s k)) true * R k true (y k)) = B := by
    dsimp [B]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Equiv.prod_comp s (fun k => L k (x k) true)]
  have hab (b : Bool) : Complex.normSq (∏ k, L k (x k) b * R k b (y k)) =
      cyclicIndependentWeight L R (fun z => Sum.elim x y z ^^ b) := by
    rw [map_prod]
    simp_rw [Complex.normSq_mul, gateSwitchProbability_eq_normSq _ (hL _),
      gateSwitchProbability_eq_normSq _ (hR _)]
    rw [Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    change gateSwitchProbability (R k) (b ^^ y k) = gateSwitchProbability (R k) (y k ^^ b)
    rw [Bool.xor_comm]
  have ha : Complex.normSq A = cyclicIndependentWeight L R (Sum.elim x y) := by
    simpa only [Bool.xor_false] using hab false
  have hb : Complex.normSq B = cyclicIndependentWeight L R (fun z => !(Sum.elim x y z)) := by
    simpa only [Bool.xor_true] using hab true
  have hprod : A * star B = ((switchParity x * switchParity y : ℝ) : ℂ) * C := by
    dsimp only [A,B,C]
    rw [star_prod, ← Finset.prod_mul_distrib]
    simp only [switchParity, Complex.ofReal_mul, Complex.ofReal_prod]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    rw [StarMul.star_mul]
    calc
      _ = (L k (x k) false * star (L k (x k) true)) *
          (R k false (y k) * star (R k true (y k))) := by ring
      _ = _ := by
        rw [gate_row_mixed_sign _ (hL k), gate_column_mixed_sign _ (hR k)]
        cases x k <;> cases y k <;> simp [switchSign]
  have hr : (A * star B).re = switchParity x * switchParity y * C.re := by
    rw [hprod, Complex.re_ofReal_mul]
  rw [hB]
  change Complex.normSq (A + ((s.sign : ℤ) : ℂ) * B) = _
  rcases Int.units_eq_one_or s.sign with h | h
  · simp only [h, Units.val_one, Int.cast_one, one_mul, Complex.normSq_add]
    rw [ha, hb]
    change _ + _ + 2 * (A * star B).re = _
    rw [hr]
    simp [cyclicGateInterference, h, C]
    ring
  · simp only [h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul,
      Complex.normSq_add, Complex.normSq_neg, map_neg, mul_neg, Complex.neg_re]
    rw [ha, hb]
    change _ + _ + -(2 * (A * star B).re) = _
    rw [hr]
    simp [cyclicGateInterference, h, C]
    ring
theorem cyclic_two_products_normSq (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, BalancedGate (L k)) (hR : ∀ k, BalancedGate (R k)) (x y : κ → Bool) :
    Complex.normSq ((∏ l, L l (x l) false * R l false (y l)) +
      ((s.sign : ℤ) : ℂ) * ∏ l, L (s l) (x (s l)) true * R l true (y l)) =
      2*(1/2 : ℝ)^(Fintype.card κ + Fintype.card κ) +
      2 * switchParity x * switchParity y * cyclicGateInterference s L R := by
  simpa only [cyclicIndependentWeight_balanced L R hL hR, ← two_mul] using
    cyclic_two_products_independent_normSq s L R (fun k => (hL k).1) (fun k => (hR k).1) x y

end

end MOC

open BigOperators Matrix

namespace MOC

noncomputable section

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- A layer of independent two-coordinate gates, labeled by the block chart. -/
def blockGateMatrix (e : κ × Bool ≃ ι) (Q : κ → Matrix Bool Bool ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => if (e.symm i).1 = (e.symm j).1 then
    Q (e.symm i).1 (e.symm i).2 (e.symm j).2 else 0

theorem blockGateMatrix_unitary (e : κ × Bool ≃ ι) (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, IsUnitary (Q k)) : IsUnitary (blockGateMatrix e Q) := by
  let f := e.symm.trans (Equiv.prodComm κ Bool)
  have H : IsUnitary (Matrix.blockDiagonal Q) := by
    constructor
    · rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
        show (fun k => Q k * (Q k)ᴴ) = 1 from funext fun k => (hQ k).1,
        Matrix.blockDiagonal_one]
    · rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
        show (fun k => (Q k)ᴴ * Q k) = 1 from funext fun k => (hQ k).2,
        Matrix.blockDiagonal_one]
  have he : blockGateMatrix e Q = (Matrix.blockDiagonal Q).submatrix f f := by
    ext i j
    simp [blockGateMatrix, f, Matrix.blockDiagonal_apply]
  exact he ▸ unitary_reindex f f H

theorem blockGateMatrix_mul_unitary (e f : κ × Bool ≃ ι)
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k, IsUnitary (L k))
    (hR : ∀ k, IsUnitary (R k)) :
    IsUnitary (blockGateMatrix e L * blockGateMatrix f R) := by
  have hA := blockGateMatrix_unitary e L hL
  have hB := blockGateMatrix_unitary f R hR
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (blockGateMatrix f R),
      hB.1, Matrix.one_mul, hA.1]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (blockGateMatrix e L)ᴴ,
      hA.2, Matrix.one_mul, hB.2]

/-- The gate product along the two alternating matchings associated with a cycle. -/
def cyclicGateMixer (s : Equiv.Perm κ) (L R : κ → Matrix Bool Bool ℂ) :
    Matrix (κ × Bool) (κ × Bool) ℂ :=
  blockGateMatrix (Equiv.refl _) L * blockGateMatrix (cyclicRightChart s) R

omit [DecidableEq ι] in
/-- An entry of the product is the sum over the two coordinates of its output block. -/
theorem blockGateMatrix_mul_entry (e f : κ × Bool ≃ ι)
    (L R : κ → Matrix Bool Bool ℂ) (k l : κ) (i j : Bool) :
    (blockGateMatrix e L * blockGateMatrix f R) (e (k,i)) (f (l,j)) =
      ∑ b : Bool, if (f.symm (e (k,b))).1 = l then
        L k i b * R l (f.symm (e (k,b))).2 j else 0 := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · apply Finset.sum_congr rfl
    intro b _
    by_cases h : (f.symm (e (k,b))).1 = l <;> simp [blockGateMatrix, h]
  · intro t _ ht
    simp [blockGateMatrix, Ne.symm ht]
  · simp

/-- The transverse square matrix has one diagonal and one weighted cycle. -/
theorem cyclicSwitchMatrix_transverse_entry (s : Equiv.Perm κ)
    (L R : κ → Matrix Bool Bool ℂ) (x y : κ → Bool) (k l : κ) :
    (blockGateMatrix (Equiv.refl _) L * blockGateMatrix (cyclicRightChart s) R)
        (k,x k) (cyclicRightChart s (l,y l)) =
      (if k = l then L l (x l) false * R l false (y l) else 0) +
      (if k = s l then L (s l) (x (s l)) true * R l true (y l) else 0) := by
  rw [show (k,x k) = (Equiv.refl (κ × Bool)) (k,x k) from rfl,
    blockGateMatrix_mul_entry, Fintype.sum_bool]
  by_cases h0 : k = l <;> by_cases h1 : k = s l <;>
    simp_all [cyclicRightChart, Equiv.symm_apply_eq, add_comm]

/-- Take one label from each output and input pair. The determinant has two terms. -/
theorem cyclicSwitchMatrix_transverse_det (s : Equiv.Perm κ) (hc : TraversesAllIndices s)
    (hs : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ) (x y : κ → Bool) :
    ((blockGateMatrix (Equiv.refl _) L * blockGateMatrix (cyclicRightChart s) R).submatrix
      (fun k => (k,x k)) (fun l => cyclicRightChart s (l,y l))).det =
    (∏ l, L l (x l) false * R l false (y l)) +
    ((Equiv.Perm.sign s : ℤ) : ℂ) * ∏ l, L (s l) (x (s l)) true * R l true (y l) := by
  let d (l : κ) := L l (x l) false * R l false (y l)
  let w (l : κ) := L (s l) (x (s l)) true * R l true (y l)
  have he :
      (blockGateMatrix (Equiv.refl _) L * blockGateMatrix (cyclicRightChart s) R).submatrix
        (fun k => (k,x k)) (fun l => cyclicRightChart s (l,y l)) =
        diagonal d + weightedPermutationMatrix s w := by
    ext k l
    rw [Matrix.submatrix_apply, cyclicSwitchMatrix_transverse_entry, Matrix.add_apply,
      Matrix.diagonal_apply, weightedPermutationMatrix, Matrix.of_apply]
    by_cases h : k = l <;> simp [h, d, w]
  rw [he, det_diagonal_add_weightedPermutationMatrix d w hc hs]

/-- Squared modulus for transversals of balanced gates. -/
theorem cyclicSwitchMatrix_transverse_normSq (s : Equiv.Perm κ) (hc : TraversesAllIndices s)
    (hs : s ≠ 1) (L R : κ → Matrix Bool Bool ℂ)
    (hL : ∀ k, BalancedGate (L k)) (hR : ∀ k, BalancedGate (R k)) (x y : κ → Bool) :
    Complex.normSq (((blockGateMatrix (Equiv.refl _) L * blockGateMatrix (cyclicRightChart s) R).submatrix
      (fun k => (k,x k)) (fun l => cyclicRightChart s (l,y l))).det) =
      2*(1/2 : ℝ)^(Fintype.card κ + Fintype.card κ) +
      2 * switchParity x * switchParity y * cyclicGateInterference s L R := by
  rw [cyclicSwitchMatrix_transverse_det s hc hs]
  exact cyclic_two_products_normSq s L R hL hR x y

end

end MOC

open BigOperators Matrix Finset

namespace MOC

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- A block layer has the squared-minor law of independent switches. -/
theorem blockGateMatrix_independent_law (e : κ × Bool ≃ ι) (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, IsUnitary (Q k)) (I J : Finset ι) :
    subsetMinorSq (blockGateMatrix e Q) I J =
      ∑ x ∈ Finset.univ.filter (fun x : κ → Bool =>
        J.map (blockSwitch e x).toEmbedding = I), ∏ k, gateSwitchProbability (Q k) (x k) := by
  classical
  let f := e.symm.trans (Equiv.prodComm κ Bool)
  have he : blockGateMatrix e Q = (Matrix.blockDiagonal Q).submatrix f f := by
    ext i j
    simp [blockGateMatrix, f, Matrix.blockDiagonal_apply]
  have hmap (x : κ → Bool) :
      (J.map (blockSwitch e x).toEmbedding).map f.toEmbedding =
        (J.map f.toEmbedding).map (balancedLayerSwitch x).toEmbedding := by
    rw [Finset.map_map, Finset.map_map]
    congr 1
    ext i : 1
    obtain ⟨⟨k,b⟩, rfl⟩ := e.surjective i
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, blockSwitch_apply, f,
      Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodComm_apply]
    cases b <;> cases h : x k <;> simp [balancedLayerSwitch, gateSwitch, h]
  rw [he, squared_minor_reindex f f _ (gateLayer_unitary Q hQ),
    gateLayer_minor_law Q hQ]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hmap x, Finset.map_inj]

/-- A balanced block layer has the squared-minor law of independent fair switches. -/
theorem blockGateMatrix_minor_law (e : κ × Bool ≃ ι) (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, BalancedGate (Q k)) (I J : Finset ι) :
    subsetMinorSq (blockGateMatrix e Q) I J =
      ∑ _x ∈ Finset.univ.filter (fun x : κ → Bool =>
        J.map (blockSwitch e x).toEmbedding = I), (1 / 2 : ℝ) ^ Fintype.card κ := by
  simpa only [gateSwitchProbability, fun k => (hQ k).2, Finset.prod_const, Finset.card_univ] using
    blockGateMatrix_independent_law e Q (fun k => (hQ k).1) I J

end MOC
