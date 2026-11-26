import MOC.FiniteMinorLaw
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open BigOperators Finset Matrix

namespace MOC

/-- A two-position gate has equal transition probabilities in every entry. -/
def BalancedGate (Q : Matrix Bool Bool ℂ) : Prop :=
  IsUnitary Q ∧ ∀ i j, Complex.normSq (Q i j) = 1 / 2

theorem gate_column_flip (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q) (r c : Bool) :
    Q r (!c) * star (Q (!r) (!c)) = -(Q r c * star (Q (!r) c)) := by
  have h := congrFun (congrFun hQ.1 r) (!r)
  cases r <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool] at h ⊢ <;>
    first | exact eq_neg_of_add_eq_zero_left h | exact eq_neg_of_add_eq_zero_right h

theorem gate_row_flip (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q) (r c : Bool) :
    Q (!r) c * star (Q (!r) (!c)) = -(Q r c * star (Q r (!c))) := by
  have h := congrFun (congrFun hQ.2 (!c)) c
  cases r <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool] at h ⊢ <;>
    apply eq_neg_of_add_eq_zero_left <;>
    convert h using 1 <;> ring

theorem gate_row_mixed_sign (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q) (r : Bool) :
    Q r false * star (Q r true) =
      (if r then (-1 : ℂ) else 1) * (Q false false * star (Q false true)) := by
  cases r
  · simp
  · simpa only [Bool.not_false, Bool.true_eq, if_true, neg_one_mul] using
      gate_row_flip Q hQ false false

theorem gate_column_mixed_sign (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q) (c : Bool) :
    Q false c * star (Q true c) =
      (if c then (-1 : ℂ) else 1) * (Q false false * star (Q true false)) := by
  cases c
  · simp
  · simpa only [Bool.not_false, Bool.true_eq, if_true, neg_one_mul] using
      gate_column_flip Q hQ false false

theorem balancedGate_entry_norm (Q : Matrix Bool Bool ℂ) (hQ : BalancedGate Q) (r c : Bool) :
    ‖Q r c‖ = Real.sqrt (1 / 2) := by
  calc
    ‖Q r c‖ = Real.sqrt (Complex.normSq (Q r c)) := by
      rw [← Complex.sq_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = _ := by rw [hQ.2]

theorem balancedGate_mixed_norm (Q : Matrix Bool Bool ℂ) (hQ : BalancedGate Q) (r c i j : Bool) :
    ‖Q r c * star (Q i j)‖ = 1 / 2 := by
  rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj, balancedGate_entry_norm Q hQ, balancedGate_entry_norm Q hQ,
    ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem balancedGate_product_norm {κ : Type*} [Fintype κ] (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, BalancedGate (Q k)) (r c i j : κ → Bool) :
    ‖∏ k, Q k (r k) (c k) * star (Q k (i k) (j k))‖ = (1 / 2 : ℝ) ^ Fintype.card κ := by
  rw [Complex.norm_prod]
  simp_rw [fun k => balancedGate_mixed_norm (Q k) (hQ k) (r k) (c k) (i k) (j k)]
  rw [Finset.prod_const, Finset.card_univ]

theorem balancedGate_interference_bound {κ : Type*} [Fintype κ]
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k, BalancedGate (L k))
    (hR : ∀ k, BalancedGate (R k)) :
    |(∏ k, (L k false false * star (L k false true)) *
      (R k false false * star (R k true false))).re| ≤
      (1 / 2 : ℝ) ^ (Fintype.card κ + Fintype.card κ) := by
  apply le_trans (Complex.abs_re_le_norm _)
  rw [Finset.prod_mul_distrib, Complex.norm_mul,
    balancedGate_product_norm L hL (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => true),
    balancedGate_product_norm R hR (fun _ => false) (fun _ => false) (fun _ => true) (fun _ => false),
    ← pow_add]

theorem unitary_gate_det_normSq (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q) :
    Complex.normSq Q.det = 1 := by
  have h := congrArg Matrix.det hQ.1
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  rw [← Complex.ofReal_inj, Complex.ofReal_one, ← Complex.mul_conj]
  exact h

/-- The two deterministic switches of a two-position gate. -/
def gateSwitch (x : Bool) : Equiv.Perm Bool :=
  if x then Equiv.swap false true else Equiv.refl Bool

/-- The squared moduli in each row of a unitary gate sum to one. -/
theorem gate_row_probability (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q) (i : Bool) :
    Complex.normSq (Q i false) + Complex.normSq (Q i true) = 1 := by
  have h := congrFun (congrFun hQ.1 i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool,
    Matrix.one_apply_eq, Complex.star_def, Complex.mul_conj] at h
  exact Complex.ofReal_injective (by push_cast; simpa only [add_comm] using h)

theorem gate_column_probability (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q)
    (j : Bool) : Complex.normSq (Q false j) + Complex.normSq (Q true j) = 1 := by
  have h := congrFun (congrFun hQ.2 j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool,
    Matrix.one_apply_eq, Complex.star_def] at h
  rw [mul_comm (starRingEnd ℂ (Q false j)), mul_comm (starRingEnd ℂ (Q true j)),
    Complex.mul_conj, Complex.mul_conj] at h
  exact Complex.ofReal_injective (by push_cast; simpa only [add_comm] using h)

/-- The probabilities of the two possible permutations of a gate. -/
def gateSwitchProbability (Q : Matrix Bool Bool ℂ) (x : Bool) : ℝ :=
  Complex.normSq (Q false x)

theorem gateSwitchProbability_sum (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q) :
    ∑ x, gateSwitchProbability Q x = 1 := by
  rw [Fintype.sum_bool]
  simpa only [gateSwitchProbability, add_comm] using gate_row_probability Q hQ false

theorem gateSwitchProbability_eq_normSq (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q)
    (i j : Bool) : Complex.normSq (Q i j) = gateSwitchProbability Q (i ^^ j) := by
  have hr₁ := gate_row_probability Q hQ false
  have hr₂ := gate_row_probability Q hQ true
  have hc := gate_column_probability Q hQ false
  cases i <;> cases j <;> simp [gateSwitchProbability] <;> linarith

private theorem gate_minor_law (Q : Matrix Bool Bool ℂ) (hQ : IsUnitary Q)
    (I J : Finset Bool) :
    subsetMinorSq Q I J =
      ∑ x ∈ univ.filter (fun x => J.map (gateSwitch x).toEmbedding = I),
        gateSwitchProbability Q x := by
  apply indexed_minor_law_of_small Q hQ gateSwitch (gateSwitchProbability Q) _ I J
  intro S T he hS
  have hle : S.card ≤ 1 := by simpa using hS
  by_cases hzero : S.card = 0
  · obtain rfl := Finset.card_eq_zero.mp hzero
    obtain rfl := Finset.card_eq_zero.mp (he.symm.trans hzero)
    apply Complex.ofReal_injective
    rw [← sum_signedWeight_image_eq_subsetMinorSq Q hQ]
    simpa [sum_signedWeight Q (det_ne_zero_of_unitary hQ)] using
      congrArg Complex.ofReal (gateSwitchProbability_sum Q hQ).symm
  · have hone : S.card = 1 := by omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (he.symm.trans hone)
    rw [subsetMinorSq_singleton Q hQ, gateSwitchProbability_eq_normSq Q hQ,
      Finset.sum_filter, Fintype.sum_bool]
    cases i <;> cases j <;> simp [gateSwitch]

theorem balancedGate_minor_law (Q : Matrix Bool Bool ℂ) (hQ : BalancedGate Q)
    (I J : Finset Bool) :
    subsetMinorSq Q I J =
      ∑ _x ∈ univ.filter (fun x => J.map (gateSwitch x).toEmbedding = I), (1 / 2 : ℝ) := by
  simpa only [gateSwitchProbability, hQ.2] using gate_minor_law Q hQ.1 I J

section Layer

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Apply the chosen switch independently within every block. -/
def balancedLayerSwitch (x : κ → Bool) : Equiv.Perm (Bool × κ) where
  toFun p := (gateSwitch (x p.2) p.1, p.2)
  invFun p := ((gateSwitch (x p.2)).symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem gateLayer_unitary (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, IsUnitary (Q k)) : IsUnitary (Matrix.blockDiagonal Q) := by
  have h₁ : (fun k => Q k * (Q k)ᴴ) = 1 := funext fun k => (hQ k).1
  have h₂ : (fun k => (Q k)ᴴ * Q k) = 1 := funext fun k => (hQ k).2
  constructor <;>
    simp only [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, h₁, h₂,
      Matrix.blockDiagonal_one]

theorem gateLayer_determinant_law (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, IsUnitary (Q k)) (a b : Bool × κ → ℂ) :
    (∑ x : κ → Bool, ((∏ k, gateSwitchProbability (Q k) (x k) : ℝ) : ℂ) *
      matchingProduct a b (balancedLayerSwitch x)) =
        determinantValue a b (Matrix.blockDiagonal Q) := by
  let a₀ (k : κ) (i : Bool) := a (i, k)
  let b₀ (k : κ) (i : Bool) := b (i, k)
  have hdet : determinantValue a b (Matrix.blockDiagonal Q) =
      ∏ k, determinantValue (a₀ k) (b₀ k) (Q k) := by
    unfold determinantValue
    rw [← Matrix.blockDiagonal_diagonal a₀, ← Matrix.blockDiagonal_diagonal b₀,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul,
      ← Matrix.blockDiagonal_add, Matrix.det_blockDiagonal]
    rfl
  have hlocal (k : κ) : determinantValue (a₀ k) (b₀ k) (Q k) =
      ∑ x : Bool, (gateSwitchProbability (Q k) x : ℂ) * matchingProduct (a₀ k) (b₀ k) (gateSwitch x) := by
    exact (determinantValue_eq_sum_of_indexed_minor_law (a₀ k) (b₀ k) (Q k) (hQ k)
        gateSwitch (gateSwitchProbability (Q k)) (gate_minor_law (Q k) (hQ k))).symm
  rw [hdet]
  simp_rw [hlocal]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
  congr 1
  rw [matchingProduct, Fintype.prod_prod_type_right]
  rfl

theorem gateLayer_minor_law (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, IsUnitary (Q k)) (I J : Finset (Bool × κ)) :
    subsetMinorSq (Matrix.blockDiagonal Q) I J =
      ∑ x ∈ univ.filter (fun x : κ → Bool =>
        J.map (balancedLayerSwitch x).toEmbedding = I), ∏ k, gateSwitchProbability (Q k) (x k) := by
  classical
  by_cases hc : I.card = J.card
  · apply Complex.ofReal_injective
    rw [← sum_signedWeight_image_eq_subsetMinorSq _ (gateLayer_unitary Q hQ),
      Complex.ofReal_sum]
    have hm (σ : Equiv.Perm (Bool × κ)) :=
      matchingProduct_subset_marker I J hc σ
    have hv := (signed_determinant (fun i => if i ∈ I then 0 else 1)
      (fun j => if j ∈ J then 1 else 0) (Matrix.blockDiagonal Q) (gateLayer_unitary Q hQ))
    rw [← gateLayer_determinant_law Q hQ] at hv
    simp_rw [hm] at hv
    rw [Finset.sum_filter, Finset.sum_filter]
    simpa only [mul_ite, mul_one, mul_zero, Complex.ofReal_zero, apply_ite] using hv
  · have hn (x : κ → Bool) : J.map (balancedLayerSwitch x).toEmbedding ≠ I := by
      intro he
      exact hc (by rw [← he, Finset.card_map])
    simp [subsetMinorSq, hc, hn]

theorem balancedLayer_unitary (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, BalancedGate (Q k)) : IsUnitary (Matrix.blockDiagonal Q) :=
  gateLayer_unitary Q (fun k => (hQ k).1)

theorem balancedLayer_determinant_law (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, BalancedGate (Q k)) (a b : Bool × κ → ℂ) :
    (∑ x : κ → Bool, ((1 / 2 : ℂ) ^ Fintype.card κ) *
      matchingProduct a b (balancedLayerSwitch x)) =
        determinantValue a b (Matrix.blockDiagonal Q) := by
  simpa only [gateSwitchProbability, fun k => (hQ k).2, Finset.prod_const, Finset.card_univ,
    Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    gateLayer_determinant_law Q (fun k => (hQ k).1) a b

theorem balancedLayer_minor_law (Q : κ → Matrix Bool Bool ℂ)
    (hQ : ∀ k, BalancedGate (Q k)) (I J : Finset (Bool × κ)) :
    subsetMinorSq (Matrix.blockDiagonal Q) I J =
      ∑ _x ∈ univ.filter (fun x : κ → Bool =>
        J.map (balancedLayerSwitch x).toEmbedding = I), (1 / 2 : ℝ) ^ Fintype.card κ := by
  simpa only [gateSwitchProbability, fun k => (hQ k).2, Finset.prod_const, Finset.card_univ] using
    gateLayer_minor_law Q (fun k => (hQ k).1) I J

end Layer

end MOC
