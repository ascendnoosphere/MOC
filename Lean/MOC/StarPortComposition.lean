import MOC.SinglePortComposition

/-! Products of covered coordinate blocks with one common coordinate. -/

open Matrix BigOperators

namespace MOC

noncomputable section

/-- The coordinates outside the port, in the order of their blocks. -/
def StarPortPetals : List ℕ → Type
  | [] => Fin 0
  | n :: ns => Fin n ⊕ StarPortPetals ns

instance starPortPetalsFintype : (sizes : List ℕ) → Fintype (StarPortPetals sizes)
  | [] => inferInstanceAs (Fintype (Fin 0))
  | n :: ns =>
    letI := starPortPetalsFintype ns
    inferInstanceAs (Fintype (Fin n ⊕ StarPortPetals ns))

instance starPortPetalsDecidableEq : (sizes : List ℕ) → DecidableEq (StarPortPetals sizes)
  | [] => inferInstanceAs (DecidableEq (Fin 0))
  | n :: ns =>
    letI := starPortPetalsDecidableEq ns
    inferInstanceAs (DecidableEq (Fin n ⊕ StarPortPetals ns))

/-- A unitary gate on `n` private coordinates and the common port. -/
structure StarPortGate (n : ℕ) where
  matrix : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ
  unitary : IsUnitary matrix
  covered : ∀ a b, Holds a b matrix

/-- A rank-one phase on a gate block. The phase `-1` gives a Householder reflection. -/
def StarPortGate.ofRankOnePhase {n : ℕ} (v : Fin n ⊕ Unit → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1) : StarPortGate n where
  matrix := rankOnePhase v z
  unitary := rankOnePhase_unitary v z hv hz
  covered := fun a b => holds_rankOnePhase a b v z hv hz

/-- Every unitary gate of order at most three can be used in the product. -/
def StarPortGate.ofSmall {n : ℕ} (hn : n ≤ 2)
    (U : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ) (hU : IsUnitary U) : StarPortGate n where
  matrix := U
  unitary := hU
  covered := fun a b => conjecture_of_card_le_three (by simpa using Nat.succ_le_succ hn) a b U hU

/-- An ordered sequence of gates with the specified private block sizes. -/
inductive StarPortGates : List ℕ → Type
  | nil : StarPortGates []
  | cons {n : ℕ} {ns : List ℕ} : StarPortGate n → StarPortGates ns → StarPortGates (n :: ns)

private def starPortSplit (n : ℕ) (ns : List ℕ) :
    (Unit ⊕ StarPortPetals (n :: ns)) ≃ ((Fin n ⊕ Unit) ⊕ StarPortPetals ns) :=
  (Equiv.sumAssoc Unit (Fin n) (StarPortPetals ns)).symm.trans
    (Equiv.sumCongr (Equiv.sumComm Unit (Fin n)) (Equiv.refl (StarPortPetals ns)))

/-- Extend a matrix by the identity on the first private block. -/
private def starPortExtendTail (n : ℕ) (ns : List ℕ) :
    Matrix (Unit ⊕ StarPortPetals ns) (Unit ⊕ StarPortPetals ns) ℂ →*
      Matrix (Unit ⊕ StarPortPetals (n :: ns)) (Unit ⊕ StarPortPetals (n :: ns)) ℂ where
  toFun W := (singlePortRight W).submatrix (starPortSplit n ns) (starPortSplit n ns)
  map_one' := by
    simp only [singlePortRight, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  map_mul' V W := by
    simp only [singlePortRight, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- The factors in multiplication order, with each local matrix extended by
the identity outside its private block and the port. -/
def starPortFactorMatrices : {sizes : List ℕ} → StarPortGates sizes →
    List (Matrix (Unit ⊕ StarPortPetals sizes) (Unit ⊕ StarPortPetals sizes) ℂ)
  | [], .nil => []
  | n :: ns, .cons G gs =>
    (singlePortLeft G.matrix).submatrix (starPortSplit n ns) (starPortSplit n ns) ::
      (starPortFactorMatrices gs).map (starPortExtendTail n ns)

/-- The unitary product of gates with one common port and otherwise disjoint
blocks satisfies determinant inclusion for every pair of complex spectra. -/
theorem holds_starPortMixer {sizes : List ℕ} (gs : StarPortGates sizes) :
    IsUnitary (starPortFactorMatrices gs).prod ∧
      ∀ a b, Holds a b (starPortFactorMatrices gs).prod := by
  induction gs with
  | nil => exact ⟨isUnitary_one, holds_identity⟩
  | @cons n ns G gs ih =>
    let e := starPortSplit n ns
    let P := (starPortFactorMatrices gs).prod
    let V : Matrix ((Fin n ⊕ Unit) ⊕ StarPortPetals ns) _ ℂ := singlePortLeft G.matrix
    let W : Matrix ((Fin n ⊕ Unit) ⊕ StarPortPetals ns) _ ℂ := singlePortRight P
    have hprod : (starPortFactorMatrices (.cons G gs)).prod = (V * W).submatrix e e := by
      rw [starPortFactorMatrices, List.prod_cons, ← map_list_prod]
      exact Matrix.submatrix_mul_equiv V W e e e
    have hV : IsUnitary V := unitary_directSum G.unitary isUnitary_one
    have hW : IsUnitary W :=
      unitary_reindex _ _ (unitary_directSum isUnitary_one ih.1)
    have hVW : IsUnitary (V * W) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        relative_unitary (V := Vᴴ) (W := W) (by
          simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose, and_comm] using hV) hW
    rw [hprod]
    refine ⟨unitary_reindex e e hVW, fun a b => ?_⟩
    have h := (holds_reindex_iff e e (a ∘ e.symm) (b ∘ e.symm) (V * W)).mpr
      (holds_singlePortComposition _ _ _ _ G.unitary ih.1 G.covered ih.2)
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using h

end

end MOC
