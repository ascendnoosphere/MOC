import MOC.BlockConstraintLeray
import MOC.PaddedConstraintNerve

/-! Leray lower bounds in orders that include a padded block. -/

open Finset Matrix BigOperators

namespace MOC

noncomputable section

private abbrev PaddedNerveBlock (k : ℕ) := Lex (Unit ⊕ Fin k)

private def paddedNerveIndex {k : ℕ} (r : ℕ) : PaddedNerveBlock k → Type
  | Sum.inl _ => Fin 4 ⊕ Fin r
  | Sum.inr _ => Fin 4

private instance paddedNerveIndexFintype {k r : ℕ} (j : PaddedNerveBlock k) :
    Fintype (paddedNerveIndex r j) := by
  change Unit ⊕ Fin k at j
  rcases j with (_ | _)
  · exact inferInstanceAs (Fintype (Fin 4 ⊕ Fin r))
  · exact inferInstanceAs (Fintype (Fin 4))

private instance paddedNerveIndexDecidableEq {k r : ℕ} (j : PaddedNerveBlock k) :
    DecidableEq (paddedNerveIndex r j) := by
  change Unit ⊕ Fin k at j
  rcases j with (_ | _)
  · exact inferInstanceAs (DecidableEq (Fin 4 ⊕ Fin r))
  · exact inferInstanceAs (DecidableEq (Fin 4))

private def paddedNerveDimension {k : ℕ} (r : ℕ) : PaddedNerveBlock k → ℕ
  | Sum.inl _ => 12 + r
  | Sum.inr _ => 12

private def paddedNerveMixer {k : ℕ} (r : ℕ) :
    (j : PaddedNerveBlock k) → Matrix (paddedNerveIndex r j) (paddedNerveIndex r j) ℂ
  | Sum.inl _ => paddedConstraintMixer r
  | Sum.inr _ => fourMarginalMixer

private def paddedNerveProbeEquiv (r : ℕ) : Fin (12 + r + 1) ≃ Fin 13 ⊕ Fin r :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

private def paddedNerveRows {k : ℕ} (r : ℕ) :
    (j : PaddedNerveBlock k) → Fin (paddedNerveDimension r j + 1) → Finset (paddedNerveIndex r j)
  | Sum.inl _ => paddedConstraintRows r ∘ paddedNerveProbeEquiv r
  | Sum.inr _ => fun i => ordinaryCostRows (fourConstraintRay i)

private def paddedNerveColumns {k : ℕ} (r : ℕ) :
    (j : PaddedNerveBlock k) → Fin (paddedNerveDimension r j + 1) → Finset (paddedNerveIndex r j)
  | Sum.inl _ => paddedConstraintColumns r ∘ paddedNerveProbeEquiv r
  | Sum.inr _ => fun i => ordinaryCostColumns (fourConstraintRay i)

/-- The row and column labels for one padded mixer and `k` order-four mixers. -/
abbrev PaddedBlockMinorIndex (k r : ℕ) := Σ j : PaddedNerveBlock k, paddedNerveIndex r j

theorem paddedBlockMinorIndex_card (k r : ℕ) :
    Fintype.card (PaddedBlockMinorIndex k r) = 4 * (k + 1) + r := by
  rw [Fintype.card_sigma]
  change (∑ j : Unit ⊕ Fin k, Fintype.card (paddedNerveIndex r j)) = _
  simp [Fintype.sum_sum_type, paddedNerveIndex, Fintype.card_sum, Finset.sum_const, nsmul_eq_mul] <;>
    omega

/-- The block matrix is unitary in the stated order. -/
def paddedBlockMinorMixer (k r : ℕ) :
    Matrix (PaddedBlockMinorIndex k r) (PaddedBlockMinorIndex k r) ℂ :=
  blockDiagonal' (paddedNerveMixer r)

private theorem paddedNerveMixer_unitary {k r : ℕ} (j : PaddedNerveBlock k) :
    IsUnitary (paddedNerveMixer r j) := by
  change Unit ⊕ Fin k at j
  rcases j with (_ | _)
  · exact paddedConstraintMixer_unitary r
  · exact fourMarginalMixer_unitary

theorem paddedBlockMinorMixer_unitary (k r : ℕ) : IsUnitary (paddedBlockMinorMixer k r) :=
  blockDiagonal'_isUnitary _ paddedNerveMixer_unitary

/-- A relabeling of the probes preserves every feasibility constraint. -/
private theorem minorConstraintNerve_map_equiv {v w ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : v ≃ w) (U : Matrix ι ι ℂ) (I J : w → Finset ι) (s : Finset v) :
    s ∈ minorConstraintNerve U (I ∘ e) (J ∘ e) ↔
      s.map e.toEmbedding ∈ minorConstraintNerve U I J := by
  constructor
  · rintro ⟨W, hW, hm, hc⟩
    refine ⟨W, hW, hm, ?_⟩
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact hc j hj
  · rintro ⟨W, hW, hm, hc⟩
    exact ⟨W, hW, hm, fun i hi => hc (e i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)⟩

private theorem paddedNerve_local_boundaries {k r : ℕ} (j : PaddedNerveBlock k)
    (s : Finset (Fin (paddedNerveDimension r j + 1))) :
    s ∈ minorConstraintNerve (paddedNerveMixer r j) (paddedNerveRows r j) (paddedNerveColumns r j) ↔
      s ≠ univ := by
  change Unit ⊕ Fin k at j
  rcases j with (_ | _)
  · let e := paddedNerveProbeEquiv r
    change s ∈ minorConstraintNerve (paddedConstraintMixer r)
      (paddedConstraintRows r ∘ e) (paddedConstraintColumns r ∘ e) ↔ _
    rw [minorConstraintNerve_map_equiv]
    change PaddedConstraintFeasible r (s.map e.toEmbedding) ↔ _
    rw [paddedConstraintFeasible_iff]
    rw [← Finset.map_univ_equiv e, Finset.map_inj]
  · exact (fourConstraintFeasible_subsetImage_iff s).symm.trans (fourConstraintFeasible_iff s)

/-- The nerve of the selected observations in the padded direct sum. -/
def paddedBlockMinorNerve (k r : ℕ) :
    Set (Finset (BlockObservationVertex
      (@paddedNerveDimension k r) (@paddedNerveIndex k r))) :=
  blockObservationNerve (paddedNerveMixer r) (paddedNerveRows r) (paddedNerveColumns r)

/-- In matrix order `4(k+1)+r`, the selected minor nerve has Leray number
at least `12(k+1)+r`. This includes all nonzero remainders. -/
theorem paddedBlockMinorNerve_not_leray (k r d : ℕ) (hd : d < 12 * (k + 1) + r) :
    ¬ IsFiniteSimplicialLeray (paddedBlockMinorNerve k r) d := by
  apply blockObservationNerve_not_leray _ paddedNerveMixer_unitary _ _ paddedNerve_local_boundaries
  change d < ∑ j : Unit ⊕ Fin k, paddedNerveDimension r j
  simp [Fintype.sum_sum_type, paddedNerveDimension, Finset.sum_const, nsmul_eq_mul] <;> omega

end

end MOC
