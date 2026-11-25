import MOC.HouseholderSupport
import MOC.PermutationPathComposition
import MOC.SpectralMinorDecomposition
import MOC.Small

/-! Composition of two covered mixing blocks with one shared coordinate.
The local weights need be common only for the single free port eigenvalue. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

private abbrev Domain (L R : Type*) := (L ⊕ Unit) ⊕ R

/-- The left block acts on the left labels and the shared label. -/
def singlePortLeft (V : Matrix (L ⊕ Unit) (L ⊕ Unit) ℂ) : Matrix (Domain L R) (Domain L R) ℂ :=
  fromBlocks V 0 0 1

/-- The right block acts on the shared label and the right labels. -/
def singlePortRight (W : Matrix (Unit ⊕ R) (Unit ⊕ R) ℂ) : Matrix (Domain L R) (Domain L R) ℂ :=
  (fromBlocks (1 : Matrix L L ℂ) 0 0 W).submatrix
    (Equiv.sumAssoc L Unit R) (Equiv.sumAssoc L Unit R)

omit [Fintype L] [Fintype R] in
private theorem portRight_entry (W : Matrix (Unit ⊕ R) (Unit ⊕ R) ℂ)
    (i : L) (j : Domain L R) :
    singlePortRight W j (.inl (.inl i)) = if j = .inl (.inl i) then 1 else 0 := by
  cases j with
  | inl j =>
    cases j with
    | inl l => simp [singlePortRight, Matrix.one_apply]
    | inr u => simp [singlePortRight]
  | inr r => simp [singlePortRight]

private theorem supported_right_fixes_left (W : Matrix (Unit ⊕ R) (Unit ⊕ R) ℂ)
    (q : Equiv.Perm (Domain L R)) (hq : signedWeight (singlePortRight W) q ≠ 0) (i : L) :
    q.symm (.inl (.inl i)) = .inl (.inl i) := by
  apply q.injective
  rw [q.apply_symm_apply]
  by_contra hn
  have hentry : singlePortRight W (q (.inl (.inl i))) (.inl (.inl i)) = 0 := by
    rw [portRight_entry, if_neg (Ne.symm hn)]
  exact hq (by
    unfold signedWeight leibnizTerm
    have hz : (∏ j, singlePortRight W (q j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ _) hentry
    rw [hz, mul_zero, zero_div])

private theorem port_det_sum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (a b : I → ℂ) (c d : J → ℂ) (V : Matrix I I ℂ) :
    determinantValue (Sum.elim a c) (Sum.elim b d) (fromBlocks V 0 0 (1 : Matrix J J ℂ)) =
      determinantValue a b V * matchingProduct c d (Equiv.refl J) := by
  unfold determinantValue matchingProduct
  rw [← Matrix.fromBlocks_diagonal, ← Matrix.fromBlocks_diagonal,
    Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.det_fromBlocks_zero₂₁,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, Matrix.diagonal_add,
    Matrix.det_diagonal, Pi.add_apply, Equiv.refl_apply]

private theorem port_left_law {T : Type*} [Fintype T] (a b : Domain L R → ℂ)
    (V : Matrix (L ⊕ Unit) (L ⊕ Unit) ℂ)
    (p : T → Equiv.Perm (L ⊕ Unit)) (w : T → ℝ)
    (hw : ∀ z : ℂ, (∑ i, (w i : ℂ) * matchingProduct (a ∘ Sum.inl)
      (Function.update (b ∘ Sum.inl) (.inr ()) z) (p i)) =
      determinantValue (a ∘ Sum.inl) (Function.update (b ∘ Sum.inl) (.inr ()) z) V)
    (q : Equiv.Perm (Domain L R)) (hq : ∀ l : L, q.symm (.inl (.inl l)) = .inl (.inl l)) :
    (∑ i, (w i : ℂ) * matchingProduct a (b ∘ q.symm) (Equiv.sumCongr (p i) (Equiv.refl R))) =
      determinantValue a (b ∘ q.symm) (singlePortLeft V) := by
  let d := b ∘ q.symm ∘ Sum.inr
  let z := b (q.symm (.inl (.inr ())))
  let e := Function.update (b ∘ Sum.inl) (.inr ()) z
  have hb : b ∘ q.symm = Sum.elim e d := by
    funext j
    cases j with
    | inr j => rfl
    | inl j =>
      cases j with
      | inl l => simp [e, Function.comp_apply, hq, Function.update_of_ne]
      | inr u => cases u; simp [e, z]
  have ha : a = Sum.elim (a ∘ Sum.inl) (a ∘ Sum.inr) := by
    funext j; cases j <;> rfl
  rw [hb]
  have hm (t : T) : matchingProduct a (Sum.elim e d) (Equiv.sumCongr (p t) (Equiv.refl R)) =
      matchingProduct (a ∘ Sum.inl) e (p t) * matchingProduct (a ∘ Sum.inr) d (Equiv.refl R) := by
    conv_lhs => rw [ha]
    exact matchingProduct_sum _ _ _ _ _ _
  have hd : determinantValue a (Sum.elim e d) (singlePortLeft V) =
      determinantValue (a ∘ Sum.inl) e V * matchingProduct (a ∘ Sum.inr) d (Equiv.refl R) := by
    conv_lhs => rw [ha]
    exact port_det_sum _ _ _ _ _
  simp_rw [hm, hd, ← mul_assoc]
  rw [← Finset.sum_mul]
  exact congrArg (· * matchingProduct (a ∘ Sum.inr) d (Equiv.refl R)) (hw z)

private theorem port_right_holds (W : Matrix (Unit ⊕ R) (Unit ⊕ R) ℂ)
    (hW : ∀ a b, Holds a b W) (a b : Domain L R → ℂ) :
    Holds a b (singlePortRight W) := by
  let e := Equiv.sumAssoc L Unit R
  let c := a ∘ e.symm
  let d := b ∘ e.symm
  have hc : c = Sum.elim (c ∘ Sum.inl) (c ∘ Sum.inr) := by funext i; cases i <;> rfl
  have hd : d = Sum.elim (d ∘ Sum.inl) (d ∘ Sum.inr) := by funext i; cases i <;> rfl
  have H : Holds c d (fromBlocks (1 : Matrix L L ℂ) 0 0 W) := by
    rw [hc,hd]
    exact holds_directSum _ _ _ _ _ _ (holds_identity _ _) (hW _ _)
  have H' := (holds_reindex_iff e e c d _).mpr H
  simpa [c, d, Function.comp_assoc, singlePortRight, e] using H'

private theorem port_paths (V : Matrix (L ⊕ Unit) (L ⊕ Unit) ℂ)
    (W : Matrix (Unit ⊕ R) (Unit ⊕ R) ℂ) :
    BijectivePermutationPaths (singlePortLeft V) (singlePortRight W) := by
  classical
  let a : Domain L R → Bool := Sum.elim (fun _ => true) (fun _ => false)
  let b : Domain L R → Bool := Sum.elim (Sum.elim (fun _ => false) (fun _ => true)) (fun _ => true)
  let A := Finset.univ.filter (fun i => a i = true)
  let B := Finset.univ.filter (fun i => b i = true)
  apply bijectivePermutationPaths_of_single_overlap _ _ A B (.inl (.inr ()))
  · rintro ((l|u)|r) <;> simp [A,B,a,b]
  · rintro ((i|u)|r) ((j|v)|s) h <;>
      simp [A,a,singlePortLeft,Matrix.one_apply] at h ⊢; assumption
  · rintro ((i|u)|r) ((j|v)|s) h <;>
      simp [B,b,singlePortRight,Matrix.one_apply] at h ⊢; assumption

/-- Two unitary mixing blocks that share exactly one coordinate preserve MOC
for arbitrary spectra if each local mixer satisfies MOC for arbitrary spectra.
The assertion uses no spectrum-independent law for either mixer. -/
theorem holds_singlePortComposition (a b : ((L ⊕ Unit) ⊕ R) → ℂ)
    (V : Matrix (L ⊕ Unit) (L ⊕ Unit) ℂ) (W : Matrix (Unit ⊕ R) (Unit ⊕ R) ℂ)
    (hV : IsUnitary V) (hW : IsUnitary W)
    (hv : ∀ c d, Holds c d V) (hw : ∀ c d, Holds c d W) :
    Holds a b (singlePortLeft V * singlePortRight W) := by
  classical
  have hleft : IsUnitary (singlePortLeft (R := R) V) := unitary_directSum hV (by simp [IsUnitary])
  have hright : IsUnitary (singlePortRight (L := L) W) :=
    unitary_reindex _ _ (unitary_directSum (by simp [IsUnitary]) hW)
  obtain ⟨k, _, p, w, hpos, hsum, hvalue⟩ :=
    (one_free_partner_entry_iff_common_law (a ∘ Sum.inl) (b ∘ Sum.inl) (.inr ()) V hV).mp
      (fun _ => hv _ _)
  let P (i : Fin k) := Equiv.sumCongr (p i) (Equiv.refl R)
  have hh := determinantValue_mul_of_bijective_paths_on_support a b
    (singlePortLeft V) (singlePortRight W) hleft hright (port_paths V W) P w
    (fun q hq => port_left_law a b V p w hvalue q (supported_right_fixes_left W q hq))
  unfold Holds
  rw [hh]
  simp_rw [← Complex.real_smul]
  apply (convex_convexHull ℝ _).sum_mem (fun i _ => hpos i) hsum
  intro i _
  apply convexHull_mono _ (port_right_holds W hw (a ∘ P i) b)
  rintro _ ⟨q, rfl⟩
  exact ⟨P i * q, rfl⟩

/-- Two Householder reflections on coordinate blocks with one shared label
satisfy the determinant inclusion for arbitrary complex spectra. The result
uses Drury's inclusion for each reflection (DOI: 10.1016/S0024-3795(99)00173-1). -/
theorem holds_singlePortHouseholderComposition (a b : ((L ⊕ Unit) ⊕ R) → ℂ)
    (v : L ⊕ Unit → ℂ) (w : Unit ⊕ R → ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hw : ∑ i, star (w i) * w i = 1) :
    Holds a b (singlePortLeft (rankOnePhase v (-1)) * singlePortRight (rankOnePhase w (-1))) :=
  holds_singlePortComposition a b _ _
    (rankOnePhase_unitary v (-1) hv (by simp)) (rankOnePhase_unitary w (-1) hw (by simp))
    (fun c d => holds_householder c d v hv) (fun c d => holds_householder c d w hw)

end

end MOC
