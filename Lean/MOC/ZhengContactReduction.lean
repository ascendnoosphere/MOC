import MOC.FourMinorTransport
import MOC.AffineGapCover

/-! A sharper order-four version of the contact reduction in Zheng,
Theorem 3.6 (preprint DOI: 10.13140/RG.2.2.36790.25923). The last
support inequality, not the reduction, is the open Lean target. -/

open BigOperators Matrix

namespace MOC

/-- In order four, a proof on real orthogonal mixers with at least seven
contacts suffices. No part of the terminal case classification is assumed. -/
theorem conjecture_four_iff_seven_orthogonal_contacts :
    Conjecture (Fin 4) ↔ ¬ ∃ O : Matrix.orthogonalGroup (Fin 4) ℝ,
      ∃ w : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O.val),
        7 ≤ w.contacts.card := by
  constructor
  · rintro h ⟨O, w, -⟩
    exact w.not_holds (h w.a w.b (Complex.ofRealHom.mapMatrix O.val)
      (isUnitary_ofReal_orthogonal O))
  · intro h
    apply conjecture_four_iff_orthogonal.mpr
    intro a b O
    classical
    let U := Complex.ofRealHom.mapMatrix O.val
    have hU : IsUnitary U := isUnitary_ofReal_orthogonal O
    apply Classical.byContradiction
    intro hf
    change ¬ Holds a b U at hf
    obtain ⟨w⟩ := nonempty_strictMatchingSupport_of_failure a b hf
    obtain ⟨v, hv⟩ := exists_strictMatchingSupport_at_least 7 w (fun u hu => by
      have hbound : u.contacts.card ≤ 2 * Fintype.card (Fin 4) - 2 := by
        rw [Fintype.card_fin]
        exact Nat.le_of_lt_succ hu
      obtain ⟨v, _, _, hinc, _⟩ := global_varying_gap_contact_transfer
        (affineGapContinuation (Equiv.Perm (Fin 4))) hU u hbound
      exact ⟨v, Finset.card_lt_card hinc⟩)
    exact h ⟨O, v, hv⟩

end MOC
