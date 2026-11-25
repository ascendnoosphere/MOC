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
  · rintro h ⟨O,w,-⟩
    have hO := isUnitary_ofReal_orthogonal O
    obtain ⟨q,hq⟩ := (holds_iff_directional _ _ _).mp (h w.a w.b _ hO) w.η
    exact (not_lt_of_ge (hq.trans (w.maximal q))) w.strict
  · intro h
    apply conjecture_four_iff_orthogonal.mpr
    intro a b O
    classical
    let U := Complex.ofRealHom.mapMatrix O.val
    have hU : IsUnitary U := isUnitary_ofReal_orthogonal O
    apply Classical.byContradiction
    intro hf
    change ¬ Holds a b U at hf
    rw [holds_iff_directional, not_forall] at hf
    obtain ⟨η,hη⟩ := hf
    push_neg at hη
    obtain ⟨p,_,hp⟩ := Finset.exists_max_image Finset.univ
      (fun q : Equiv.Perm (Fin 4) => (η * matchingProduct a b q).re)
      ⟨1,Finset.mem_univ _⟩
    let w : StrictMatchingSupport U :=
      ⟨a,b,η,p,fun q => hp q (Finset.mem_univ _),hη p⟩
    have step (d : ℕ) (u : StrictMatchingSupport U) (hd : 7 - u.contacts.card = d) :
        ∃ v : StrictMatchingSupport U, 7 ≤ v.contacts.card := by
      induction d using Nat.strong_induction_on generalizing u with
      | h d ih =>
        by_cases hk : 7 ≤ u.contacts.card
        · exact ⟨u,hk⟩
        · have hh : u.contacts.card ≤ 2 * Fintype.card (Fin 4) - 2 := by
            rw [Fintype.card_fin]
            omega
          obtain ⟨v,_,_,hv,_⟩ := global_varying_gap_contact_transfer
            (affineGapContinuation (Equiv.Perm (Fin 4))) hU u hh
          have hh := Finset.card_lt_card hv
          exact ih (7 - v.contacts.card) (by omega) v rfl
    obtain ⟨v,hv⟩ := step _ w rfl
    exact h ⟨O,v,hv⟩

end MOC
