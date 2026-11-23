import MOC.LiftedSimplex

open BigOperators

namespace MOC

/-- A finite collection of lists of real scores has a lexicographic maximum. -/
theorem exists_maximum_score_list (n : ℕ) (C : Type*) [Fintype C] [Nonempty C]
    (L : C → Fin n → ℝ) :
    ∃ t : C, ∀ c i, (∀ k, k < i → L c k = L t k) → L c i ≤ L t i := by
  classical
  induction n generalizing C with
  | zero =>
    exact ⟨Classical.choice inferInstance, fun c i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (fun c => L c 0) Finset.univ_nonempty
    let F := {c : C // L c 0 = L a 0}
    letI : Fintype F := Fintype.ofFinite F
    letI : Nonempty F := ⟨⟨a, rfl⟩⟩
    obtain ⟨b,hb⟩ := ih F (fun c k => L c.val k.succ)
    refine ⟨b.val, ?_⟩
    intro c i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _
      rw [b.property]
      exact ha c (Finset.mem_univ c)
    · intro h
      let c' : F := ⟨c, (h 0 (Fin.succ_pos j)).trans b.property⟩
      exact hb c' j (fun k hk => h k.succ (Fin.succ_lt_succ_iff.mpr hk))

end MOC
