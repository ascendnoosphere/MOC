import Mathlib.Logic.Equiv.Fintype

/-! Assignment of rounded values to distinct labels that carry those values. -/

namespace MOC

/-- On the selected rows, replace each rounded endpoint by a distinct label
that carries that endpoint. The exceptional label keeps its assigned row. -/
theorem exists_perm_reciprocal_segment_rematch
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (E : Finset ι) (exception : ι) (q rounded : ι → β) (p s : β) (hps : p ≠ s)
    (hp : E.card ≤ (Finset.univ.filter fun j => j ≠ exception ∧ q j = p).card)
    (hs : E.card ≤ (Finset.univ.filter fun j => j ≠ exception ∧ q j = s).card)
    (hr : ∀ j ≠ exception, rounded j = p ∨ rounded j = s) (σ : Equiv.Perm ι) :
    ∃ τ : Equiv.Perm ι, τ exception = σ exception ∧
      ∀ i ∈ E, i ≠ σ exception → q (τ.symm i) = rounded (σ.symm i) := by
  classical
  let targets (v : β) := Finset.univ.filter (fun j => j ≠ exception ∧ q j = v)
  have endpoint_spec (v : β) (j : targets v) : (j : ι) ≠ exception ∧ q j = v :=
    (Finset.mem_filter.mp j.property).2
  obtain ⟨ep⟩ : Nonempty (E ↪ targets p) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using hp)
  obtain ⟨es⟩ : Nonempty (E ↪ targets s) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using hs)
  let label (i : E) : ι :=
    if rounded (σ.symm i) = p then ep i else es i
  have label_ne (i : E) : label i ≠ exception := by
    unfold label
    split
    · exact (endpoint_spec p (ep i)).1
    · exact (endpoint_spec s (es i)).1
  have label_value (i : E) (hi : (i : ι) ≠ σ exception) :
      q (label i) = rounded (σ.symm i) := by
    have hinv : σ.symm i ≠ exception := fun h => hi (by rw [← h, σ.apply_symm_apply])
    unfold label
    split
    · rename_i h
      exact (endpoint_spec p (ep i)).2.trans h.symm
    · rename_i h
      exact (endpoint_spec s (es i)).2.trans ((hr _ hinv).resolve_left h).symm
  have label_injective : Function.Injective label := by
    intro i j h
    by_cases hi : rounded (σ.symm i) = p <;> by_cases hj : rounded (σ.symm j) = p
    · exact ep.injective (Subtype.ext (by simpa only [label, if_pos hi, if_pos hj] using h))
    · have he : (ep i : ι) = es j := by simpa only [label, if_pos hi, if_neg hj] using h
      exact (hps ((endpoint_spec p (ep i)).2.symm.trans
        ((congrArg q he).trans (endpoint_spec s (es j)).2))).elim
    · have he : (ep j : ι) = es i := by simpa only [label, if_neg hi, if_pos hj] using h.symm
      exact (hps ((endpoint_spec p (ep j)).2.symm.trans
        ((congrArg q he).trans (endpoint_spec s (es i)).2))).elim
    · exact es.injective (Subtype.ext (by simpa only [label, if_neg hi, if_neg hj] using h))
  let rows := insert (σ exception) E
  let assign (i : rows) : ι := if hi : (i : ι) = σ exception then exception
    else label ⟨i, (Finset.mem_insert.mp i.property).resolve_left hi⟩
  have assign_injective : Function.Injective assign := by
    intro i j h
    dsimp only [assign] at h
    by_cases hi : (i : ι) = σ exception <;> by_cases hj : (j : ι) = σ exception
    · exact Subtype.ext (hi.trans hj.symm)
    · rw [dif_pos hi, dif_neg hj] at h
      exact (label_ne _ h.symm).elim
    · rw [dif_neg hi, dif_pos hj] at h
      exact (label_ne _ h).elim
    · rw [dif_neg hi, dif_neg hj] at h
      exact Subtype.ext (congrArg (fun x : E => (x : ι)) (label_injective h))
  let e := Equiv.ofInjective assign assign_injective
  have extension (i : ι) (hi : i ∈ rows) : e.extendSubtype i = assign ⟨i, hi⟩ :=
    e.extendSubtype_apply_of_mem i hi
  have special : e.extendSubtype (σ exception) = exception := by
    rw [extension _ (Finset.mem_insert_self _ _)]
    simp only [assign, dif_pos rfl]
  refine ⟨e.extendSubtype.symm, ?_, ?_⟩
  · calc
      e.extendSubtype.symm exception = e.extendSubtype.symm (e.extendSubtype (σ exception)) :=
        congrArg e.extendSubtype.symm special.symm
      _ = σ exception := e.extendSubtype.symm_apply_apply _
  · intro i hi hn
    change q (e.extendSubtype i) = _
    rw [extension _ (Finset.mem_insert_of_mem hi)]
    simpa only [assign, dif_neg hn] using label_value ⟨i, hi⟩ hn

end MOC
