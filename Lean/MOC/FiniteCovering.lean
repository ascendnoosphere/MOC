import Mathlib.Topology.Covering
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Hausdorff

/-! A finite-degree local homeomorphism is a covering. The root branches
above a regular value of a plane curve can be used as its local charts. -/

open Set Function Bundle

namespace MOC

/-- Local inverse branches of a map of constant positive finite degree
give covering trivializations when the domain is Hausdorff. -/
theorem isCoveringMap_of_localHomeomorph_finite_degree
    {E B : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace B]
    {p : E → B} (hlocal : IsLocalHomeomorph p) {d : ℕ} (hd : 0 < d)
    (hdegree : ∀ b : B, Nonempty (Fin d ≃ ↥(p ⁻¹' {b}))) : IsCoveringMap p := by
  classical
  intro b₀
  let e (b : B) : Fin d ≃ ↥(p ⁻¹' {b}) := Classical.choice (hdegree b)
  let a (i : Fin d) : E := (e b₀ i).val
  have ha (i : Fin d) : p (a i) = b₀ := (e b₀ i).property
  obtain ⟨N, hN, hsep⟩ := (Set.finite_range a).t2_separation
  have hdisj {i j : Fin d} (hij : i ≠ j) : Disjoint (N (a i)) (N (a j)) :=
    hsep ⟨i, rfl⟩ ⟨j, rfl⟩ (fun h => hij ((e b₀).injective (Subtype.ext h)))
  choose q hq hpeq using fun i : Fin d => hlocal (a i)
  let U : Set B := ⋂ i : Fin d, ((q i).target ∩ (q i).symm ⁻¹' N (a i))
  have hUopen : IsOpen U := isOpen_iInter_of_finite fun i =>
    (q i).continuousOn_invFun.isOpen_inter_preimage (q i).open_target (hN (a i)).2
  have hb₀ : b₀ ∈ U := by
    apply mem_iInter.mpr
    intro i
    have hh : q i (a i) = b₀ := (congrFun (hpeq i).symm (a i)).trans (ha i)
    rw [← hh]
    exact ⟨(q i).map_source (hq i), by rw [mem_preimage, (q i).left_inv (hq i)]; exact (hN (a i)).1⟩
  have htarget {b : B} (hb : b ∈ U) (i : Fin d) : b ∈ (q i).target :=
    ((mem_iInter.mp hb) i).1
  let F (bi : B × Fin d) : E := (q bi.2).symm bi.1
  have hpF {b : B} (hb : b ∈ U) (i : Fin d) : p (F (b, i)) = b := by
    change p ((q i).symm b) = b
    rw [hpeq i, (q i).right_inv (htarget hb i)]
  have hlabel {b b' : B} {i j : Fin d} (hb : b ∈ U) (hb' : b' ∈ U)
      (h : F (b, i) = F (b', j)) : i = j := by
    apply Classical.byContradiction
    intro hij
    have hi : F (b, i) ∈ N (a i) := ((mem_iInter.mp hb) i).2
    have hj : F (b', j) ∈ N (a j) := ((mem_iInter.mp hb') j).2
    exact Set.disjoint_left.mp (hdisj hij) hi (h.symm ▸ hj)
  let D : Set (B × Fin d) := U ×ˢ univ
  have hbij : BijOn F D (p ⁻¹' U) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨b, i⟩ hb
      change p (F (b, i)) ∈ U
      rw [hpF hb.1 i]
      exact hb.1
    · rintro ⟨b, i⟩ hb ⟨b', j⟩ hb' he
      have hbase : b = b' := (hpF hb.1 i).symm.trans ((congrArg p he).trans (hpF hb'.1 j))
      exact Prod.ext hbase (hlabel hb.1 hb'.1 he)
    · intro x hx
      let b := p x
      let lift (i : Fin d) : ↥(p ⁻¹' {b}) := ⟨F (b, i), hpF hx i⟩
      have hinj : Injective lift := fun i j h => hlabel hx hx (congrArg Subtype.val h)
      have hsurj := Finite.surjective_of_injective ((e b).symm.injective.comp hinj)
      obtain ⟨i, hi⟩ := hsurj ((e b).symm ⟨x, rfl⟩)
      exact ⟨(b, i), ⟨hx, mem_univ i⟩, congrArg Subtype.val ((e b).symm.injective hi)⟩
  have hFcont : ContinuousOn F D := continuousOn_prod_of_discrete_right.2 fun i =>
    (q i).continuousOn_invFun.mono (fun _ hb => htarget hb.1 i)
  have hFopen : IsOpenMap (D.restrict F) := by
    intro O hO
    let slice (i : Fin d) (u : U) : D := ⟨(u.val, i), ⟨u.property, mem_univ i⟩⟩
    let V (i : Fin d) : Set B := Subtype.val '' (slice i ⁻¹' O)
    have hV (i : Fin d) : IsOpen (V i) :=
      hUopen.isOpenMap_subtype_val _
        (hO.preimage ((continuous_subtype_val.prodMk continuous_const).subtype_mk
          (fun u : U => ⟨u.property, mem_univ i⟩)))
    have hVu (i : Fin d) : V i ⊆ U := by
      rintro _ ⟨u, _, rfl⟩
      exact u.property
    have heq : (D.restrict F) '' O = ⋃ i, (q i).symm '' V i := by
      ext y
      constructor
      · rintro ⟨⟨⟨b, i⟩, hb⟩, hO', rfl⟩
        exact mem_iUnion.mpr ⟨i, b, ⟨⟨b, hb.1⟩, hO', rfl⟩, rfl⟩
      · intro hy
        rcases mem_iUnion.mp hy with ⟨i, b, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨slice i u, hu, rfl⟩
    rw [heq]
    exact isOpen_iUnion fun i =>
      (q i).isOpen_image_symm_of_subset_target (hV i) (fun _ hb => htarget (hVu i hb) i)
  letI : Nonempty (B × Fin d) := ⟨(b₀, ⟨0, hd⟩)⟩
  let f := Set.BijOn.toPartialEquiv F D (p ⁻¹' U) hbij
  let t := (PartialHomeomorph.ofContinuousOpenRestrict f hFcont hFopen
    (hUopen.prod isOpen_univ)).symm
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Fin d)
  refine ⟨inferInstance, ⟨{
    toPartialHomeomorph := t
    baseSet := U
    open_baseSet := hUopen
    source_eq := rfl
    target_eq := rfl
    proj_toFun := ?_ }, hb₀⟩⟩
  intro x hx
  have htx : (t x).1 ∈ U := (t.map_source hx).1
  calc
    (t x).1 = p (F (t x)) := (hpF htx (t x).2).symm
    _ = p x := congrArg p (t.left_inv hx)

end MOC
