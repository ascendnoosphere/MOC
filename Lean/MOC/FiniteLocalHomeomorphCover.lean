import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Maps.Proper.Basic

/-! A proper finite local homeomorphism is a covering. -/

open Filter Set Bundle unitInterval
open scoped Topology

namespace MOC

/-- A closed surjective local homeomorphism between Hausdorff spaces with
finite fibers is a covering. The finite algebraic curve hypotheses normally
supply closedness by properness. -/
theorem isCoveringMap_of_closedMap_finite_localHomeomorph
    {E X : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
    (f : E → X) (hf : IsLocalHomeomorph f) (hclosed : IsClosedMap f)
    (hfinite : ∀ x : X, (f ⁻¹' ({x} : Set X)).Finite) (hsurj : Function.Surjective f) :
    IsCoveringMap f := by
  classical
  intro x
  let T := f ⁻¹' ({x} : Set X)
  let F := ↥T
  letI : Finite F := (hfinite x).to_subtype
  haveI : DiscreteTopology F := inferInstance
  refine ⟨inferInstance, ?_⟩
  obtain ⟨u, hu⟩ := hsurj x
  let i₀ : F := ⟨u, hu⟩
  obtain ⟨U, hU, hdis⟩ := (hfinite x).t2_separation
  have hchart (i : F) : ∃ e : PartialHomeomorph E X, i.val ∈ e.source ∧ f = e :=
    hf i.val
  choose e hsrc heq using hchart
  let W (i : F) := U i.val ∩ (e i).source
  have hW (i : F) : IsOpen (W i) := (hU i.val).2.inter (e i).open_source
  have hiW (i : F) : i.val ∈ W i := ⟨(hU i.val).1, hsrc i⟩
  have hdisW ⦃i j : F⦄ (hij : i ≠ j) : Disjoint (W i) (W j) :=
    (hdis i.property j.property (fun h => hij (Subtype.ext h))).mono inter_subset_left inter_subset_left
  let V := (⋂ i, f '' W i) ∩ (f '' ((⋃ i, W i)ᶜ))ᶜ
  have hV : IsOpen V := (isOpen_iInter_of_finite fun i => hf.isOpenMap _ (hW i)).inter
    (hclosed _ (isOpen_iUnion hW).isClosed_compl).isOpen_compl
  have hxV : x ∈ V := by
    refine ⟨mem_iInter.mpr (fun i => ⟨i.val, hiW i, i.property⟩), ?_⟩
    rintro ⟨a, ha, hax⟩
    exact ha (mem_iUnion.mpr ⟨(⟨a, hax⟩ : F), hiW _⟩)
  have hWV {a : E} (ha : f a ∈ V) : ∃ i : F, a ∈ W i := by
    by_contra! hn
    exact ha.2 ⟨a, fun hu => (mem_iUnion.mp hu).elim hn, rfl⟩
  let ind (a : E) : F := if h : ∃ i : F, a ∈ W i then h.choose else i₀
  have hind (a : E) (i : F) (ha : a ∈ W i) : ind a = i := by
    have h : ∃ j, a ∈ W j := ⟨i, ha⟩
    dsimp only [ind]
    rw [dif_pos h]
    by_contra hn
    exact (Set.disjoint_left.mp (hdisW hn)) h.choose_spec ha
  let un (p : X × F) : E := (e p.2).symm p.1
  have hun (y : X) (i : F) (hy : y ∈ V) : un (y,i) ∈ W i ∧ f (un (y,i)) = y := by
    obtain ⟨a, ha, hay⟩ := mem_iInter.mp hy.1 i
    have hx : (e i) a = y := (congrFun (heq i).symm a).trans hay
    have hleft := (e i).left_inv ha.2
    have h : un (y,i) = a := by simpa only [un, ← hx] using hleft
    exact ⟨h ▸ ha, by rw [h, hay]⟩
  have hc_ind : ContinuousOn ind (f ⁻¹' V) := by
    intro a ha
    have ha' : f a ∈ V := ha
    obtain ⟨i, hi⟩ := hWV ha'
    have he : (fun _ : E => i) =ᶠ[𝓝 a] ind := by
      filter_upwards [(hW i).mem_nhds hi] with b hb
      exact (hind b i hb).symm
    exact (continuousAt_const.congr he).continuousWithinAt
  have hc_un : ContinuousOn un (V ×ˢ univ) := by
    rintro ⟨y,i⟩ hy
    have hy' : y ∈ V := hy.1
    have hy'' : y ∈ (e i).target := by
      obtain ⟨a, ha, hay⟩ := mem_iInter.mp hy'.1 i
      rw [← hay, heq i]
      exact (e i).map_source ha.2
    have hc : ContinuousAt (fun b : X × F => (e i).symm b.1) (y,i) :=
      ((e i).symm.continuousAt hy'').comp continuous_fst.continuousAt
    have he : (fun b : X × F => (e i).symm b.1) =ᶠ[𝓝 (y,i)] un := by
      have hsing : {i} ∈ 𝓝 i := (isOpen_discrete {i}).mem_nhds (mem_singleton _)
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hsing] with b hb
      have hb' : b.2 = i := hb
      simp [un, hb']
    exact (hc.congr he).continuousWithinAt
  refine ⟨{
    toFun := fun a => (f a, ind a)
    invFun := un
    source := f ⁻¹' V
    target := V ×ˢ univ
    map_source' := fun a ha => ⟨ha, mem_univ _⟩
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := hV.preimage hf.continuous
    open_target := hV.prod isOpen_univ
    continuousOn_toFun := hf.continuous.continuousOn.prodMk hc_ind
    continuousOn_invFun := hc_un
    baseSet := V
    open_baseSet := hV
    source_eq := rfl
    target_eq := rfl
    proj_toFun := fun _ _ => rfl }, hxV⟩
  · rintro ⟨y,i⟩ hy
    change f (un (y,i)) ∈ V
    rw [(hun y i hy.1).2]
    exact hy.1
  · intro a ha
    have ha' : f a ∈ V := ha
    obtain ⟨i, hi⟩ := hWV ha'
    change un (f a, ind a) = a
    rw [hind a i hi]
    dsimp only [un]
    rw [heq i]
    exact (e i).left_inv hi.2
  · rintro ⟨y,i⟩ hy
    apply Prod.ext
    · exact (hun y i hy.1).2
    · exact hind _ i (hun y i hy.1).1


/-- Properness supplies the finite fibers and closedness needed above. -/
theorem isCoveringMap_of_proper_localHomeomorph
    {E X : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
    (f : E → X) (hf : IsLocalHomeomorph f) (hp : IsProperMap f)
    (hsurj : Function.Surjective f) : IsCoveringMap f := by
  apply isCoveringMap_of_closedMap_finite_localHomeomorph f hf hp.isClosedMap _ hsurj
  intro x
  let S := f ⁻¹' ({x} : Set X)
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (hp.isCompact_preimage isCompact_singleton)
  haveI : DiscreteTopology S := singletons_open_iff_discrete.mp (by
    intro a
    obtain ⟨e, ha, he⟩ := hf a.val
    have heq : (Subtype.val : S → E) ⁻¹' e.source = {a} := by
      ext b
      constructor
      · intro hb
        apply Set.mem_singleton_iff.mpr
        apply Subtype.ext
        apply e.injOn hb ha
        rw [← he]
        exact (show f b.val = x from b.property).trans (show f a.val = x from a.property).symm
      · intro hb
        rw [Set.mem_singleton_iff.mp hb]
        exact ha
    rw [← heq]
    exact e.open_source.preimage continuous_subtype_val)
  letI : Finite S := finite_of_compact_of_discrete
  exact Set.toFinite _

/-- Continuous motion in a connected parameter set cannot leave a finite
strict chamber without first meeting a point with all deficits nonnegative
and at least one zero. -/
theorem all_positive_of_preconnected_no_boundary
    {A β : Type*} [TopologicalSpace A] [PreconnectedSpace A] [Finite β]
    (D : β → A → ℝ) (hD : ∀ i, Continuous (D i))
    (hno : ∀ a, (∀ i, 0 ≤ D i a) → ∀ i, 0 < D i a)
    (a₀ : A) (ha₀ : ∀ i, 0 < D i a₀) :
    ∀ a i, 0 < D i a := by
  let S : Set A := {a | ∀ i, 0 < D i a}
  have hopen : IsOpen S := by
    have heq : S = ⋂ i, {a | 0 < D i a} := by ext a; simp [S]
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hD i)
  have hclosed : IsClosed S := by
    have heq : S = ⋂ i, {a | 0 ≤ D i a} := by
      ext a
      simp only [S, mem_setOf_eq, mem_iInter]
      exact ⟨fun h i => (h i).le, hno a⟩
    rw [heq]
    exact isClosed_iInter fun i => isClosed_le continuous_const (hD i)
  have hu : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨a₀, ha₀⟩
  intro a
  have ha : a ∈ S := by rw [hu]; exact mem_univ _
  exact ha

/-- Lift a base path in the positive-gap slice and keep all existing
strict deficits, provided no new contact is possible on the slice. -/
theorem exists_positive_lift_of_coveringMap
    {E X β : Type*} [TopologicalSpace E] [TopologicalSpace X] [Finite β]
    (f : E → X) (hf : IsCoveringMap f)
    (e : E) (γ : C(I, X)) (hstart : γ 0 = f e)
    (D : β → E → ℝ) (hD : ∀ i, Continuous (D i))
    (he : ∀ i, 0 < D i e)
    (hno : ∀ z, f z ∈ Set.range γ → (∀ i, 0 ≤ D i z) → ∀ i, 0 < D i z) :
    ∃ Γ : C(I, E), f ∘ Γ = γ ∧ Γ 0 = e ∧ ∀ t i, 0 < D i (Γ t) := by
  obtain ⟨Γ, hΓ, hΓ₀⟩ := hf.exists_path_lifts γ e hstart
  refine ⟨Γ, hΓ, hΓ₀, ?_⟩
  refine all_positive_of_preconnected_no_boundary (fun i => D i ∘ Γ)
    (fun i => (hD i).comp Γ.continuous) ?_ 0 ?_
  · intro t ht
    exact hno (Γ t) ⟨t, (congrFun hΓ t).symm⟩ ht
  · simpa only [Function.comp_apply, hΓ₀] using he


/-- A lift of a periodic base map has a positive iterate of the same
period when one fiber is finite. This gives finite monodromy on a logarithm
half-plane without a classification theorem for all punctured-disk covers. -/
theorem exists_positive_iterate_period_of_finite_cover
    {A E X : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [TopologicalSpace E] [TopologicalSpace X]
    (p : E → X) (hp : IsCoveringMap p)
    (g : A → E) (hg : Continuous g)
    (τ : A → A) (hτ : Continuous τ)
    (hper : ∀ a, p (g (τ a)) = p (g a))
    (a₀ : A) (hfin : (p ⁻¹' {p (g a₀)}).Finite) :
    ∃ m : ℕ, 0 < m ∧ ∀ a, g (τ^[m] a) = g a := by
  have hiter (n : ℕ) (a : A) : p (g (τ^[n] a)) = p (g a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', hper, ih]
  obtain ⟨i, j, hij, heq⟩ := hfin.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => g (τ^[n] a₀)) (fun n => hiter n a₀)
  let m := j - i
  have hm : 0 < m := Nat.sub_pos_of_lt hij
  have hji : m + i = j := Nat.sub_add_cancel hij.le
  have hfix : (g ∘ τ^[m]) (τ^[i] a₀) = g (τ^[i] a₀) := by
    change g (τ^[m] (τ^[i] a₀)) = g (τ^[i] a₀)
    rw [← Function.iterate_add_apply, hji]
    exact heq.symm
  have hwhole : g ∘ τ^[m] = g :=
    hp.eq_of_comp_eq (hg.comp (hτ.iterate m)) hg (funext (hiter m)) _ hfix
  exact ⟨m, hm, fun a => congrFun hwhole a⟩

end MOC
