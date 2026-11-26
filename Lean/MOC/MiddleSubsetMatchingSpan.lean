import MOC.MatchingListCoefficients
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! For two equal classes, signed perfect-matching vectors span the kernel of middle
subset incidence. The scalar field can be any field of characteristic zero. -/

open Finset

namespace MOC

variable {α K : Type*} [Fintype α] [DecidableEq α] [Field K]

def middleSubsetMatchingSpan (K : Type*) [Field K] (k : ℕ) (L R : Finset α) :
    Submodule K (SubsetsOfSize α k → K) :=
  Submodule.span K (Set.range fun p : {p // SubsetMatchingList L R p} =>
    fun S : SubsetsOfSize α k => subsetMatchingCoefficient (K := K) p.val S.val)

private def extendSubsetLevel {k : ℕ} (f : SubsetsOfSize α k → K) (S : Finset α) : K :=
  if h : S.card = k then f ⟨S, h⟩ else 0

private theorem down_apply_extension (k : ℕ) (f : SubsetsOfSize α (k + 1) → K)
    (S : SubsetsOfSize α k) :
    subsetIncidenceDown k f S =
      ∑ x ∈ univ \ S.val, extendSubsetLevel f (insert x S.val) := by
  change (∑ x, if h : x ∈ S.val then 0 else f _) = _
  have he : (univ : Finset α) \ S.val = univ.filter (fun x => x ∉ S.val) := by ext x; simp
  rw [he, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ S.val
  · simp [hx]
  · simp [hx, extendSubsetLevel, card_insert_of_not_mem hx, S.property]

private theorem matchingDifference_extendSubsetLevel {k : ℕ} {p : List (α × α)}
    {L R : Finset α} (hp : SubsetMatchingList L R p) (hd : Disjoint L R)
    (hu : L ∪ R = univ) (f : SubsetsOfSize α k → K) :
    subsetMatchingDifference p (extendSubsetLevel f) ∅ =
      ∑ S : SubsetsOfSize α k, subsetMatchingCoefficient p S.val * f S := by
  classical
  rw [hp.difference_sum hd, hu, powerset_univ]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun S : Finset α => S.card = k)
    (fun S => subsetMatchingCoefficient (K := K) p S * extendSubsetLevel f S)]
  simp [extendSubsetLevel]

private def subsetCoordinatePairing {ι : Type*} [Fintype ι]
    (W : Submodule K (ι → K)) : (ι → K) →ₗ[K] Module.Dual K W where
  toFun h :=
    { toFun := fun w => ∑ i, w.val i * h i
      map_add' := fun u v => by simp [add_mul, sum_add_distrib]
      map_smul' := fun c u => by simp [mul_assoc, mul_sum] }
  map_add' f g := by ext w; simp [mul_add, sum_add_distrib]
  map_smul' c f := by ext w; simp [mul_left_comm, mul_sum]

theorem middleSubsetMatchingSpan_eq_ker [CharZero K] {k : ℕ} (L R : Finset α)
    (hl : L.card = k + 1) (hr : R.card = k + 1) (hd : Disjoint L R) (hu : L ∪ R = univ) :
    middleSubsetMatchingSpan K (k + 1) L R = LinearMap.ker (subsetIncidenceDown (K := K) k) := by
  classical
  let W := middleSubsetMatchingSpan K (k + 1) L R
  let H := LinearMap.ker (subsetIncidenceDown (α := α) (K := K) k)
  have hWH : W ≤ H := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply LinearMap.mem_ker.mpr
    ext S
    rw [down_apply_extension]
    have he := p.property.sum_extension_coefficient (K := K) hd S.val
    rw [hu] at he
    calc
      _ = ∑ x ∈ univ \ S.val, subsetMatchingCoefficient (K := K) p.val (insert x S.val) := by
        refine sum_congr rfl fun x hx => ?_
        have hx' := (mem_sdiff.mp hx).2
        simp [extendSubsetLevel, card_insert_of_not_mem hx', S.property]
      _ = 0 := he
  let P := (subsetCoordinatePairing W).comp H.subtype
  have hinj : Function.Injective P := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hvH := LinearMap.mem_ker.mp v.property
    have hh : SubsetHarmonicOn (L ∪ R) (k + 1) (extendSubsetLevel v.val) := by
      intro S _ hS
      have hs : S.card = k := by omega
      rw [hu, ← down_apply_extension k v.val ⟨S, hs⟩]
      exact congrFun hvH ⟨S, hs⟩
    have ht (p : List (α × α)) (hp : SubsetMatchingList L R p) :
        subsetMatchingDifference p (extendSubsetLevel v.val) ∅ = 0 := by
      rw [matchingDifference_extendSubsetLevel hp hd hu]
      let w : W := ⟨fun S => subsetMatchingCoefficient (K := K) p S.val,
        Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩⟩
      exact LinearMap.congr_fun hv w
    apply Subtype.ext
    funext S
    have hz := subsetHarmonic_eq_zero_of_matching_differences (k + 1) L R hl hr hd
      (extendSubsetLevel v.val) hh ht S.val (hu ▸ subset_univ S.val) S.property
    simpa [extendSubsetLevel, S.property] using hz
  have hrank := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Subspace.dual_finrank_eq] at hrank
  exact Submodule.eq_of_le_of_finrank_le hWH hrank

end MOC
