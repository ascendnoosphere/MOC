import MOC.WeightedDiamondCensusPath
import MOC.WeightedDiamondWitnessMasks

/-! A sparse exact certificate for one ray transition. The coefficient checks
cover the listed crossings. Bitset covers certify the other crossings. -/

namespace MOC.RayCoefficients

structure SparseRayCutPlan (m n : ℕ) where
  kept : Fin m → Fin n
  edges : Fin m → List (Fin m × Fin n × Poly)
  origin : Fin n → RayOrigin m
  positiveMask : ℕ
  positiveAt : Fin 24 → ℕ
  witnesses : Fin m → List (Fin m × List (Fin 24))
  zeroCoords : Fin m → List (Fin 24)
  nextPositiveCoord : Fin n → Fin 24

namespace SparseRayCutPlan

variable {m n : ℕ} (d : SparseRayCutPlan m n)

def OriginValid (old : Fin m → Row) (j : Fin 24) (l : Fin n) : RayOrigin m → Prop
  | .kept k => (zero (old k j) = true ∨ positive (old k j) = true) ∧ d.kept k = l
  | .crossing p k => positive (old p j) = true ∧ negative (old k j) = true ∧
      ((d.edges k).lookup p).map Prod.fst = some l

instance (old : Fin m → Row) (j : Fin 24) (l : Fin n) (source : RayOrigin m) :
    Decidable (d.OriginValid old j l source) := by
  cases source <;> unfold OriginValid <;> infer_instance

structure Checked (old : Fin m → Row) (next : Fin n → Row)
    (s : Finset (Fin 24)) (j : Fin 24) : Prop where
  oldSigns : ∀ k i, i ∈ s → zero (old k i) = true ∨ positive (old k i) = true
  nextSigns : ∀ l i, i ∈ s → nonneg (next l i) = true
  nextPositive : ∀ l, d.nextPositiveCoord l ∈ s ∧ positive (next l (d.nextPositiveCoord l)) = true
  cutSigns : ∀ k, zero (old k j) = true ∨ positive (old k j) = true ∨ negative (old k j) = true
  cutPositive_eq : ∀ k : Fin m, d.positiveMask.testBit k.val = positive (old k j)
  positiveAt_eq : ∀ k : Fin m, ∀ i ∈ s, (d.positiveAt i).testBit k.val = positive (old k i)
  zeroCoordsValid : ∀ k i, i ∈ d.zeroCoords k → i ∈ s ∧ zero (old k i) = true
  antichainCover : ∀ k : Fin m,
    let mask := (2 ^ m - 1).ldiff (2 ^ k.val)
    mask &&& unionMasks ((d.zeroCoords k).map d.positiveAt) = mask
  witnessesValid : ∀ k r, r ∈ d.witnesses k → r.1 ≠ k ∧
      ∀ i ∈ s, zero (old k i) = true → positive (old r.1 i) = true → i ∈ r.2
  crossingCover : ∀ k, negative (old k j) = true →
      d.positiveMask &&& unionMasks (((d.edges k).map fun r => 2 ^ r.1.val) ++
        (d.witnesses k).map (witnessMask d.positiveMask d.positiveAt)) = d.positiveMask
  keptValid : ∀ k, zero (old k j) = true ∨ positive (old k j) = true →
      ∀ i, equal (old k i) (next (d.kept k) i) = true
  edgeValid : ∀ k e, e ∈ d.edges k →
      RayCutPlan.CrossingValid old next s j e.1 k (.keep e.2.1 e.2.2)
  originsValid : ∀ l, d.OriginValid old j l (d.origin l)

private noncomputable def rayPlan (old : Fin m → Row) (next : Fin n → Row)
    (s : Finset (Fin 24)) (j : Fin 24) : RayCutPlan m n where
  kept := d.kept
  origin := d.origin
  crossing p k := by
    classical
    exact match (d.edges k).lookup p with
    | some (l, c) => .keep l c
    | none =>
      if h : ∃ q, RayCutPlan.CrossingValid old next s j p k (.skip q)
      then .skip (Classical.choose h)
      else .skip p

private theorem rayPlan_target (old : Fin m → Row) (next : Fin n → Row)
    (s : Finset (Fin 24)) (j : Fin 24) (p k : Fin m) :
    ((d.rayPlan old next s j).crossing p k).target? = ((d.edges k).lookup p).map Prod.fst := by
  cases h : (d.edges k).lookup p with
  | none =>
    simp only [rayPlan, h, Option.map_none]
    split <;> rfl
  | some e => cases e; simp [rayPlan, h, Crossing.target?]

private theorem checked_valid {old : Fin m → Row} {next : Fin n → Row}
    {s : Finset (Fin 24)} {j : Fin 24} (h : d.Checked old next s j) :
    (d.rayPlan old next s j).Valid old next s j := by
  refine ⟨h.oldSigns, h.nextSigns, fun l => ⟨d.nextPositiveCoord l, h.nextPositive l⟩,
    h.cutSigns, separates_of_maskCoverage old s d.positiveAt d.zeroCoords h.positiveAt_eq
      h.zeroCoordsValid h.antichainCover, h.keptValid, ?_, ?_⟩
  · intro p k hp hk
    cases hlookup : (d.edges k).lookup p with
    | some e =>
      obtain ⟨l, c⟩ := e
      have he : (p, l, c) ∈ d.edges k := by
        obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp hlookup
        rw [he]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      simpa only [rayPlan, hlookup] using h.edgeValid k (p, l, c) he
    | none =>
      have hcover (u) (hu : negative (old u j) = true) :
          d.positiveMask &&& unionMasks
            (((d.edges u).map Prod.fst).map (fun p => 2 ^ p.val) ++
              (d.witnesses u).map (witnessMask d.positiveMask d.positiveAt)) =
            d.positiveMask := by
        simpa only [List.map_map, Function.comp_apply] using h.crossingCover u hu
      have hcases := crossing_cover_of_masks old next s j d.positiveMask d.positiveAt
        (fun k => (d.edges k).map Prod.fst) d.witnesses h.cutPositive_eq
        h.positiveAt_eq h.oldSigns h.witnessesValid hcover p k hp hk
      have hw : ∃ q, RayCutPlan.CrossingValid old next s j p k (.skip q) := by
        rcases hcases with he | hw
        · obtain ⟨e, he, heq⟩ := List.mem_map.mp he
          have hs : ((d.edges k).lookup p).isSome := List.lookup_isSome_iff.mpr
            ⟨e, he, beq_iff_eq.mpr heq.symm⟩
          simp [hlookup] at hs
        · exact hw
      simpa only [rayPlan, hlookup, dif_pos hw] using Classical.choose_spec hw
  · intro l
    have horig := h.originsValid l
    change (d.rayPlan old next s j).OriginValid old j l (d.origin l)
    cases hsrc : d.origin l with
    | kept k =>
      simpa only [hsrc, OriginValid, RayCutPlan.OriginValid, rayPlan] using horig
    | crossing p k =>
      simpa only [hsrc, OriginValid, RayCutPlan.OriginValid, rayPlan_target] using horig

/-- A checked sparse cut adds its coordinate inequality to the ray census. -/
theorem checkedCut {old : Fin m → Row} {next : Fin n → Row}
    {s : Finset (Fin 24)} {j : Fin 24} (h : d.Checked old next s j) :
    RayCensusPath ⟨m, old, s⟩ ⟨n, next, insert j s⟩ :=
  .cons (d.rayPlan old next s j) (d.checked_valid h) rfl (.refl _)

end SparseRayCutPlan
end MOC.RayCoefficients
