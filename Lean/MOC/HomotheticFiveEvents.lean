import MOC.HomotheticFiveData

/-! The polynomial slack on each of the 52 faces is a nonnegative sum
of subset-image indicators. The finite test uses all 120 permutations. -/

open BigOperators Matrix MOC.RayCoefficients

namespace MOC.HomotheticFive

def sumPoly : (n : ℕ) → (Fin n → Poly) → Poly
  | 0, _ => []
  | n+1, v => add (v 0) (sumPoly n (fun i => v i.succ))

theorem eval_sumPoly (s : ℝ) (n : ℕ) (v : Fin n → Poly) :
    eval s (sumPoly n v) = ∑ e, eval s (v e) := by
  induction n with
  | zero => simp [sumPoly, eval]
  | succ n ih => rw [sumPoly, eval_add, ih, Fin.sum_univ_succ]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem event_check (f : Facet) : ∀ p : Label,
    equal (slack f p) (sumPoly 46 fun e =>
      if (eventSets f e).2.map (FivePermutations.perm p).toEmbedding = (eventSets f e).1
      then weight f e else []) = true := by
  have h : ∀ p : Label, equal (slack f p) (sumPoly 46 fun e =>
      if FiveSubsetEvents.imageAt p (eventIndex f e).2 = (eventIndex f e).1
      then weight f e else []) = true := by
    fin_cases f <;> decide +kernel
  simpa only [eventSets, FiveSubsetEvents.image_iff] using h

end MOC.HomotheticFive
