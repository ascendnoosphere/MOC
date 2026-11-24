import MOC.Reformulations.NativeFirstB

/-! Determinant lines and positive finite spectral torsion (085, 090, 093–098).
The chosen finite degree operators are actual matrices. A product of complex
hulls (including inverse factors) is not declared to be a single convex hull. -/

open BigOperators Matrix

namespace MOC.Reformulations.NativeFirstB

noncomputable section

abbrev MatchHull {n : ℕ} (a b : Fin n → ℂ) : Set ℂ :=
  convexHull ℝ (Set.range (matchingProduct a b))

/-- The alternating determinant product. Choosing the sign convention is
separate from the assertion that maps come from any given geometric complex. -/
def alternatingProduct {K : Type*} [Fintype K] (inverse : K → Bool) (z : K → ℂ) : ℂ :=
  ∏ k, if inverse k then (z k)⁻¹ else z k

/-- The natural product image of the degreewise hulls with the required
nonvanishing of inverse factors. -/
def determinantLineHull {K : Type*} [Fintype K] (inverse : K → Bool)
    (hulls : K → Set ℂ) : Set ℂ :=
  {v | ∃ z : K → ℂ, (∀ k, z k ∈ hulls k) ∧
    (∀ k, inverse k = true → z k ≠ 0) ∧ v = alternatingProduct inverse z}

/-- 085 and 094: actual graded normal-operator determinants lie in the
product image under MOC, with the odd-degree denominator restriction. -/
theorem gradedOperatorDeterminantLine_of_moc (h : MOCIsTrue) {K : Type*} [Fintype K]
    (n : K → ℕ) (inverse : K → Bool) (A B U : ∀ k, Mat (n k))
    (a b : ∀ k, Fin (n k) → ℂ)
    (hA : ∀ k, IsStarNormal (A k)) (hB : ∀ k, IsStarNormal (B k))
    (hU : ∀ k, IsUnitary (U k)) (ha : ∀ k, HasRoots (A k) (a k))
    (hb : ∀ k, HasRoots (B k) (b k))
    (hn : ∀ k, inverse k = true → (A k + U k * B k * (U k)ᴴ).det ≠ 0) :
    alternatingProduct inverse (fun k => (A k + U k * B k * (U k)ᴴ).det) ∈
      determinantLineHull inverse (fun k => MatchHull (a k) (b k)) :=
  ⟨_, fun k => operatorHull_of_moc h _ _ _ _ _ (hA k) (hB k) (hU k) (ha k) (hb k), hn, rfl⟩

/-- 093: the Berezinian of two graded blocks, under the two actual block
hull comparisons. The odd-block nonvanishing condition is necessary. -/
theorem berezinian_mem_quotient_hulls {m n : ℕ}
    {A₀ B₀ U₀ : Mat m} {A₁ B₁ U₁ : Mat n}
    {a₀ b₀ : Fin m → ℂ} {a₁ b₁ : Fin n → ℂ}
    (h₀ : OperatorHull A₀ B₀ U₀ a₀ b₀) (h₁ : OperatorHull A₁ B₁ U₁ a₁ b₁)
    (hne : (A₁ + U₁ * B₁ * U₁ᴴ).det ≠ 0) :
    (A₀ + U₀ * B₀ * U₀ᴴ).det / (A₁ + U₁ * B₁ * U₁ᴴ).det ∈
      {v | ∃ z₀ ∈ MatchHull a₀ b₀, ∃ z₁ ∈ MatchHull a₁ b₁, z₁ ≠ 0 ∧ v = z₀ / z₁} :=
  ⟨_, h₀, _, h₁, hne, rfl⟩

/-- 095: the product of actual determinants of the combined basis changes.
The statement concerns the factors; to be a torsion invariant, the
changes must in addition be adapted to an acyclic based complex. -/
theorem reidemeisterFactor_mem_product {K : Type*} [Fintype K] (n : K → ℕ)
    (inverse : K → Bool) (A B U : ∀ k, Mat (n k)) (a b : ∀ k, Fin (n k) → ℂ)
    (hh : ∀ k, OperatorHull (A k) (B k) (U k) (a k) (b k))
    (hn : ∀ k, (A k + U k * B k * (U k)ᴴ).det ≠ 0) :
    alternatingProduct inverse (fun k => (A k + U k * B k * (U k)ᴴ).det) ∈
      {v | ∃ z : K → ℂ, (∀ k, z k ∈ MatchHull (a k) (b k) ∧ z k ≠ 0) ∧
        v = alternatingProduct inverse z} :=
  ⟨_, fun k => ⟨hh k, hn k⟩, rfl⟩

/-- The signed interval argument underlying the finite torsion formula.
The coefficients can in particular be the Ray–Singer degree weights. -/
theorem weightedIntervalBounds {K : Type*} [Fintype K] (c l h x : K → ℝ)
    (hl : ∀ k, l k ≤ x k) (hx : ∀ k, x k ≤ h k) :
    (∑ k, min (c k * l k) (c k * h k)) ≤ ∑ k, c k * x k ∧
    (∑ k, c k * x k) ≤ ∑ k, max (c k * l k) (c k * h k) := by
  constructor <;> apply Finset.sum_le_sum <;> intro k _
  · by_cases hc : 0 ≤ c k
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (hl k) hc)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left (hx k) (le_of_not_ge hc))
  · by_cases hc : 0 ≤ c k
    · exact (mul_le_mul_of_nonneg_left (hx k) hc).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left (hl k) (le_of_not_ge hc)).trans (le_max_left _ _)

/-- 096 and the finite matrix case of 097: signed bounds for the actual
positive finite spectral log-determinants.  Each pair of bounds is
witnessed by matching products. No regularized limit is asserted. -/
theorem finiteSpectralTorsion_bounds {K : Type*} [Fintype K] (n : K → ℕ) (c : K → ℝ)
    (a b : ∀ k, Fin (n k) → ℝ) (ha : ∀ k j, 0 < a k j) (hb : ∀ k j, 0 < b k j)
    (U : ∀ k, Mat (n k)) (hU : ∀ k, IsUnitary (U k)) :
    let d k := (determinantValue (fun j => (a k j : ℂ)) (fun j => (b k j : ℂ)) (U k)).re
    let score k (σ : Equiv.Perm (Fin (n k))) := ∑ j, Real.log (a k (σ j) + b k j)
    (∀ k, 0 < d k) ∧ ∃ lo hi : ∀ k, Equiv.Perm (Fin (n k)),
      (∑ k, min (c k * score k (lo k)) (c k * score k (hi k))) ≤
        ∑ k, c k * Real.log (d k) ∧
      (∑ k, c k * Real.log (d k)) ≤
        ∑ k, max (c k * score k (lo k)) (c k * score k (hi k)) := by
  dsimp only
  have hs k := positiveRealSpectra_log_bounds (a k) (b k) (ha k) (hb k) (U k) (hU k)
  refine ⟨fun k => (hs k).1, ?_⟩
  choose lo hi hlo hhi using fun k => (hs k).2
  exact ⟨lo, hi, weightedIntervalBounds c _ _ _ hlo hhi⟩

/-- 098: the degreewise trace of the sum does not change under unitary
mixing, independently of any conjecture. Summing this identity with
alternating signs gives the corresponding graded trace. -/
theorem lefschetzTrace_unitary {n : ℕ} (A B U : Mat n) (hU : IsUnitary U) :
    (A + U * B * Uᴴ).trace = A.trace + B.trace := by
  rw [Matrix.trace_add, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU.2, Matrix.one_mul]

/-!
090 and 097 in a general finite von Neumann algebra additionally need its
trace and spectral coupling laws. Finite matrix determinant/log factors
do not prove those analytic couplings. 098 does not identify an arbitrary
conjugated sum of actions with a map of spaces, so the graded trace formula
does not by itself produce a topological Lefschetz number.
-/

end

end MOC.Reformulations.NativeFirstB
