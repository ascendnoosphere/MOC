import MOC.ContinuousWeightProbes
import Mathlib.Topology.Homotopy.Contractible

/-! An explicit deformation retraction of the union of probe constraints
onto the boundary of the simplex of equations. -/

open BigOperators Finset Filter Set Topology
open scoped unitInterval

namespace MOC.ProbeWitness

noncomputable section

variable {κ : Type*} [Fintype κ] {k : ℕ}

/-- Probability laws satisfying at least one probe equation. -/
abbrev ConstraintUnion (d : ProbeWitness κ k) :=
  {w : κ → ℝ // (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧ ∃ j, d.signedError w j = 0}

/-- Probability vectors on the probes with at least one coordinate zero. -/
abbrev SimplexBoundary (k : ℕ) :=
  {u : Fin (k + 1) → ℝ // (∀ j, 0 ≤ u j) ∧ (∑ j, u j = 1) ∧ ∃ j, u j = 0}

private def positiveError (d : ProbeWitness κ k) (w : d.ConstraintUnion)
    (j : Fin (k + 1)) : ℝ :=
  max (d.signedError w.val j) 0

private theorem sum_positiveError_pos (d : ProbeWitness κ k) (w : d.ConstraintUnion) :
    0 < ∑ j, d.positiveError w j := by
  apply d.gap_pos.trans_le
  exact (d.sum_signedError_ge w.val w.property.1).trans
    (sum_le_sum fun j _ => le_max_left _ _)

private theorem continuous_signedError (d : ProbeWitness κ k) (j : Fin (k + 1)) :
    Continuous (fun w : κ → ℝ => d.signedError w j) := by
  induction j using Fin.cases with
  | zero =>
    simp only [signedError, Fin.cases_zero, expectation]
    fun_prop
  | succ j =>
    simp only [signedError, Fin.cases_succ, expectation]
    fun_prop

private theorem continuous_positiveError (d : ProbeWitness κ k) (j : Fin (k + 1)) :
    Continuous (fun w => d.positiveError w j) :=
  ((d.continuous_signedError j).comp continuous_subtype_val).max continuous_const

/-- Keep only positive signed errors, then normalize their sum. -/
def projectToBoundary (d : ProbeWitness κ k) : C(d.ConstraintUnion, SimplexBoundary k) where
  toFun w := by
    refine ⟨fun j => d.positiveError w j / (∑ l, d.positiveError w l), ?_, ?_, ?_⟩
    · intro j
      exact div_nonneg (le_max_right _ _) (d.sum_positiveError_pos w).le
    · rw [← sum_div, div_self (d.sum_positiveError_pos w).ne']
    · obtain ⟨j, hj⟩ := w.property.2.2
      exact ⟨j, by simp [positiveError, hj]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (d.continuous_positiveError j).div
      (continuous_finset_sum _ fun l _ => d.continuous_positiveError l)
      (fun w => (d.sum_positiveError_pos w).ne')

/-- A boundary vector gives a law on the selected permutations. -/
def boundaryToLaw (d : ProbeWitness κ k) : C(SimplexBoundary k, d.ConstraintUnion) where
  toFun u := by
    refine ⟨d.law u.val, d.law_nonneg _ u.property.1, d.law_sum _ u.property.2.1, ?_⟩
    obtain ⟨j, hj⟩ := u.property.2.2
    exact ⟨j, by rw [d.signedError_law _ u.property.2.1, hj, mul_zero]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro p
    unfold law
    apply continuous_finset_sum
    intro a _
    split_ifs
    · unfold mass
      induction a using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero]
        fun_prop
      | succ a =>
        simp only [Fin.cases_succ]
        fun_prop
    · exact continuous_const

theorem project_boundaryToLaw (d : ProbeWitness κ k) (u : SimplexBoundary k) :
    d.projectToBoundary (d.boundaryToLaw u) = u := by
  have he (j : Fin (k + 1)) :
      d.positiveError (d.boundaryToLaw u) j = d.gap * u.val j := by
    unfold positiveError
    change max (d.signedError (d.law u.val) j) 0 = _
    rw [d.signedError_law _ u.property.2.1,
      max_eq_left (mul_nonneg d.gap_pos.le (u.property.1 j))]
  have hs : (∑ l, d.positiveError (d.boundaryToLaw u) l) = d.gap := by
    simp_rw [he, ← mul_sum, u.property.2.1, mul_one]
  apply Subtype.ext
  funext j
  change d.positiveError (d.boundaryToLaw u) j /
    (∑ l, d.positiveError (d.boundaryToLaw u) l) = u.val j
  rw [he, hs]
  apply (div_eq_iff d.gap_pos.ne').mpr
  exact mul_comm _ _

private theorem solved_coordinate_retract (d : ProbeWitness κ k)
    (w : d.ConstraintUnion) (j : Fin (k + 1)) (hj : d.signedError w.val j = 0) :
    d.signedError (d.boundaryToLaw (d.projectToBoundary w)).val j = 0 := by
  have hz : (d.projectToBoundary w).val j = 0 := by
    change d.positiveError w j / _ = 0
    simp [positiveError, hj]
  change d.signedError (d.law (d.projectToBoundary w).val) j = 0
  rw [d.signedError_law _ (d.projectToBoundary w).property.2.1, hz, mul_zero]

private theorem signedError_eq_zero_iff (d : ProbeWitness κ k)
    (w : κ → ℝ) (j : Fin (k + 1)) :
    d.signedError w j = 0 ↔ d.expectation w j = d.target j := by
  induction j using Fin.cases with
  | zero => simp only [signedError, Fin.cases_zero, sub_eq_zero, eq_comm]
  | succ j => simp only [signedError, Fin.cases_succ, sub_eq_zero]

private def interpolation (d : ProbeWitness κ k) (t : I) (w : d.ConstraintUnion) :
    d.ConstraintUnion := by
  let v := d.boundaryToLaw (d.projectToBoundary w)
  let f : κ → ℝ := fun p => (t : ℝ) * w.val p + (1 - (t : ℝ)) * v.val p
  refine ⟨f, ?_, ?_, ?_⟩
  · intro p
    exact add_nonneg (mul_nonneg t.property.1 (w.property.1 p))
      (mul_nonneg (sub_nonneg.mpr t.property.2) (v.property.1 p))
  · simp only [f, sum_add_distrib, ← mul_sum, w.property.2.1, v.property.2.1, mul_one]
    ring
  · obtain ⟨j, hj⟩ := w.property.2.2
    have hv := (d.signedError_eq_zero_iff _ _).mp (d.solved_coordinate_retract w j hj)
    have hw := (d.signedError_eq_zero_iff _ _).mp hj
    refine ⟨j, (d.signedError_eq_zero_iff _ _).mpr ?_⟩
    calc
      d.expectation f j = (t : ℝ) * d.expectation w.val j +
          (1 - (t : ℝ)) * d.expectation v.val j := by
        simp only [expectation, f, add_mul, sum_add_distrib, mul_assoc, mul_sum]
      _ = _ := by rw [hw, hv]; ring

/-- The straight-line homotopy stays within every constraint already
satisfied at its starting law. -/
def constraintUnion_homotopy (d : ProbeWitness κ k) :
    ContinuousMap.Homotopy (d.boundaryToLaw.comp d.projectToBoundary)
      (ContinuousMap.id _) where
  toFun tw := d.interpolation tw.1 tw.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro p
    change Continuous (fun tw : I × d.ConstraintUnion =>
      (tw.1 : ℝ) * tw.2.val p + (1 - (tw.1 : ℝ)) *
        (d.boundaryToLaw (d.projectToBoundary tw.2)).val p)
    fun_prop
  map_zero_left w := by
    apply Subtype.ext
    funext p
    simp [interpolation]
  map_one_left w := by
    apply Subtype.ext
    funext p
    simp [interpolation]

/-- For either finite fixture, the union of the exact constraints has the
homotopy type of the indicated simplex boundary. -/
def constraintUnion_homotopyEquiv (d : ProbeWitness κ k) :
    ContinuousMap.HomotopyEquiv d.ConstraintUnion (SimplexBoundary k) where
  toFun := d.projectToBoundary
  invFun := d.boundaryToLaw
  left_inv := ⟨d.constraintUnion_homotopy⟩
  right_inv := by
    have he : d.projectToBoundary.comp d.boundaryToLaw = ContinuousMap.id _ := by
      ext u
      exact d.project_boundaryToLaw u
    rw [he]
    exact ContinuousMap.Homotopic.refl _

/- For positive k, radial projection from the barycenter identifies this
boundary with the unit sphere in the hyperplane of vectors of sum zero.
The inverse extends each ray until its first coordinate reaches zero.
The usual reduced integral homology and cohomology of a sphere give
degree three for the five probes and degree four for the six probes.
This last homology calculation is outside the formalization. -/

/-- Unit intervals embedded along the coordinate axes, with their zero
endpoints identified. -/
abbrev Star (m : ℕ) :=
  {x : Fin m → ℝ // (∀ j, x j ∈ Icc 0 1) ∧
    ∀ i j, i ≠ j → x i = 0 ∨ x j = 0}

def starCenter (m : ℕ) : Star m :=
  ⟨0, fun _ => ⟨le_rfl, zero_le_one⟩, fun _ _ _ => Or.inl rfl⟩

def starBranch {m : ℕ} (j : Fin m) : C(I, Star m) where
  toFun t := by
    let x : Fin m → ℝ := fun l => if l = j then (t : ℝ) else 0
    refine ⟨x, ?_, ?_⟩
    · intro l
      by_cases h : l = j
      · simpa [x, h] using t.property
      · simp [x, h]
    · intro i l hil
      by_cases hi : i = j
      · have hl : l ≠ j := fun h => hil (hi.trans h.symm)
        exact Or.inr (by simp [x, hl])
      · exact Or.inl (by simp [x, hi])
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro l
    by_cases h : l = j
    · simpa [h] using (continuous_subtype_val : Continuous (fun t : I => (t : ℝ)))
    · simp [h]

theorem starBranch_zero {m : ℕ} (j : Fin m) :
    starBranch j 0 = starCenter m := by
  apply Subtype.ext
  funext l
  by_cases h : l = j <;> simp [starBranch, starCenter, h]

private def contractStar {m : ℕ} (t : I) (x : Star m) : Star m := by
  refine ⟨fun j => (1 - (t : ℝ)) * x.val j, ?_, ?_⟩
  · intro j
    refine ⟨mul_nonneg (sub_nonneg.mpr t.property.2) (x.property.1 j).1, ?_⟩
    calc
      _ ≤ 1 * x.val j := mul_le_mul_of_nonneg_right (by linarith [t.property.1])
        (x.property.1 j).1
      _ ≤ 1 := by simpa using (x.property.1 j).2
  · intro i j hij
    rcases x.property.2 i j hij with hi | hj
    · exact Or.inl (by rw [hi, mul_zero])
    · exact Or.inr (by rw [hj, mul_zero])

theorem star_contractible (m : ℕ) : ContractibleSpace (Star m) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨starCenter m, ⟨?_⟩⟩
  refine ⟨⟨fun tx => contractStar tx.1 tx.2, ?_⟩, ?_, ?_⟩
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    change Continuous (fun tx : I × Star m =>
      (1 - (tx.1 : ℝ)) * tx.2.val j)
    fun_prop
  · intro x
    apply Subtype.ext
    funext j
    simp [contractStar]
  · intro x
    apply Subtype.ext
    funext j
    simp [contractStar, starCenter]

/- In the algebra of continuous matrix fields, a central field commutes
with every constant matrix unit. Its values are therefore scalar
matrices. Any diagonal coordinate gives the continuous scalar function.
The formal branch statements use these scalar functions directly. -/

/-- Along every branch the normalized event errors have continuous limits,
and on at least one branch the limiting error is at least the sharp gap. -/
theorem some_branch_limiting_error_ge (d : ProbeWitness κ k)
    (w : C(Star (k + 1), κ → ℝ))
    (hw : ∀ p, 0 ≤ w (starCenter (k + 1)) p)
    (hs : ∑ p, w (starCenter (k + 1)) p = 1) :
    ∃ j : Fin (k + 1), ∃ limit : ℝ, d.gap / (k + 1) ≤ limit ∧
      Tendsto (fun t : I => |d.expectation (w (starBranch j t)) j - d.target j|)
        (𝓝 0) (𝓝 limit) := by
  let error (j : Fin (k + 1)) := |d.expectation (w (starCenter (k + 1))) j - d.target j|
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image
    (univ : Finset (Fin (k + 1))) error ⟨0, mem_univ _⟩
  have hl : d.gap / (k + 1) ≤ error j :=
    (d.error_iff _).mp ⟨w (starCenter (k + 1)), hw, hs, fun l => hj l (mem_univ _)⟩
  let f (t : I) : ℝ := |d.expectation (w (starBranch j t)) j - d.target j|
  refine ⟨j, error j, hl, ?_⟩
  have hfc : Continuous f := by
    unfold f expectation
    fun_prop
  have hv : f 0 = error j := by simp only [f, error, starBranch_zero]
  rw [← hv]
  exact hfc.continuousAt

/-- A continuous law on the star cannot represent all of the normalized
branch data. -/
theorem no_continuous_star_weights (d : ProbeWitness κ k) :
    ¬ ∃ w : C(Star (k + 1), κ → ℝ),
      (∀ p, 0 ≤ w (starCenter (k + 1)) p) ∧
      (∑ p, w (starCenter (k + 1)) p = 1) ∧
      ∀ (j : Fin (k + 1)) (t : I), 0 < (t : ℝ) →
        d.expectation (w (starBranch j t)) j = d.target j := by
  rintro ⟨w, hw, hs, h⟩
  obtain ⟨j, limit, hlim, ht⟩ := d.some_branch_limiting_error_ge w hw hs
  have hmap : Tendsto (fun t : ℝ =>
      (⟨max 0 (min t 1), le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩ : I))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ =>
        (⟨max 0 (min t 1), le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩ : I)) := by
      exact ((continuous_id.min continuous_const).const_max 0).subtype_mk _
    have h0 : (⟨max 0 (min (0 : ℝ) 1), le_max_left _ _,
        max_le zero_le_one (min_le_right _ _)⟩ : I) = 0 := by
      apply Subtype.ext
      norm_num
    rw [← h0]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : limit = 0 := by
    apply tendsto_nhds_unique_of_eventuallyEq (ht.comp hmap) tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t hp
    simp only [Function.comp_apply]
    rw [h j _ (lt_max_iff.mpr (Or.inr (lt_min hp.1 zero_lt_one))), sub_self, abs_zero]
  have hpos : 0 < d.gap / (k + 1) := div_pos d.gap_pos (by positivity)
  rw [hz] at hlim
  exact hpos.not_le hlim

end

end MOC.ProbeWitness

namespace MOC.ContinuousWeightProbes

open Matrix ProbeWitness ContinuousWeightCounterexample

noncomputable section

variable {n : ℕ}

def scaledProbeDifference (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (w : Equiv.Perm (Fin n) → ℝ) : ℂ :=
  (∑ p, (w p : ℂ) * matchingProduct (fun j => (t : ℂ) * a j)
    (fun j => (t : ℂ) * b j) p.symm) -
    determinantValue (fun j => (t : ℂ) * a j) (fun j => (t : ℂ) * b j) U

private theorem normalized_scaledProbeDifference
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (ht : 0 < t) (w : Equiv.Perm (Fin n) → ℝ) :
    ‖scaledProbeDifference a b U t w‖ / t ^ n =
      ‖(∑ p, (w p : ℂ) * matchingProduct a b p.symm) - determinantValue a b U‖ := by
  have h : scaledProbeDifference a b U t w =
      (t : ℂ)^n * ((∑ p, (w p : ℂ) * matchingProduct a b p.symm) -
        determinantValue a b U) := by
    unfold scaledProbeDifference
    rw [determinantValue_scale, mul_sub, Finset.mul_sum, Fintype.card_fin]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [matchingProduct_scale, Fintype.card_fin, mul_left_comm]
  rw [h, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  field_simp [pow_ne_zero n ht.ne']

def probeLeft (I : Finset (Fin n)) (i : Fin n) : ℂ := if i ∈ I then 0 else 1

def probeRight (J : Finset (Fin n)) (j : Fin n) : ℂ := if j ∈ J then 1 else 0

/-- On the order-four branches, dividing the physical determinant error
by the fourth power of the branch coordinate gives the probe error. -/
theorem four_probe_normalized_error (j : Fin 5) (t : ℝ) (ht : 0 < t)
    (w : Equiv.Perm (Fin 4) → ℝ) :
    ‖scaledProbeDifference (probeLeft (pairRows j)) (probeRight (pairCols j)) mixer t w‖ /
      t ^ 4 = |fourProbes.expectation w j - fourProbes.target j| := by
  obtain ⟨hd, hv⟩ := four_probe_physical j
  rw [normalized_scaledProbeDifference _ _ _ _ ht]
  change ‖(∑ p, (w p : ℂ) * matchingProduct
      (fun i => if i ∈ pairRows j then 0 else 1)
      (fun i => if i ∈ pairCols j then 1 else 0) p.symm) -
        determinantValue (fun i => if i ∈ pairRows j then 0 else 1)
          (fun i => if i ∈ pairCols j then 1 else 0) mixer‖ = _
  simp only [hd, hv, ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ProbeWitness.expectation]

/-- The complemented order-five equation has exactly the same absolute
physical error as the original singleton equation. -/
theorem five_probe_normalized_error (j : Fin 6) (t : ℝ) (ht : 0 < t)
    (w : Equiv.Perm (Fin 5) → ℝ) (hw : ∑ p, w p = 1) :
    ‖scaledProbeDifference (probeLeft (fiveProbeRows j)) (probeRight (fiveProbeCols j))
        fiveMixer t w‖ / t ^ 5 = |fiveProbes.expectation w j - fiveProbes.target j| := by
  obtain ⟨hd, hv⟩ := five_probe_physical j
  rw [normalized_scaledProbeDifference _ _ _ _ ht]
  change ‖(∑ p, (w p : ℂ) * matchingProduct
      (fun i => if i ∈ fiveProbeRows j then 0 else 1)
      (fun i => if i ∈ fiveProbeCols j then 1 else 0) p.symm) -
        determinantValue (fun i => if i ∈ fiveProbeRows j then 0 else 1)
          (fun i => if i ∈ fiveProbeCols j then 1 else 0) fiveMixer‖ = _
  by_cases h : j.val < 5
  · simp only [hd, hv, if_pos h, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ProbeWitness.expectation]
  · have hm : fiveProbes.target j = 0 := by simp [fiveProbes, fiveTarget, h]
    simp only [hd, hv, if_neg h, mul_sub, mul_one, sum_sub_distrib,
      ← Complex.ofReal_mul, ← Complex.ofReal_sum, hw, Complex.ofReal_one, hm, sub_zero]
    rw [sub_right_comm, sub_self, zero_sub, norm_neg]
    simp only [Complex.norm_real, Real.norm_eq_abs, ProbeWitness.expectation]

def starSpectrum {m : ℕ} (s : Fin m → Fin n → ℂ) (x : Star m) (i : Fin n) : ℂ :=
  ∑ j, (x.val j : ℂ) * s j i

theorem starSpectrum_continuous {m : ℕ} (s : Fin m → Fin n → ℂ) :
    Continuous (starSpectrum s) := by
  apply continuous_pi
  intro i
  unfold starSpectrum
  fun_prop

theorem starSpectrum_branch {m : ℕ} (s : Fin m → Fin n → ℂ) (j : Fin m) (t : I) :
    starSpectrum s (starBranch j t) = fun i => (t : ℝ) * s j i := by
  funext i
  unfold starSpectrum
  rw [Finset.sum_eq_single j]
  · simp [starBranch]
  · intro l _ hl
    simp [starBranch, hl]
  · simp

/-- The order-four physical determinant field has no continuous exact law. -/
theorem no_continuous_four_probe_determinants :
    ¬ ∃ w : C(Star 5, Equiv.Perm (Fin 4) → ℝ),
      (∀ x p, 0 ≤ w x p) ∧ (∀ x, ∑ p, w x p = 1) ∧
      ∀ (j : Fin 5) (t : I), 0 < (t : ℝ) →
        scaledProbeDifference (probeLeft (pairRows j)) (probeRight (pairCols j))
          mixer t (w (starBranch j t)) = 0 := by
  rintro ⟨w, hw, hs, he⟩
  apply fourProbes.no_continuous_star_weights
  refine ⟨w, hw _, hs _, fun j t ht => ?_⟩
  have h := four_probe_normalized_error j t ht (w (starBranch j t))
  rw [he j t ht, norm_zero, zero_div, eq_comm, abs_eq_zero] at h
  exact sub_eq_zero.mp h

/-- The order-five physical determinant field has no continuous exact law. -/
theorem no_continuous_five_probe_determinants :
    ¬ ∃ w : C(Star 6, Equiv.Perm (Fin 5) → ℝ),
      (∀ x p, 0 ≤ w x p) ∧ (∀ x, ∑ p, w x p = 1) ∧
      ∀ (j : Fin 6) (t : I), 0 < (t : ℝ) →
        scaledProbeDifference (probeLeft (fiveProbeRows j)) (probeRight (fiveProbeCols j))
          fiveMixer t (w (starBranch j t)) = 0 := by
  rintro ⟨w, hw, hs, he⟩
  apply fiveProbes.no_continuous_star_weights
  refine ⟨w, hw _, hs _, fun j t ht => ?_⟩
  have h := five_probe_normalized_error j t ht (w (starBranch j t)) (hs _)
  rw [he j t ht, norm_zero, zero_div, eq_comm, abs_eq_zero] at h
  exact sub_eq_zero.mp h

end

end MOC.ContinuousWeightProbes
