import MOC.ContinuousWeightCounterexample
import MOC.FiniteMinorLaw

/-! Exact projection probes in orders four and five. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

/-- A list of probe equations with a pointwise cover inequality and actual
permutations for the zero and two-event columns. -/
structure ProbeWitness (κ : Type*) (k : ℕ) where
  event : κ → Fin (k + 1) → ℝ
  target : Fin (k + 1) → ℝ
  sample : Fin (k + 1) → κ
  cover : ∀ p, event p 0 ≤ ∑ j : Fin k, event p j.succ
  sample_event : ∀ a j, event (sample a) j =
    if a = 0 then 0 else if j = 0 ∨ a = j then 1 else 0
  target_nonneg : ∀ j, 0 ≤ target j
  target_zero_le_one : target 0 ≤ 1
  gap_pos : 0 < target 0 - ∑ j : Fin k, target j.succ

namespace ProbeWitness

variable {κ : Type*} [Fintype κ] {k : ℕ}

def gap (d : ProbeWitness κ k) : ℝ :=
  d.target 0 - ∑ j : Fin k, d.target j.succ

def expectation (d : ProbeWitness κ k) (w : κ → ℝ) (j : Fin (k + 1)) : ℝ :=
  ∑ p, w p * d.event p j

def signedError (d : ProbeWitness κ k) (w : κ → ℝ) : Fin (k + 1) → ℝ :=
  Fin.cases (d.target 0 - d.expectation w 0)
    (fun j => d.expectation w j.succ - d.target j.succ)

theorem sum_signedError_ge (d : ProbeWitness κ k) (w : κ → ℝ)
    (hw : ∀ p, 0 ≤ w p) : d.gap ≤ ∑ j, d.signedError w j := by
  have hc : d.expectation w 0 ≤ ∑ j : Fin k, d.expectation w j.succ := calc
    _ ≤ ∑ p, w p * ∑ j : Fin k, d.event p j.succ :=
      sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (d.cover p) (hw p)
    _ = _ := by
      simp only [expectation, mul_sum]
      exact sum_comm
  rw [Fin.sum_univ_succ]
  simp only [signedError, Fin.cases_zero, Fin.cases_succ, sum_sub_distrib]
  unfold gap
  linarith

private def mass (d : ProbeWitness κ k) (u : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ :=
  Fin.cases (1 - d.target 0 + d.gap * u 0)
    (fun j => d.target j.succ + d.gap * u j.succ)

open Classical in
/-- A probability law obtained from the selected permutations. -/
def law (d : ProbeWitness κ k) (u : Fin (k + 1) → ℝ) : κ → ℝ :=
  fun p => ∑ a, if d.sample a = p then d.mass u a else 0

theorem law_nonneg (d : ProbeWitness κ k) (u : Fin (k + 1) → ℝ)
    (hu : ∀ j, 0 ≤ u j) (p : κ) : 0 ≤ d.law u p := by
  classical
  unfold law
  apply sum_nonneg
  intro a _
  split_ifs with h
  · have hg : 0 ≤ d.gap := d.gap_pos.le
    refine Fin.cases ?_ (fun j => ?_) a
    · exact add_nonneg (sub_nonneg.mpr d.target_zero_le_one) (mul_nonneg hg (hu 0))
    · exact add_nonneg (d.target_nonneg j.succ) (mul_nonneg hg (hu j.succ))
  · exact le_rfl

theorem law_sum (d : ProbeWitness κ k) (u : Fin (k + 1) → ℝ)
    (hu : ∑ j, u j = 1) : ∑ p, d.law u p = 1 := by
  classical
  unfold law
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, if_true]
  rw [Fin.sum_univ_succ] at hu ⊢
  simp only [mass, Fin.cases_zero, Fin.cases_succ, sum_add_distrib, ← mul_sum]
  unfold gap
  linear_combination (d.target 0 - (∑ j : Fin k, d.target j.succ)) * hu

private theorem expectation_law (d : ProbeWitness κ k) (u : Fin (k + 1) → ℝ)
    (j : Fin (k + 1)) : d.expectation (d.law u) j =
      ∑ a, d.mass u a * d.event (d.sample a) j := by
  classical
  unfold expectation law
  simp only [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, if_true]

theorem signedError_law (d : ProbeWitness κ k) (u : Fin (k + 1) → ℝ)
    (hu : ∑ j, u j = 1) (j : Fin (k + 1)) :
    d.signedError (d.law u) j = d.gap * u j := by
  classical
  induction j using Fin.cases with
  | zero =>
    simp only [signedError, Fin.cases_zero, expectation_law, Fin.sum_univ_succ,
      d.sample_event, if_true, mul_zero, zero_add, Fin.succ_ne_zero,
      true_or, mul_one, mass, Fin.cases_succ, sum_add_distrib, ← mul_sum]
    rw [Fin.sum_univ_succ] at hu
    unfold gap
    linear_combination -(d.target 0 - (∑ q : Fin k, d.target q.succ)) * hu
  | succ j =>
    simp only [signedError, Fin.cases_succ, expectation_law, Fin.sum_univ_succ,
      d.sample_event, if_true, mul_zero, zero_add, Fin.succ_ne_zero,
      false_or, Fin.succ_inj, mul_ite, mul_one,
      sum_ite_eq', mem_univ, mass, Fin.cases_succ]
    ring

theorem abs_signedError (d : ProbeWitness κ k) (w : κ → ℝ) (j : Fin (k + 1)) :
    |d.signedError w j| = |d.expectation w j - d.target j| := by
  induction j using Fin.cases with
  | zero => exact abs_sub_comm _ _
  | succ j => rfl

/-- A uniform error bound is possible precisely when it is at least the
cover gap divided by the number of probe equations. -/
theorem error_iff (d : ProbeWitness κ k) (e : ℝ) :
    (∃ w : κ → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      ∀ j, |d.expectation w j - d.target j| ≤ e) ↔
      d.gap / (k + 1) ≤ e := by
  constructor
  · rintro ⟨w, hw, -, he⟩
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k + 1)).mpr
    calc
      _ ≤ ∑ j, d.signedError w j := d.sum_signedError_ge w hw
      _ ≤ ∑ _ : Fin (k + 1), e :=
        sum_le_sum fun j _ => (le_abs_self _).trans (d.abs_signedError w j ▸ he j)
      _ = _ := by simp [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  · intro he
    let u : Fin (k + 1) → ℝ := fun _ => 1 / (k + 1)
    have hu (j) : 0 ≤ u j := by dsimp [u]; positivity
    have hs : ∑ j, u j = 1 := by
      simp only [u, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      field_simp
    refine ⟨d.law u, d.law_nonneg u hu, d.law_sum u hs, fun j => ?_⟩
    rw [← d.abs_signedError, d.signedError_law u hs,
      abs_of_nonneg (mul_nonneg d.gap_pos.le (hu j))]
    simpa only [u, mul_one_div] using he

/-- The exact feasibility nerve is the boundary of the simplex of probes. -/
theorem constraint_nerve (d : ProbeWitness κ k) (S : Finset (Fin (k + 1))) :
    (∃ w : κ → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      ∀ j ∈ S, d.expectation w j = d.target j) ↔ S ≠ univ := by
  classical
  constructor
  · rintro ⟨w, hw, -, hm⟩ rfl
    have hz (j) : d.signedError w j = 0 := by
      have h := d.abs_signedError w j
      rw [hm j (mem_univ j), sub_self, abs_zero, abs_eq_zero] at h
      exact h
    have hg := d.sum_signedError_ge w hw
    simp only [hz, sum_const_zero] at hg
    exact (not_lt_of_ge hg) d.gap_pos
  · intro h
    obtain ⟨a, -, ha⟩ := not_subset.mp (fun hS => h (eq_univ_of_univ_subset hS))
    let u : Fin (k + 1) → ℝ := fun j => if j = a then 1 else 0
    have hu (j) : 0 ≤ u j := by unfold u; split_ifs <;> norm_num
    have hs : ∑ j, u j = 1 := by simp [u]
    refine ⟨d.law u, d.law_nonneg u hu, d.law_sum u hs, fun j hj => ?_⟩
    have hja : j ≠ a := fun hEq => ha (hEq ▸ hj)
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    rw [← d.abs_signedError, d.signedError_law u hs j]
    simp [u, hja]

end ProbeWitness

namespace ContinuousWeightProbes

open ContinuousWeightCounterexample

/-- A zero-one spectral probe is its physical squared minor. -/
theorem determinantValue_projection_probe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (I J : Finset ι) (hc : I.card = J.card) :
    determinantValue (fun i => if i ∈ I then 0 else 1)
      (fun j => if j ∈ J then 1 else 0) U = (subsetMinorSq U I J : ℂ) := by
  classical
  rw [← sum_signedWeight_image_eq_subsetMinorSq U hU I J,
    ← signed_determinant _ _ U hU, sum_filter]
  apply sum_congr rfl
  intro p _
  rw [matchingProduct_subset_marker I J hc]
  split_ifs <;> simp

def pairRows {n : ℕ} [NeZero n] : Fin 5 → Finset (Fin n) :=
  ![{0,1}, {0,2}, {0,3}, {0,3}, {0,3}]

def pairCols {n : ℕ} [NeZero n] : Fin 5 → Finset (Fin n) :=
  ![{2,3}, {0,2}, {0,2}, {0,3}, {1,3}]

def pairTarget : Fin 5 → ℝ :=
  fun j => (![1024,289,144,289,144] j : ℝ) / 2401

private def fiveNumerator : Matrix (Fin 5) (Fin 5) GaussianInt :=
  !![1,4,4,4,0; -4,1,4,-4,0; -4,-4,1,4,0; -4,4,-4,1,0; 0,0,0,0,7]

def fiveMixer : Matrix (Fin 5) (Fin 5) ℂ :=
  (1 / 7 : ℂ) • fiveNumerator.map GaussianInt.toComplex

theorem isUnitary_fiveMixer : IsUnitary fiveMixer := by
  apply isUnitary_divide_gaussian_matrix
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem four_pair_probe_targets (j : Fin 5) :
    subsetMinorSq mixer (pairRows j) (pairCols j) = pairTarget j := by
  fin_cases j <;> simp only [pairRows, pairCols, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    rw [subsetMinorSq_pair mixer isUnitary_mixer (by decide) (by decide)] <;>
    norm_num [pairTarget, mixer, mixerNumerator, Complex.normSq_apply, GaussianInt.toComplex_def',
      Matrix.smul_apply, Matrix.map_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im]

theorem five_pair_probe_targets (j : Fin 5) :
    subsetMinorSq fiveMixer (pairRows j) (pairCols j) = pairTarget j := by
  fin_cases j <;> simp only [pairRows, pairCols, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    rw [subsetMinorSq_pair fiveMixer isUnitary_fiveMixer (by decide) (by decide)] <;>
    norm_num [pairTarget, fiveMixer, fiveNumerator, Complex.normSq_apply, GaussianInt.toComplex_def',
      Matrix.smul_apply, Matrix.map_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im]

theorem five_singleton_probe_target :
    subsetMinorSq fiveMixer {4} {4} = 1 := by
  rw [subsetMinorSq_singleton fiveMixer isUnitary_fiveMixer]
  norm_num [fiveMixer, fiveNumerator, Complex.normSq_apply, GaussianInt.toComplex_def',
    Matrix.smul_apply, Matrix.map_apply, Complex.mul_re, Complex.mul_im]

private def pairEventBit {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) (j : Fin 5) : ℕ :=
  if (pairRows j).map p.toEmbedding = pairCols j then 1 else 0

private def fiveEventBit (p : Equiv.Perm (Fin 5)) (j : Fin 6) : ℕ :=
  if hj : j.val < 5 then pairEventBit p ⟨j.val,hj⟩ else if p 4 = 4 then 0 else 1

def fiveTarget (j : Fin 6) : ℝ :=
  if hj : j.val < 5 then pairTarget ⟨j.val,hj⟩ else 0

private def fourSample (i : Fin 5) : Equiv.Perm (Fin 4) :=
  fourPerm (![3,16,17,23,22] i)

private def fiveSampleValues (i : Fin 6) : Fin 5 → Fin 5 :=
  ![![0,2,3,1,4], ![2,3,0,1,4], ![2,3,1,0,4], ![3,2,1,0,4],
    ![3,2,0,1,4], ![2,3,1,4,0]] i

private def fiveSampleInverse (i : Fin 6) : Fin 5 → Fin 5 :=
  ![![0,3,1,2,4], ![2,3,0,1,4], ![3,2,0,1,4], ![3,2,1,0,4],
    ![2,3,1,0,4], ![4,2,0,1,3]] i

private def fiveSample (i : Fin 6) : Equiv.Perm (Fin 5) where
  toFun := fiveSampleValues i
  invFun := fiveSampleInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem four_cover (p : Equiv.Perm (Fin 4)) :
    pairEventBit p 0 ≤ ∑ j : Fin 4, pairEventBit p j.succ := by
  have h : ∀ i : Fin 24, pairEventBit (fourPerm i) 0 ≤
      ∑ j : Fin 4, pairEventBit (fourPerm i) j.succ := by decide +kernel
  obtain ⟨i,rfl⟩ := fourPerm_surjective p
  exact h i

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem five_cover :
    ∀ p : Equiv.Perm (Fin 5), fiveEventBit p 0 ≤ ∑ j : Fin 5, fiveEventBit p j.succ := by
  decide +kernel

/-- The five projection constraints in matrix order four. -/
def fourProbes : ProbeWitness (Equiv.Perm (Fin 4)) 4 where
  event p j := pairEventBit p j
  target := pairTarget
  sample := fourSample
  cover p := by exact_mod_cast four_cover p
  sample_event a j := by
    have h : ∀ a j : Fin 5, pairEventBit (fourSample a) j =
        if a = 0 then 0 else if j = 0 ∨ a = j then 1 else 0 := by decide +kernel
    have hj := h a j
    split_ifs at hj ⊢ <;> exact_mod_cast hj
  target_nonneg j := by fin_cases j <;> norm_num [pairTarget]
  target_zero_le_one := by norm_num [pairTarget]
  gap_pos := by norm_num [pairTarget, Fin.sum_univ_four]

/-- The five pair constraints and complemented singleton constraint in
matrix order five. -/
def fiveProbes : ProbeWitness (Equiv.Perm (Fin 5)) 5 where
  event p j := fiveEventBit p j
  target := fiveTarget
  sample := fiveSample
  cover p := by exact_mod_cast five_cover p
  sample_event a j := by
    have h : ∀ a j : Fin 6, fiveEventBit (fiveSample a) j =
        if a = 0 then 0 else if j = 0 ∨ a = j then 1 else 0 := by decide +kernel
    have hj := h a j
    split_ifs at hj ⊢ <;> exact_mod_cast hj
  target_nonneg j := by fin_cases j <;> norm_num [fiveTarget, pairTarget]
  target_zero_le_one := by norm_num [fiveTarget, pairTarget]
  gap_pos := by norm_num [fiveTarget, pairTarget, Fin.sum_univ_succ]

theorem four_probe_gap : fourProbes.gap = 158 / 2401 := by
  norm_num [ProbeWitness.gap, fourProbes, pairTarget, Fin.sum_univ_four]

theorem five_probe_gap : fiveProbes.gap = 158 / 2401 := by
  norm_num [ProbeWitness.gap, fiveProbes, fiveTarget, pairTarget, Fin.sum_univ_succ]

theorem four_probe_optimal_error (e : ℝ) :
    (∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      ∀ j, |fourProbes.expectation w j - fourProbes.target j| ≤ e) ↔ 158 / 12005 ≤ e := by
  rw [fourProbes.error_iff, four_probe_gap]
  norm_num

theorem five_probe_optimal_error (e : ℝ) :
    (∃ w : Equiv.Perm (Fin 5) → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      ∀ j, |fiveProbes.expectation w j - fiveProbes.target j| ≤ e) ↔ 79 / 7203 ≤ e := by
  rw [fiveProbes.error_iff, five_probe_gap]
  norm_num

private theorem map_inv_eq_iff {ι : Type*} [DecidableEq ι]
    (p : Equiv.Perm ι) (I J : Finset ι) :
    J.map p.symm.toEmbedding = I ↔ I.map p.toEmbedding = J := by
  constructor <;> intro h
  · rw [← h, Finset.map_map]
    ext j
    simp [Finset.mem_map_equiv]
  · rw [← h, Finset.map_map]
    ext j
    simp [Finset.mem_map_equiv]

theorem pair_probe_matching {n : ℕ} [NeZero n]
    (p : Equiv.Perm (Fin n)) (j : Fin 5) (hc : (pairRows j : Finset (Fin n)).card =
      (pairCols j : Finset (Fin n)).card) :
    matchingProduct (fun i => if i ∈ (pairRows j : Finset (Fin n)) then 0 else 1)
      (fun i => if i ∈ (pairCols j : Finset (Fin n)) then 1 else 0) p.symm =
      (pairEventBit p j : ℂ) := by
  rw [matchingProduct_subset_marker _ _ hc, map_inv_eq_iff]
  unfold pairEventBit
  split_ifs <;> norm_num

theorem four_probe_physical (j : Fin 5) :
    (determinantValue (fun i => if i ∈ (pairRows j : Finset (Fin 4)) then 0 else 1)
      (fun i => if i ∈ pairCols j then 1 else 0) mixer =
        (fourProbes.target j : ℂ)) ∧
      ∀ p, matchingProduct (fun i => if i ∈ pairRows j then 0 else 1)
        (fun i => if i ∈ pairCols j then 1 else 0) p.symm = (fourProbes.event p j : ℂ) := by
  have hc : (pairRows j : Finset (Fin 4)).card = (pairCols j : Finset (Fin 4)).card := by
    fin_cases j <;> decide
  constructor
  · rw [determinantValue_projection_probe _ isUnitary_mixer _ _ hc, four_pair_probe_targets]
    rfl
  · intro p
    simpa only [fourProbes, Complex.ofReal_natCast] using pair_probe_matching p j hc

def fiveProbeRows (j : Fin 6) : Finset (Fin 5) :=
  if hj : j.val < 5 then pairRows ⟨j.val,hj⟩ else {4}

def fiveProbeCols (j : Fin 6) : Finset (Fin 5) :=
  if hj : j.val < 5 then pairCols ⟨j.val,hj⟩ else {4}

theorem five_probe_physical (j : Fin 6) :
    let a (i : Fin 5) : ℂ := if i ∈ fiveProbeRows j then 0 else 1
    let b (i : Fin 5) : ℂ := if i ∈ fiveProbeCols j then 1 else 0
    (determinantValue a b fiveMixer =
      if j.val < 5 then (fiveProbes.target j : ℂ) else 1) ∧
      ∀ p, matchingProduct a b p.symm =
        if j.val < 5 then (fiveProbes.event p j : ℂ) else 1 - (fiveProbes.event p j : ℂ) := by
  dsimp only
  by_cases h : j.val < 5
  · simp only [fiveProbeRows, fiveProbeCols, dif_pos h, if_pos h, fiveProbes,
      fiveTarget, fiveEventBit]
    let q : Fin 5 := ⟨j.val,h⟩
    have hc : (pairRows q : Finset (Fin 5)).card = (pairCols q : Finset (Fin 5)).card := by
      fin_cases q <;> decide
    constructor
    · rw [determinantValue_projection_probe _ isUnitary_fiveMixer _ _ hc, five_pair_probe_targets]
    · intro p
      simpa only [Complex.ofReal_natCast] using pair_probe_matching p q hc
  · simp only [fiveProbeRows, fiveProbeCols, dif_neg h, if_neg h, fiveProbes, fiveEventBit]
    have hc : ({4} : Finset (Fin 5)).card = ({4} : Finset (Fin 5)).card := rfl
    constructor
    · rw [determinantValue_projection_probe _ isUnitary_fiveMixer _ _ hc,
        five_singleton_probe_target, Complex.ofReal_one]
    · intro p
      rw [matchingProduct_subset_marker _ _ hc, map_inv_eq_iff]
      simp only [Finset.map_singleton, Equiv.toEmbedding_apply, Finset.singleton_inj]
      split_ifs <;> norm_num

end ContinuousWeightProbes

end

end MOC
