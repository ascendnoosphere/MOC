import MOC.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Determinant and support identities for a phase change at one eigenvector of a normal sum. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Schur complement at the diagonal block of an arrowhead matrix. -/
theorem det_arrowhead (x : ℂ) (d p q : ι → ℂ) (hd : ∀ i, d i ≠ 0) (s t : ℂ) :
    (fromBlocks (fun (_ _ : Unit) => x) (fun _ j => s * p j)
      (fun i _ => t * q i) (diagonal d)).det =
    (x - (s * t) * ∑ i, p i * q i / d i) * ∏ i, d i := by
  let L : Matrix Unit ι ℂ := fun _ j => s * p j / d j
  let C : Matrix ι Unit ℂ := fun i _ => t * q i
  let X : Matrix Unit Unit ℂ := fun _ _ => x - (s * t) * ∑ i, p i * q i / d i
  have hdiag : L * diagonal d = (fun _ j => s * p j : Matrix Unit ι ℂ) := by
    ext i j
    simp [L, Matrix.mul_diagonal, div_mul_cancel₀, hd]
  have hSchur : X + L * C = (fun _ _ => x : Matrix Unit Unit ℂ) := by
    ext i j
    simp only [X, L, C, Matrix.add_apply, Matrix.mul_apply, Finset.mul_sum]
    have hterm (k : ι) : s * p k / d k * (t * q k) = s * t * (p k * q k / d k) := by
      simp only [div_eq_mul_inv]
      ring
    simp only [hterm, sub_add_cancel]
  calc
    _ = (fromBlocks 1 L 0 (1 : Matrix ι ι ℂ) * fromBlocks X 0 C (diagonal d)).det := by
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
        hdiag, hSchur, C]
    _ = _ := by
      rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
        Matrix.det_one]
      simp only [Matrix.det_unique, Matrix.det_one, one_mul, Matrix.det_diagonal, X]

/-- An arrowhead phase move preserves every real support for which the pair coefficients vanish. -/
theorem arrowhead_phase_support_eq (x η z : ℂ) (d p q : ι → ℂ) (hd : ∀ i, d i ≠ 0)
    (hpair : ∀ i, (η * (∏ j, d j) * (p i * q i / d i)).re = 0) :
    (η * (fromBlocks (fun (_ _ : Unit) => x) (fun _ j => (z - 1) * p j)
      (fun i _ => (star z - 1) * q i) (diagonal d)).det).re =
    (η * (x * ∏ i, d i)).re := by
  rw [det_arrowhead x d p q hd]
  have hn : (z - 1) * (star z - 1) = (Complex.normSq (z - 1) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sub, map_one, starRingEnd_apply, mul_comm]
  rw [hn]
  have hsum :
      (η * (∏ j, d j) * ∑ i, p i * q i / d i).re = 0 := by
    simp only [Finset.mul_sum, map_sum (Complex.reAddGroupHom)] at *
    rw [show (∑ i, η * (∏ j, d j) * (p i * q i / d i)).re =
        ∑ i, (η * (∏ j, d j) * (p i * q i / d i)).re from
      map_sum Complex.reAddGroupHom _ _]
    simp only [hpair, Finset.sum_const_zero]
  rw [show η * ((x - (Complex.normSq (z - 1) : ℂ) * ∑ i, p i * q i / d i) *
      ∏ i, d i) = η * (x * ∏ i, d i) - (Complex.normSq (z - 1) : ℂ) *
        (η * (∏ i, d i) * ∑ i, p i * q i / d i) by ring]
  simp [Complex.sub_re, Complex.mul_re, hsum]

/-- Normality relates the two cross entries, and stationarity makes their support coefficient
purely imaginary. Here `x,y` are distinct eigenvalues of the sum. -/
theorem stationary_pair_support_zero (x y κ u v : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≠ y) (hnormal : star v * (x - y) = star (x - y) * u)
    (hcritical : κ * u * (y⁻¹ - x⁻¹) = star (κ * v * (x⁻¹ - y⁻¹))) :
    (κ * u * v / (x * y)).re = 0 := by
  let c : ℂ := κ * u * (y⁻¹ - x⁻¹)
  have hδ : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hδ' : star (x - y) ≠ 0 := star_ne_zero.mpr hδ
  have hc : star c = κ * v * (x⁻¹ - y⁻¹) := by
    exact (congrArg star hcritical).trans (star_star _)
  have hu : star (v / (x - y)) = u / (x - y) := by
    rw [star_div₀]
    apply (div_eq_div_iff hδ' hδ).2
    simpa only [mul_comm (star (x - y)) u] using hnormal
  have he : κ * u * v / (x * y) = c * (v / (x - y)) := by
    dsimp [c]
    field_simp
    ring
  have hanti : star (κ * u * v / (x * y)) = -(κ * u * v / (x * y)) := by
    conv_lhs => rw [he, star_mul', hc, hu]
    field_simp
    ring
  have hre := congrArg Complex.re hanti
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hre
  exact (CharZero.neg_eq_self_iff.mp hre.symm)

/-- When two normal matrices have a diagonal sum, their cross entries across any pair of
eigenspaces are conjugate up to a phase fixed by the eigenvalue gap. -/
theorem cross_entries_of_normal_diagonal_sum (h : ι → ℂ) (B : Matrix ι ι ℂ)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : (diagonal h - B) * (diagonal h - B)ᴴ = (diagonal h - B)ᴴ * (diagonal h - B))
    (i j : ι) :
    star (B j i) * (h i - h j) = star (h i - h j) * B i j := by
  have hdiag : diagonal h * diagonal (star h) = diagonal (star h) * diagonal h := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun k => mul_comm (h k) (star (h k)))
  simp only [Matrix.conjTranspose_sub, Matrix.diagonal_conjTranspose, Matrix.mul_sub,
    Matrix.sub_mul, hdiag, hB] at hA
  have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hA
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply,
    Matrix.conjTranspose_apply] at he
  rw [star_sub]
  linear_combination -he

/-- Each eigenspace compression of one summand is normal when both summands and their sum
are normal. Here the sum has already been diagonalized. -/
theorem normal_eigenvalue_submatrix (h : ι → ℂ) (B : Matrix ι ι ℂ)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : (diagonal h - B) * (diagonal h - B)ᴴ = (diagonal h - B)ᴴ * (diagonal h - B))
    (x : ℂ) [DecidablePred (fun i => h i = x)] :
    let C := B.submatrix (Subtype.val : {i // h i = x} → ι) Subtype.val
    C * Cᴴ = Cᴴ * C := by
  dsimp only
  ext i j
  let l (k : ι) := B i k * star (B j k)
  let r (k : ι) := star (B k i) * B k j
  change (∑ k : {k // h k = x}, l k) = ∑ k : {k // h k = x}, r k
  let s := Finset.univ.filter (fun k => h k = x)
  have hs (k : ι) : k ∈ s ↔ h k = x := by simp [s]
  rw [← Finset.sum_subtype s hs l, ← Finset.sum_subtype s hs r]
  have hf : (∑ k, l k) = ∑ k, r k := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, l, r] using
      congrArg (fun M : Matrix ι ι ℂ => M i j) hB
  have hoff (k : ι) (hk : h k ≠ x) : l k = r k := by
    have hi := cross_entries_of_normal_diagonal_sum h B hB hA (i : ι) k
    have hj := congrArg star (cross_entries_of_normal_diagonal_sum h B hB hA (j : ι) k)
    rw [i.property] at hi
    rw [j.property] at hj
    simp only [star_mul', star_star] at hj
    apply mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm hk))
    dsimp [l, r]
    simp only [Complex.star_def] at hi hj ⊢
    linear_combination -(B k j) * hi - (B i k) * hj
  have he : (∑ k ∈ Finset.univ.filter (fun k => h k ≠ x), l k) =
      ∑ k ∈ Finset.univ.filter (fun k => h k ≠ x), r k := by
    refine Finset.sum_congr rfl (fun k hk => hoff k ?_)
    exact (Finset.mem_filter.mp hk).2
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => h k = x) l,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => h k = x) r, he] at hf
  exact add_right_cancel hf

/-- A Hermitian commutator of the inverse diagonal sum forces the support coefficient to vanish
between distinct eigenspaces. -/
theorem stationary_normal_diagonal_pair_zero (h : ι → ℂ) (B : Matrix ι ι ℂ)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : (diagonal h - B) * (diagonal h - B)ᴴ = (diagonal h - B)ᴴ * (diagonal h - B))
    (κ : ℂ)
    (hcritical : (κ • (B * diagonal (fun i => (h i)⁻¹) -
      diagonal (fun i => (h i)⁻¹) * B))ᴴ =
      κ • (B * diagonal (fun i => (h i)⁻¹) - diagonal (fun i => (h i)⁻¹) * B))
    (i j : ι) (hi : h i ≠ 0) (hj : h j ≠ 0) (hij : h i ≠ h j) :
    (κ * B i j * B j i / (h i * h j)).re = 0 := by
  apply stationary_pair_support_zero (h i) (h j) κ _ _ hi hj hij
    (cross_entries_of_normal_diagonal_sum h B hB hA i j)
  have hc := congrArg (fun M : Matrix ι ι ℂ => M i j) hcritical.symm
  simpa only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, mul_sub, ← mul_assoc,
    mul_right_comm (κ * B i j), mul_comm ((h i)⁻¹) (B i j),
    mul_comm ((h j)⁻¹) (B j i)] using hc

private theorem diagonal_phase_add_eq_arrowhead
    (h : Unit ⊕ ι → ℂ) (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (z : ℂ) (hz : z * star z = 1) :
    let R := diagonal (Sum.elim (fun _ : Unit => z) (fun _ : ι => 1))
    diagonal h - B + R * B * Rᴴ =
      fromBlocks (fun _ _ => h (Sum.inl ()))
        (fun _ j => (z - 1) * B (Sum.inl ()) (Sum.inr j))
        (fun i _ => (star z - 1) * B (Sum.inr i) (Sum.inl ()))
        (diagonal fun i => h (Sum.inr i)) := by
  dsimp only
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  rcases i with (⟨⟩ | i) <;> rcases j with (⟨⟩ | j)
  · simp only [Sum.elim_inl, Matrix.diagonal_apply_eq, fromBlocks_apply₁₁]
    rw [mul_right_comm z, hz, one_mul, sub_add_cancel]
  · simp [Matrix.diagonal_apply]
    ring
  · simp [Matrix.diagonal_apply]
    ring
  · simp [Matrix.diagonal_apply]

/-- Conjugating the second summand by a phase at the distinguished eigenvector preserves
stationary real support when its row has been diagonalized inside its eigenspace. -/
theorem stationary_normal_diagonal_phase_support_eq
    (h : Unit ⊕ ι → ℂ) (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (η z : ℂ) (hnz : ∀ i, h i ≠ 0) (hz : z * star z = 1)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : (diagonal h - B) * (diagonal h - B)ᴴ = (diagonal h - B)ᴴ * (diagonal h - B))
    (hcritical :
      let M := diagonal (fun i => (h i)⁻¹)
      let κ := η * (diagonal h).det
      (κ • (B * M - M * B))ᴴ = κ • (B * M - M * B))
    (hwithin : ∀ i : ι, h (Sum.inl ()) = h (Sum.inr i) →
      B (Sum.inl ()) (Sum.inr i) * B (Sum.inr i) (Sum.inl ()) = 0) :
    let R := diagonal (Sum.elim (fun _ : Unit => z) (fun _ : ι => 1))
    (η * (diagonal h - B + R * B * Rᴴ).det).re = (η * (diagonal h).det).re := by
  let x := h (Sum.inl ())
  let d (i : ι) := h (Sum.inr i)
  let p (i : ι) := B (Sum.inl ()) (Sum.inr i)
  let q (i : ι) := B (Sum.inr i) (Sum.inl ())
  have hd : (diagonal h).det = x * ∏ i, d i := by
    rw [Matrix.det_diagonal, Fintype.prod_sum_type]
    simp [x, d]
  dsimp only
  rw [diagonal_phase_add_eq_arrowhead h B z hz, hd]
  apply arrowhead_phase_support_eq x η z d p q (fun i => hnz (Sum.inr i))
  intro i
  by_cases hi : x = d i
  · simp [p, q, hwithin i hi]
  · have hc := stationary_normal_diagonal_pair_zero h B hB hA _ hcritical
      (Sum.inl ()) (Sum.inr i) (hnz _) (hnz _) hi
    change ((η * (diagonal h).det) * p i * q i / (x * d i)).re = 0 at hc
    rw [hd] at hc
    convert hc using 2
    have hx : x ≠ 0 := hnz (Sum.inl ())
    have hy : d i ≠ 0 := hnz (Sum.inr i)
    field_simp
    ring

/-- A nontrivial phase strictly increases the squared Frobenius norm when the distinguished
row couples to the rest. The comparison also applies when the new sum is nonnormal. -/
theorem diagonal_phase_frobeniusSq_lt
    (h : Unit ⊕ ι → ℂ) (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (z : ℂ) (hz : z * star z = 1) (hz' : z ≠ 1)
    (hmove : ∃ j : ι, B (Sum.inl ()) (Sum.inr j) ≠ 0) :
    let R := diagonal (Sum.elim (fun _ : Unit => z) (fun _ : ι => 1))
    let S := diagonal h - B + R * B * Rᴴ
    (∑ i, ∑ j, Complex.normSq (diagonal h i j)) < ∑ i, ∑ j, Complex.normSq (S i j) := by
  let p (j : ι) := B (Sum.inl ()) (Sum.inr j)
  let q (i : ι) := B (Sum.inr i) (Sum.inl ())
  let d (i : ι) := h (Sum.inr i)
  let R1 : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
    diagonal (Sum.elim (fun _ : Unit => 1) (fun _ : ι => 1))
  have hR1 : R1 = 1 := by
    have he : Sum.elim (fun _ : Unit => (1 : ℂ)) (fun _ : ι => 1) = fun _ => 1 := by
      funext i
      cases i <;> rfl
    dsimp [R1]
    rw [he, Matrix.diagonal_one]
  have hinitial := diagonal_phase_add_eq_arrowhead h B 1 (by simp)
  change diagonal h - B + R1 * B * R1ᴴ = _ at hinitial
  rw [hR1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, sub_add_cancel] at hinitial
  dsimp only
  rw [diagonal_phase_add_eq_arrowhead h B z hz, hinitial]
  simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Finset.univ_unique, Finset.sum_singleton,
    sub_self, star_one, zero_mul, map_zero, Finset.sum_const_zero, add_zero, zero_add,
    Finset.sum_add_distrib]
  obtain ⟨j, hj⟩ := hmove
  have hpos : 0 < Complex.normSq ((z - 1) * p j) :=
    Complex.normSq_pos.mpr (mul_ne_zero (sub_ne_zero.mpr hz') hj)
  have hrows : 0 < ∑ j, Complex.normSq ((z - 1) * p j) :=
    hpos.trans_le (Finset.single_le_sum (f := fun k => Complex.normSq ((z - 1) * p k))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ j))
  have hcols : 0 ≤ ∑ i, Complex.normSq ((star z - 1) * q i) :=
    Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hpositive := add_pos_of_pos_of_nonneg hrows hcols
  change Complex.normSq (h (Sum.inl ())) + ∑ i, ∑ j, Complex.normSq (diagonal d i j) <
    (Complex.normSq (h (Sum.inl ())) + ∑ i, Complex.normSq ((star z - 1) * q i)) +
      ((∑ j, Complex.normSq ((z - 1) * p j)) + ∑ i, ∑ j, Complex.normSq (diagonal d i j))
  linarith only [hpositive]

/-- A coupled, within-eigenspace diagonal row of an invertible stationary normal sum admits
a unitary reflection with the same determinant support and larger squared Frobenius norm. -/
theorem stationary_normal_diagonal_exists_phase_move
    (h : Unit ⊕ ι → ℂ) (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (η : ℂ) (hnz : ∀ i, h i ≠ 0)
    (hB : B * Bᴴ = Bᴴ * B)
    (hA : (diagonal h - B) * (diagonal h - B)ᴴ = (diagonal h - B)ᴴ * (diagonal h - B))
    (hcritical :
      let M := diagonal (fun i => (h i)⁻¹)
      let κ := η * (diagonal h).det
      (κ • (B * M - M * B))ᴴ = κ • (B * M - M * B))
    (hwithin : ∀ i : ι, h (Sum.inl ()) = h (Sum.inr i) →
      B (Sum.inl ()) (Sum.inr i) * B (Sum.inr i) (Sum.inl ()) = 0)
    (hmove : ∃ j : ι, B (Sum.inl ()) (Sum.inr j) ≠ 0) :
    ∃ R : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ, IsUnitary R ∧
      let S := diagonal h - B + R * B * Rᴴ
      (η * S.det).re = (η * (diagonal h).det).re ∧
      (∑ i, ∑ j, Complex.normSq (diagonal h i j)) < ∑ i, ∑ j, Complex.normSq (S i j) := by
  let w : Unit ⊕ ι → ℂ := Sum.elim (fun _ => -1) (fun _ => 1)
  let R := diagonal w
  have hw₁ (i : Unit ⊕ ι) : w i * star (w i) = 1 := by
    cases i <;> simp [w]
  have hw₂ (i : Unit ⊕ ι) : star (w i) * w i = 1 := (mul_comm _ _).trans (hw₁ i)
  have hR : IsUnitary R := by
    constructor
    · dsimp [R]
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      exact congrArg Matrix.diagonal (funext hw₁)
    · dsimp [R]
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      exact congrArg Matrix.diagonal (funext hw₂)
  have hphase : (-1 : ℂ) * star (-1) = 1 := by simp
  exact ⟨R, hR, stationary_normal_diagonal_phase_support_eq h B η (-1)
    hnz hphase hB hA hcritical hwithin,
    diagonal_phase_frobeniusSq_lt h B (-1) hphase (by norm_num) hmove⟩

end MOC
