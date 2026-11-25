import MOC.Weights
import MOC.Normal
import MOC.ExtendedCases

/-!
# Weighted permutation cycles

A scalar shift of a normal weighted permutation cycle satisfies the determinant
inclusion against every diagonal partner. The uniform permutation law suffices.
-/

open scoped BigOperators Matrix
open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weighted permutation matrix with weight `w j` in column `j`. -/
def weightedPermutationMatrix (p : Equiv.Perm ι) (w : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => if i = p j then w j else 0

/-- A single cycle visits every index from each starting index. This includes a
one-element cycle. -/
def TraversesAllIndices (p : Equiv.Perm ι) : Prop :=
  ∀ i j, ∃ k : ℕ, (p ^ k) i = j

omit [Fintype ι] [DecidableEq ι] in
private theorem no_fixed_point_of_ne_one {p : Equiv.Perm ι}
    (hcycle : TraversesAllIndices p) (hp : p ≠ 1) (i : ι) : p i ≠ i := by
  intro hi
  have hpow (k : ℕ) : (p ^ k) i = i := by
    induction k with
    | zero => rw [pow_zero, Equiv.Perm.one_apply]
    | succ k hk => rw [pow_succ', Equiv.Perm.mul_apply, hk, hi]
  apply hp
  ext j
  obtain ⟨k, hk⟩ := hcycle i j
  have hji : j = i := hk.symm.trans (hpow k)
  rw [hji]
  exact hi

private theorem perm_eq_one_or_cycle {p σ : Equiv.Perm ι}
    (hcycle : TraversesAllIndices p) (hσ : ∀ j, σ j = j ∨ σ j = p j) :
    σ = 1 ∨ σ = p := by
  by_cases h : σ = 1
  · exact Or.inl h
  right
  have hi : ∃ i, σ i ≠ i := by
    by_contra hn
    apply h
    ext i
    exact not_not.mp (fun hni => hn ⟨i, hni⟩)
  obtain ⟨i, hi⟩ := hi
  have hnext (j : ι) (hj : σ j ≠ j) : σ (p j) ≠ p j := by
    intro hfix
    have hmove : σ j = p j := (hσ j).resolve_left hj
    exact hj (hmove.trans (σ.injective (hmove.trans hfix.symm)).symm)
  have hpow (k : ℕ) : σ ((p ^ k) i) ≠ (p ^ k) i := by
    induction k with
    | zero => rwa [pow_zero, Equiv.Perm.one_apply]
    | succ k hk =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hnext _ hk
  ext j
  obtain ⟨k, hk⟩ := hcycle i j
  exact (hσ j).resolve_left (hk ▸ hpow k)

/-- The only possible nonzero determinant terms use all diagonal entries or
all cycle edges. -/
theorem det_diagonal_add_weightedPermutationMatrix (a w : ι → ℂ)
    {p : Equiv.Perm ι} (hcycle : TraversesAllIndices p) (hp : p ≠ 1) :
    (diagonal a + weightedPermutationMatrix p w).det =
      (∏ j, a j) + ((Equiv.Perm.sign p : ℤ) : ℂ) * ∏ j, w j := by
  let M := diagonal a + weightedPermutationMatrix p w
  have hfixed := no_fixed_point_of_ne_one hcycle hp
  have hterm (σ : Equiv.Perm ι) (h₁ : σ ≠ 1) (h₂ : σ ≠ p) :
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, M (σ j) j = 0 := by
    have h : ¬ ∀ j, σ j = j ∨ σ j = p j := by
      intro hσ
      exact (perm_eq_one_or_cycle hcycle hσ).elim h₁ h₂
    obtain ⟨j, hj⟩ := not_forall.mp h
    have hj₁ : σ j ≠ j := fun heq => hj (Or.inl heq)
    have hj₂ : σ j ≠ p j := fun heq => hj (Or.inr heq)
    have hz : M (σ j) j = 0 := by
      simp [M, weightedPermutationMatrix, Matrix.diagonal_apply_ne _ hj₁, hj₂]
    have hprod : ∏ i, M (σ i) i = 0 :=
      Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) hz
    rw [hprod, mul_zero]
  have hone (j : ι) : M j j = a j := by
    simp [M, weightedPermutationMatrix, Ne.symm (hfixed j)]
  have hperm (j : ι) : M (p j) j = w j := by
    simp [M, weightedPermutationMatrix, Matrix.diagonal_apply_ne _ (hfixed j)]
  change M.det = _
  rw [Matrix.det_apply']
  calc
    _ = ∑ σ : Equiv.Perm ι,
        ((if σ = 1 then ∏ j, a j else 0) +
          (if σ = p then ((Equiv.Perm.sign p : ℤ) : ℂ) * ∏ j, w j else 0)) := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h₁ : σ = 1
      · subst σ
        simp [hp.symm, hone, Equiv.Perm.one_apply, Equiv.Perm.sign_one]
      by_cases h₂ : σ = p
      · subst σ
        simp [hp, hperm]
      simp [h₁, h₂, hterm σ h₁ h₂]
    _ = _ := by simp [Finset.sum_add_distrib]

/-- If permuting the diagonal partner leaves its determinant unchanged, the
uniform mean of the matching products equals that determinant. -/
theorem uniform_matching_mean_of_diagonal_permutation_invariant
    (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (hinv : ∀ ρ : Equiv.Perm ι, determinantValue (a ∘ ρ) b U = determinantValue a b U) :
    ∑ τ : Equiv.Perm ι, (((Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ : ℝ) : ℂ) *
      matchingProduct a b τ = determinantValue a b U := by
  let N : ℂ := Fintype.card (Equiv.Perm ι)
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm ι) ≠ 0)
  have hmatching (σ : Equiv.Perm ι) :
      ∑ ρ : Equiv.Perm ι, matchingProduct (a ∘ ρ) b σ =
        ∑ τ : Equiv.Perm ι, matchingProduct a b τ :=
    Equiv.sum_comp (Equiv.mulRight σ) (matchingProduct a b)
  have havg : N * determinantValue a b U = ∑ τ : Equiv.Perm ι, matchingProduct a b τ := by
    calc
      _ = ∑ ρ : Equiv.Perm ι, determinantValue (a ∘ ρ) b U := by
        simp [hinv, N, nsmul_eq_mul]
      _ = ∑ ρ : Equiv.Perm ι, ∑ σ : Equiv.Perm ι,
          signedWeight U σ * matchingProduct (a ∘ ρ) b σ := by
        apply Finset.sum_congr rfl
        intro ρ _
        exact (signed_determinant (a ∘ ρ) b U hU).symm
      _ = ∑ σ : Equiv.Perm ι, signedWeight U σ *
          (∑ τ : Equiv.Perm ι, matchingProduct a b τ) := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, hmatching]
      _ = _ := by rw [← Finset.sum_mul, sum_signedWeight U (det_ne_zero_of_unitary hU), one_mul]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast, ← Finset.mul_sum]
  change N⁻¹ * _ = _
  rw [← havg, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- The uniform permutation law works for every diagonal partner of a scalar
shift of a normal weighted cycle. -/
theorem uniform_matching_mean_weighted_permutation_cycle
    (a b w : ι → ℂ) (c : ℂ) {p : Equiv.Perm ι} {U : Matrix ι ι ℂ}
    (hcycle : TraversesAllIndices p) (hU : IsUnitary U)
    (hB : U * diagonal b * Uᴴ = diagonal (fun _ => c) + weightedPermutationMatrix p w) :
    ∑ τ : Equiv.Perm ι, (((Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ : ℝ) : ℂ) *
      matchingProduct a b τ = determinantValue a b U := by
  apply uniform_matching_mean_of_diagonal_permutation_invariant a b hU
  intro ρ
  by_cases hp : p = 1
  · subst p
    haveI : Subsingleton ι := ⟨fun i j => by
      obtain ⟨k, hk⟩ := hcycle i j
      simpa only [one_pow, Equiv.Perm.one_apply] using hk⟩
    have hρ : ρ = 1 := by
      ext i
      exact Subsingleton.elim _ _
    subst ρ
    rfl
  simp only [determinantValue, hB, ← add_assoc, Matrix.diagonal_add,
    det_diagonal_add_weightedPermutationMatrix _ _ hcycle hp]
  congr 1
  exact Equiv.prod_comp ρ (fun i => a i + c)

/-- In a diagonal partner basis, a scalar shift of a normal weighted cycle
satisfies the determinant inclusion for every diagonal partner. The equality
`hB` gives the spectral list of the shifted cycle through a unitary
diagonalization. -/
theorem holds_weighted_permutation_cycle
    (a b w : ι → ℂ) (c : ℂ) {p : Equiv.Perm ι} {U : Matrix ι ι ℂ}
    (hcycle : TraversesAllIndices p) (hU : IsUnitary U)
    (hB : U * diagonal b * Uᴴ = diagonal (fun _ => c) + weightedPermutationMatrix p w) :
    Holds a b U := by
  let r : ℝ := Fintype.card (Equiv.Perm ι)
  have hr : r ≠ 0 := by
    dsimp [r]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm ι) ≠ 0)
  refine holds_of_weights (fun _ => r⁻¹) (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) ?_ ?_
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hr
  exact uniform_matching_mean_weighted_permutation_cycle a b w c hcycle hU hB

/-- The determinant inclusion for a diagonal matrix and any finite family of
normal weighted cycle blocks. Each block has its own scalar shift. -/
theorem det_mem_hull_of_weighted_permutation_cycle_blocks
    {k : ℕ} (m : Fin k → ℕ) (p : ∀ j, Equiv.Perm (Fin (m j)))
    (w : ∀ j, Fin (m j) → ℂ) (c : Fin k → ℂ) (a b : (Σ j, Fin (m j)) → ℂ)
    (hcycle : ∀ j, TraversesAllIndices (p j))
    (B : Matrix (Σ j, Fin (m j)) (Σ j, Fin (m j)) ℂ)
    (hB : B = Matrix.blockDiagonal'
      (fun j => diagonal (fun _ => c j) + weightedPermutationMatrix (p j) (w j)))
    (hNormal : IsStarNormal B)
    (hRoots : B.charpoly.roots = Finset.univ.val.map b) :
    (diagonal a + B).det ∈ convexHull ℝ (Set.range (matchingProduct a b)) := by
  let W (j : Fin k) := diagonal (fun _ => c j) + weightedPermutationMatrix (p j) (w j)
  change B = Matrix.blockDiagonal' W at hB
  have hlocal (j : Fin k) : IsStarNormal (W j) := by
    constructor
    have h : star B * B = B * star B := hNormal.star_comm_self.eq
    change Bᴴ * B = B * Bᴴ at h
    rw [hB, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_inj] at h
    exact congrFun h j
  choose d U hu hd using fun j => exists_unitary_diagonalization (W j) (hlocal j)
  let V := Matrix.blockDiagonal' U
  let b' : (Σ j, Fin (m j)) → ℂ := fun i => d i.1 i.2
  have hV : IsUnitary V := by
    dsimp [V]
    constructor <;>
      rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
        ← Matrix.blockDiagonal'_one, Matrix.blockDiagonal'_inj] <;>
      funext j
    · exact (hu j).1
    · exact (hu j).2
  have hdiag : B = V * diagonal b' * Vᴴ := by
    rw [hB]
    dsimp [V, b']
    rw [← Matrix.blockDiagonal'_diagonal, Matrix.blockDiagonal'_conjTranspose,
      ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext hd)
  have hcovered : Holds a b' V := by
    apply holds_of_finite_paired_blocks m (Equiv.refl _) (Equiv.refl _) a b' V U
    · simp [V]
    intro j
    exact holds_weighted_permutation_cycle _ (d j) (w j) (c j) (hcycle j) (hu j) (hd j).symm
  have heq : (Finset.univ : Finset (Σ j, Fin (m j))).val.map b =
      (Finset.univ : Finset (Σ j, Fin (m j))).val.map b' := by
    rw [← hRoots, hdiag, roots_unitary_diagonalization b' hV]
  obtain ⟨e, rfl⟩ := exists_perm_of_equal_multisets b b' heq
  rw [show a = a ∘ (Equiv.refl _) by rfl, matchingRange_relabel, hdiag]
  exact hcovered

end

end MOC
