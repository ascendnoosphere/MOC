import MOC.SpectralMinorDecomposition

/-! Objective-specific support bounds from an assignment dual on fixed-size
subsets. The certificate uses nonnegative squared minors, not a common
probability law on the underlying permutations.

In order five, put `F(I,J) = Re(η (∏ i ∈ Iᶜ, a i) (∏ j ∈ J, b j))`,
`G(I,J) = F(I,J) + F(Iᶜ,Jᶜ)` and `H(i,j) = G({i},{j})`. Complementary
regrouping of the matching product gives constant, singleton, and doubleton
terms. The pair incidence formula in `OrderFivePairMarkers` converts the
singletons: take `C(I,J) = G(I,J) + (∑ i ∈ I, ∑ j ∈ J, H(i,j)) / 3` and
`c = G(∅,∅) - (∑ i, ∑ j, H(i,j)) / 3`. This expression gives the score
decomposition from subset multiplication, without any positivity claim
for the chosen costs. The theorem below proves the conditional support
inequality for any such cost representation, in every subset layer. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Subsets of a specified size, used as the two sides of an assignment problem. -/
abbrev SubsetLayer (ι : Type*) (k : ℕ) := {J : Finset ι // J.card = k}

/-- A permutation of the labels induces a permutation of its subset layer. -/
def subsetLayerPerm (k : ℕ) (σ : Equiv.Perm ι) : Equiv.Perm (SubsetLayer ι k) where
  toFun J := ⟨J.val.map σ.toEmbedding, (Finset.card_map _).trans J.property⟩
  invFun J := ⟨J.val.map σ.symm.toEmbedding, (Finset.card_map _).trans J.property⟩
  left_inv J := by
    apply Subtype.ext
    ext i
    simp [Finset.mem_map_equiv]
  right_inv J := by
    apply Subtype.ext
    ext i
    simp [Finset.mem_map_equiv]

/-- An upper assignment dual bound on the cost for one actual spectral
objective certifies that same bound for the determinant. -/
theorem spectral_support_le_subset_assignment_dual
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (k : ℕ)
    (c : ℝ) (C : SubsetLayer ι k → SubsetLayer ι k → ℝ)
    (r q : SubsetLayer ι k → ℝ)
    (hscore : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re =
      c + ∑ J, C (subsetLayerPerm k σ J) J)
    (hdual : ∀ I J, C I J ≤ r I + q J) :
    (η * determinantValue a b U).re ≤ c + (∑ I, r I) + ∑ J, q J := by
  classical
  let W := SubsetLayer ι k × SubsetLayer ι k
  let I (e : W) : Finset ι := e.2.val
  let J (e : W) : Finset ι := e.1.val
  let w (e : W) : ℝ := r e.2 + q e.1 - C e.2 e.1
  apply spectral_support_of_subsetImage_certificate a b U hU η _ I J w
      (fun e => sub_nonneg.mpr (hdual e.2 e.1)) (fun _ => 0) (by simp)
  intro σ
  simp only [zero_add]
  have hsum (B : SubsetLayer ι k) :
      (∑ A : SubsetLayer ι k, (r A + q B - C A B) * subsetImageEvent A.val B.val σ) =
        r (subsetLayerPerm k σ B) + q B - C (subsetLayerPerm k σ B) B := by
    let A₀ := subsetLayerPerm k σ B
    have ha (A : SubsetLayer ι k) (hn : A ≠ A₀) :
        B.val.map σ.toEmbedding ≠ A.val := by
      intro he
      apply hn
      exact Subtype.ext he.symm
    rw [Finset.sum_eq_single A₀]
    · simp [subsetImageEvent, A₀, subsetLayerPerm]
    · intro A _ hn
      simp [subsetImageEvent, ha A hn]
    · simp
  rw [hscore, Fintype.sum_prod_type]
  simp only [w, I, J, hsum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Equiv.sum_comp (subsetLayerPerm k σ) r]
  ring

/-- If one permutation of the original labels induces a tight assignment
for the dual potentials, it bounds the determinant support value.
The law and any assignment optimizer for a different objective can differ. -/
theorem spectral_support_of_tight_induced_subset_assignment
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (k : ℕ)
    (c : ℝ) (C : SubsetLayer ι k → SubsetLayer ι k → ℝ)
    (r q : SubsetLayer ι k → ℝ) (σ₀ : Equiv.Perm ι)
    (hscore : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re =
      c + ∑ J, C (subsetLayerPerm k σ J) J)
    (hdual : ∀ I J, C I J ≤ r I + q J)
    (htight : ∀ J, C (subsetLayerPerm k σ₀ J) J = r (subsetLayerPerm k σ₀ J) + q J) :
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b σ₀).re := by
  have h := spectral_support_le_subset_assignment_dual a b U hU η k c C r q hscore hdual
  rw [hscore σ₀]
  simp_rw [htight, Finset.sum_add_distrib, Equiv.sum_comp (subsetLayerPerm k σ₀) r]
  simpa only [add_assoc] using h

end

end MOC
