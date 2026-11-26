import MOC.RankTwoKernelInclusion
import MOC.TwoValues
import Mathlib.Data.Finset.Sum

/-! Convex comparison under decomposable tensor evaluations. -/

open BigOperators Matrix

namespace MOC

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The action of a permutation on the two-state tensor basis indexed by subsets. -/
def subsetPermutationOperator {R : Type*} [Zero R] [One R] (σ : Equiv.Perm ι) :
    Matrix (Finset ι) (Finset ι) R :=
  Matrix.of fun I J => if J.map σ.toEmbedding = I then 1 else 0

noncomputable section

/-- The squared exterior-minor table, viewed as an operator on the subset basis. -/
def exteriorTransportOperator (U : Matrix ι ι ℂ) : Matrix (Finset ι) (Finset ι) ℝ :=
  Matrix.of (subsetMinorSq U)

/-- The basis coordinates of a tensor whose factors have two coordinates. -/
def subsetProductCoordinates (f g : ι → ℂ) (I : Finset ι) : ℂ :=
  (∏ i ∈ Iᶜ, f i) * ∏ i ∈ I, g i

private theorem subsetProductCoordinates_map (f g : ι → ℂ)
    (σ : Equiv.Perm ι) (J : Finset ι) :
    subsetProductCoordinates f g (J.map σ.toEmbedding) =
      subsetProductCoordinates (f ∘ σ) (g ∘ σ) J := by
  have h : (J.map σ.toEmbedding)ᶜ = (Jᶜ).map σ.toEmbedding := by
    ext i
    simp [Finset.mem_map_equiv]
  simp only [subsetProductCoordinates, h, Finset.prod_map, Function.comp_apply,
    Equiv.toEmbedding_apply]

/-- Evaluate an operator between one product covector and one product vector. -/
def productTensorEvaluation (a₀ a₁ b₀ b₁ : ι → ℂ) :
    Matrix (Finset ι) (Finset ι) ℝ →ₗ[ℝ] ℂ where
  toFun T := ∑ J, ∑ I, (T I J : ℂ) *
    (subsetProductCoordinates a₀ a₁ I * subsetProductCoordinates b₀ b₁ J)
  map_add' T R := by
    simp only [Matrix.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  map_smul' c T := by
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul,
      RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- Evaluating a permutation on product data multiplies the pairwise evaluations. -/
theorem productTensorEvaluation_permutation (a₀ a₁ b₀ b₁ : ι → ℂ) (σ : Equiv.Perm ι) :
    productTensorEvaluation a₀ a₁ b₀ b₁ (subsetPermutationOperator σ) =
      ∏ j, (a₀ (σ j) * b₀ j + a₁ (σ j) * b₁ j) := by
  change (∑ J, ∑ I, ((if J.map σ.toEmbedding = I then 1 else 0 : ℝ) : ℂ) *
    (subsetProductCoordinates a₀ a₁ I * subsetProductCoordinates b₀ b₁ J)) = _
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, subsetProductCoordinates_map]
  rw [show (∏ j, (a₀ (σ j) * b₀ j + a₁ (σ j) * b₁ j)) =
      ∏ j, (a₁ (σ j) * b₁ j + a₀ (σ j) * b₀ j) from
    Finset.prod_congr rfl fun j _ => add_comm _ _]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro J _
  simp only [subsetProductCoordinates, Function.comp_apply, Finset.prod_mul_distrib]
  ring

/-- One real signed sum of permutation operators gives the entire exterior table. -/
theorem exteriorTransportOperator_eq_sum (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    exteriorTransportOperator U =
      ∑ σ : Equiv.Perm ι, realSignedWeight U σ • subsetPermutationOperator σ := by
  ext I J
  have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  have h' : (∑ σ : Equiv.Perm ι, if J.map σ.toEmbedding = I then realSignedWeight U σ else 0) =
      subsetMinorSq U I J := by
    simpa only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
      Complex.ofReal_re, realSignedWeight] using h
  simpa only [exteriorTransportOperator, subsetPermutationOperator, Matrix.of_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] using h'.symm

private theorem productTensorEvaluation_exterior_spectral (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    productTensorEvaluation a (fun _ => 1) (fun _ => 1) b (exteriorTransportOperator U) =
      determinantValue a b U := by
  rw [determinantValue_eq_sum_subsetMinors a b U hU]
  change (∑ J, ∑ I, (subsetMinorSq U I J : ℂ) *
    (subsetProductCoordinates a (fun _ => 1) I * subsetProductCoordinates (fun _ => 1) b J)) = _
  simp only [subsetProductCoordinates, Finset.prod_const_one, one_mul, mul_one]

/-- The exterior table evaluates on arbitrary product data as the determinant
of the corresponding bilinear pairing kernel. -/
theorem productTensorEvaluation_exterior (a₀ a₁ b₀ b₁ : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    productTensorEvaluation a₀ a₁ b₀ b₁ (exteriorTransportOperator U) =
      kernelDeterminantValue (Matrix.of fun i j => a₀ i * b₀ j + a₁ i * b₁ j) U := by
  let K := Matrix.of fun i j => a₀ i * b₀ j + a₁ i * b₁ j
  have hK : K.rank ≤ 2 := rank_two_product_kernel_le a₀ a₁ b₀ b₁
  rw [exteriorTransportOperator_eq_sum U hU, map_sum]
  simp only [map_smul, productTensorEvaluation_permutation, Complex.real_smul]
  exact (kernelDeterminantValue_eq_sum_realSigned K U hK hU).symm

/-- Each product evaluation has its own convex combination of permutations. -/
def SegreAdmissible (T : Matrix (Finset ι) (Finset ι) ℝ) : Prop :=
  ∀ a₀ a₁ b₀ b₁ : ι → ℂ, productTensorEvaluation a₀ a₁ b₀ b₁ T ∈
    convexHull ℝ (Set.range fun σ : Equiv.Perm ι =>
      productTensorEvaluation a₀ a₁ b₀ b₁ (subsetPermutationOperator σ))

theorem conjecture_iff_segre_admissible : Conjecture ι ↔
    ∀ U : Matrix ι ι ℂ, IsUnitary U → SegreAdmissible (exteriorTransportOperator U) := by
  constructor
  · intro h U hU a₀ a₁ b₀ b₁
    rw [productTensorEvaluation_exterior _ _ _ _ U hU]
    simp_rw [productTensorEvaluation_permutation]
    exact (rankTwoKernelInclusion_iff_conjecture.mpr h) _ U
      (rank_two_product_kernel_le a₀ a₁ b₀ b₁) hU
  · intro h a b U hU
    have hs := h U hU a (fun _ => 1) (fun _ => 1) b
    rw [productTensorEvaluation_exterior_spectral a b U hU] at hs
    simpa only [productTensorEvaluation_permutation, mul_one, one_mul, matchingProduct] using hs

/-- The set of operators with the product-evaluation comparison is convex. -/
theorem convex_segreAdmissible : Convex ℝ {T : Matrix (Finset ι) (Finset ι) ℝ | SegreAdmissible T} := by
  intro T hT R hR c d hc hd hcd a₀ a₁ b₀ b₁
  simp only [map_add, map_smul]
  exact convex_convexHull ℝ _ (hT a₀ a₁ b₀ b₁) (hR a₀ a₁ b₀ b₁) hc hd hcd

/-- Tensor product of two subset-basis operators, indexed by subsets of a disjoint sum. -/
def subsetTensorProduct (T : Matrix (Finset ι) (Finset ι) ℝ)
    (R : Matrix (Finset κ) (Finset κ) ℝ) : Matrix (Finset (ι ⊕ κ)) (Finset (ι ⊕ κ)) ℝ :=
  Matrix.of fun I J => T I.toLeft J.toLeft * R I.toRight J.toRight

private theorem subsetProductCoordinates_sum (f g : ι ⊕ κ → ℂ)
    (I : Finset ι) (J : Finset κ) :
    subsetProductCoordinates f g (I.disjSum J) =
      subsetProductCoordinates (f ∘ Sum.inl) (g ∘ Sum.inl) I *
      subsetProductCoordinates (f ∘ Sum.inr) (g ∘ Sum.inr) J := by
  have h : (I.disjSum J)ᶜ = Iᶜ.disjSum Jᶜ := by
    ext x
    cases x <;> simp
  simp only [subsetProductCoordinates, h, Finset.prod_disj_sum, Function.comp_apply]
  ring

private theorem productTensorEvaluation_tensor (T : Matrix (Finset ι) (Finset ι) ℝ)
    (R : Matrix (Finset κ) (Finset κ) ℝ) (a₀ a₁ b₀ b₁ : ι ⊕ κ → ℂ) :
    productTensorEvaluation a₀ a₁ b₀ b₁ (subsetTensorProduct T R) =
      productTensorEvaluation (a₀ ∘ Sum.inl) (a₁ ∘ Sum.inl) (b₀ ∘ Sum.inl) (b₁ ∘ Sum.inl) T *
      productTensorEvaluation (a₀ ∘ Sum.inr) (a₁ ∘ Sum.inr) (b₀ ∘ Sum.inr) (b₁ ∘ Sum.inr) R := by
  let f (J I : Finset (ι ⊕ κ)) := ((subsetTensorProduct T R) I J : ℂ) *
    (subsetProductCoordinates a₀ a₁ I * subsetProductCoordinates b₀ b₁ J)
  let l (J I : Finset ι) := (T I J : ℂ) *
    (subsetProductCoordinates (a₀ ∘ Sum.inl) (a₁ ∘ Sum.inl) I *
      subsetProductCoordinates (b₀ ∘ Sum.inl) (b₁ ∘ Sum.inl) J)
  let r (J I : Finset κ) := (R I J : ℂ) *
    (subsetProductCoordinates (a₀ ∘ Sum.inr) (a₁ ∘ Sum.inr) I *
      subsetProductCoordinates (b₀ ∘ Sum.inr) (b₁ ∘ Sum.inr) J)
  let e := (Finset.sumEquiv (α := ι) (β := κ)).toEquiv.symm
  have h (J I : Finset ι × Finset κ) : f (e J) (e I) = l J.1 I.1 * r J.2 I.2 := by
    change f (J.1.disjSum J.2) (I.1.disjSum I.2) = _
    simp only [f, l, r, subsetTensorProduct, Matrix.of_apply, Finset.toLeft_disjSum,
      Finset.toRight_disjSum, Complex.ofReal_mul, subsetProductCoordinates_sum]
    ring
  change (∑ J, ∑ I, f J I) = (∑ J, ∑ I, l J I) * ∑ J, ∑ I, r J I
  calc
    _ = ∑ J, ∑ I, f (e J) (e I) := by
      rw [← Equiv.sum_comp e (fun J => ∑ I, f J I)]
      apply Finset.sum_congr rfl
      intro J _
      exact (Equiv.sum_comp e (f (e J))).symm
    _ = ∑ j, ∑ j', ∑ i, ∑ i', l j i * r j' i' := by
      simp only [h, Fintype.sum_prod_type]
    _ = ∑ j, ∑ i, ∑ j', ∑ i', l j i * r j' i' := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.mul_sum]

/-- Tensor products preserve the product-evaluation convex comparison. -/
theorem SegreAdmissible.tensor {T : Matrix (Finset ι) (Finset ι) ℝ}
    {R : Matrix (Finset κ) (Finset κ) ℝ} (hT : SegreAdmissible T)
    (hR : SegreAdmissible R) : SegreAdmissible (subsetTensorProduct T R) := by
  intro a₀ a₁ b₀ b₁
  rw [productTensorEvaluation_tensor]
  apply mul_mem_of_mem_convexHulls (convex_convexHull ℝ _) _ (hT _ _ _ _) (hR _ _ _ _)
  rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
  apply subset_convexHull ℝ _
  refine ⟨Equiv.sumCongr σ τ, ?_⟩
  simp only [productTensorEvaluation_permutation, Fintype.prod_sum_type,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Function.comp_apply]

end

end MOC
