import MOC.Reformulations.Common

open BigOperators

namespace MOC.Reformulations

private def multiplicity {n r : ℕ} (f : Fin n → Fin r) (i : Fin r) : ℕ :=
  (Finset.univ.filter fun j => f j = i).card

/-- Integer couplings of finite spectral labels. Equal spectral values can be
grouped under one label; assigning them several labels also works. -/
def IntegerCoupling {n r s : ℕ} (l : Fin n → Fin r) (rgt : Fin n → Fin s)
    (c : Fin r → Fin s → ℕ) : Prop :=
  (∀ i, ∑ j, c i j = multiplicity l i) ∧
  (∀ j, ∑ i, c i j = multiplicity rgt j)

/-- C★ 4. The hull vertices are products of complex factors with integer multiplicities. -/
def CouplingForm : Prop :=
  ∀ (n r s : ℕ) (l : Fin n → Fin r) (rgt : Fin n → Fin s)
    (a : Fin r → ℂ) (b : Fin s → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U →
    determinantValue (a ∘ l) (b ∘ rgt) U ∈ convexHull ℝ
      {z | ∃ c : Fin r → Fin s → ℕ, IntegerCoupling l rgt c ∧
        z = ∏ i, ∏ j, (a i + b j) ^ c i j}

private theorem permutation_has_coupling {n r s : ℕ}
    (l : Fin n → Fin r) (rgt : Fin n → Fin s) (a : Fin r → ℂ) (b : Fin s → ℂ)
    (p : Equiv.Perm (Fin n)) :
    ∃ c : Fin r → Fin s → ℕ, IntegerCoupling l rgt c ∧
      matchingProduct (a ∘ l) (b ∘ rgt) p = ∏ i, ∏ j, (a i + b j) ^ c i j := by
  classical
  let c (i : Fin r) (j : Fin s) :=
    (Finset.univ.filter (fun k : Fin n => l (p k) = i ∧ rgt k = j)).card
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro i
    have h : (Finset.univ.filter fun k : Fin n => l (p k) = i).map p.toEmbedding =
        (Finset.univ.filter fun k : Fin n => l k = i) := by
      ext k
      simp [Finset.mem_map_equiv]
    rw [multiplicity, ← h, Finset.card_map]
    simpa only [c, Finset.filter_filter, Finset.mem_univ, and_true] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ.filter fun k : Fin n => l (p k) = i) Finset.univ rgt)
  · intro j
    simpa only [c, multiplicity, Finset.filter_filter, Finset.mem_univ, and_true, true_and, and_comm] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ.filter fun k : Fin n => rgt k = j) Finset.univ (fun k => l (p k)))
  · unfold matchingProduct
    calc
      _ = ∏ ij : Fin r × Fin s, (a ij.1 + b ij.2) ^ c ij.1 ij.2 := by
        change (∏ k : Fin n, (a (l (p k)) + b (rgt k))) = _
        rw [← Finset.prod_fiberwise' Finset.univ (fun k : Fin n => (l (p k), rgt k))
          (fun ij : Fin r × Fin s => a ij.1 + b ij.2)]
        simp only [Finset.prod_const, c]
        apply Finset.prod_congr rfl
        rintro ⟨i, j⟩ _
        simp only [Prod.mk.injEq]
      _ = _ := Fintype.prod_prod_type _

private theorem unit_sum_nat {n : ℕ} (f : Fin n → ℕ) (hf : (∑ i, f i) = 1) :
    ∃ i, f i = 1 ∧ ∀ j, j ≠ i → f j = 0 := by
  classical
  have h : ∃ i, f i ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hf
  obtain ⟨i, hi⟩ := h
  have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (f j))
    (Finset.mem_univ i)
  have hi' : f i = 1 := by omega
  refine ⟨i, hi', fun j hj => ?_⟩
  have hz := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  rw [hf, hi'] at hz
  have hle' := Finset.single_le_sum
    (fun k (_ : k ∈ Finset.univ.erase i) => Nat.zero_le (f k))
    (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  omega

private theorem multiplicity_id {n : ℕ} (i : Fin n) :
    multiplicity id i = 1 := by
  classical
  have h : (Finset.univ.filter fun j : Fin n => id j = i) = {i} := by ext j; simp
  rw [multiplicity, h, Finset.card_singleton]

private theorem unit_coupling_is_permutation {n : ℕ} (c : Fin n → Fin n → ℕ)
    (hc : IntegerCoupling id id c) :
    ∃ p : Equiv.Perm (Fin n), ∀ i j, c i j = if p j = i then 1 else 0 := by
  classical
  have hcol (j : Fin n) := unit_sum_nat (fun i => c i j) ((hc.2 j).trans (multiplicity_id j))
  choose f hf hzero using hcol
  dsimp only at hf hzero
  have hrow (i : Fin n) := unit_sum_nat (c i) ((hc.1 i).trans (multiplicity_id i))
  have hinj : Function.Injective f := by
    intro j k he
    obtain ⟨j₀, _, hz⟩ := hrow (f j)
    have hj : j = j₀ := by
      by_cases hh : j = j₀
      · exact hh
      · have h1 := hf j
        have h0 := hz j hh
        omega
    have hk : k = j₀ := by
      by_cases hh : k = j₀
      · exact hh
      · have h1 := hf k
        have h0 := hz k hh
        rw [he] at h0
        omega
    exact hj.trans hk.symm
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  intro i j
  change c i j = if f j = i then 1 else 0
  split
  · rename_i he
    simpa only [← he] using hf j
  · rename_i he
    exact hzero j i (Ne.symm he)

theorem couplingForm_iff : CouplingForm ↔ MOCIsTrue := by
  classical
  constructor
  · intro h n a b U hU
    apply convexHull_mono _ (h n n n id id a b U hU)
    rintro z ⟨c, hc, rfl⟩
    obtain ⟨p, hp⟩ := unit_coupling_is_permutation c hc
    refine ⟨p, ?_⟩
    unfold matchingProduct
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    symm
    rw [Finset.prod_eq_single (p j)]
    · rw [hp, if_pos rfl, pow_one]
    · intro i _ hi
      rw [hp, if_neg (Ne.symm hi), pow_zero]
    · simp
  · intro h n r s l rgt a b U hU
    apply convexHull_mono _ (h n (a ∘ l) (b ∘ rgt) U hU)
    rintro z ⟨p, rfl⟩
    exact permutation_has_coupling l rgt a b p

end MOC.Reformulations
