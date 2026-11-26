import MOC.PfaffianMatchingModulus
import Mathlib.GroupTheory.Perm.Sign

/-! Evaluation of the permutation Pfaffian on the standard skew form. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The standard skew form with one skew block of size two for each pair. -/
def standardSkewBlocks (n : ℕ) : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ :=
  Matrix.of fun i j => if i.1 = j.1 then !![0, 1; -1, 0] i.2 j.2 else 0

private abbrev BoolPair (n : ℕ) := Fin n × Bool

private def boolPairEquiv (n : ℕ) : PfaffianIndex n ≃ BoolPair n :=
  Equiv.prodCongr (Equiv.refl _) finTwoEquiv

private def boolSkewEntry {n : ℕ} (x y : BoolPair n) : ℂ :=
  if x.1 = y.1 then
    if x.2 = y.2 then 0 else if x.2 then -1 else 1
  else 0

private theorem standardSkewBlocks_bool (n : ℕ) (x y : PfaffianIndex n) :
    standardSkewBlocks n x y = boolSkewEntry (boolPairEquiv n x) (boolPairEquiv n y) := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  have hp (k : Fin n) (c : Fin 2) : boolPairEquiv n (k, c) = (k, finTwoEquiv c) := rfl
  rw [hp, hp]
  by_cases h : i = j
  · fin_cases a <;> fin_cases b <;>
      simp [standardSkewBlocks, Matrix.of_apply, boolSkewEntry, finTwoEquiv, h]
  · simp [standardSkewBlocks, Matrix.of_apply, boolSkewEntry, h]

private def preservesPairs {n : ℕ} (p : Equiv.Perm (BoolPair n)) : Prop :=
  ∀ i : Fin n, (p (i, false)).1 = (p (i, true)).1

private instance {n : ℕ} (p : Equiv.Perm (BoolPair n)) : Decidable (preservesPairs p) := by
  unfold preservesPairs
  infer_instance

private def packPairs {n : ℕ} (f : Equiv.Perm (Fin n)) (g : Fin n → Equiv.Perm Bool) :
    Equiv.Perm (BoolPair n) :=
  (Equiv.prodCongrLeft (fun _ : Bool => f)) * Equiv.prodCongrRight g

private theorem packPairs_apply {n : ℕ} (f : Equiv.Perm (Fin n))
    (g : Fin n → Equiv.Perm Bool) (i : Fin n) (b : Bool) :
    packPairs f g (i, b) = (f i, g i b) := rfl

private def pairPacking {n : ℕ} (p : Equiv.Perm (Fin n) × (Fin n → Equiv.Perm Bool)) :
    {q : Equiv.Perm (BoolPair n) // preservesPairs q} :=
  ⟨packPairs p.1 p.2, fun _ => rfl⟩

private theorem pairPacking_bijective (n : ℕ) :
    Function.Bijective (@pairPacking n) := by
  constructor
  · intro p q h
    have hval (i : Fin n) (b : Bool) : (p.1 i, p.2 i b) = (q.1 i, q.2 i b) :=
      congrArg (fun t : {r : Equiv.Perm (BoolPair n) // preservesPairs r} => t.val (i, b)) h
    apply Prod.ext
    · apply Equiv.ext
      intro i
      exact congrArg Prod.fst (hval i false)
    · funext i
      apply Equiv.ext
      intro b
      exact congrArg Prod.snd (hval i b)
  · intro p
    let f (i : Fin n) : Fin n := (p.val (i, false)).1
    let g (i : Fin n) (b : Bool) : Bool := (p.val (i, b)).2
    have hval (i : Fin n) (b : Bool) : p.val (i, b) = (f i, g i b) := by
      apply Prod.ext
      · cases b
        · rfl
        · exact (p.property i).symm
      · rfl
    have hg (i : Fin n) : Function.Bijective (g i) := by
      apply Finite.injective_iff_bijective.mp
      intro b c h
      have h' : p.val (i, b) = p.val (i, c) := by rw [hval, hval, h]
      exact congrArg Prod.snd (p.val.injective h')
    have hf : Function.Bijective f := by
      apply Finite.injective_iff_bijective.mp
      intro i j h
      obtain ⟨b, hb⟩ := (hg i).2 (g j false)
      have h' : p.val (i, b) = p.val (j, false) := by rw [hval, hval, h, hb]
      exact congrArg Prod.fst (p.val.injective h')
    refine ⟨(Equiv.ofBijective f hf, fun i => Equiv.ofBijective (g i) (hg i)), ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i, b⟩
    exact (hval i b).symm

private theorem packPairs_sign {n : ℕ} (f : Equiv.Perm (Fin n))
    (g : Fin n → Equiv.Perm Bool) :
    Equiv.Perm.sign (packPairs f g) = ∏ i, Equiv.Perm.sign (g i) := by
  rw [packPairs, map_mul, Equiv.Perm.sign_prodCongrLeft, Equiv.Perm.sign_prodCongrRight,
    Fintype.prod_bool, Int.units_mul_self, one_mul]

private theorem boolSkewEntry_sign {n : ℕ} (i : Fin n) (g : Equiv.Perm Bool) :
    boolSkewEntry (i, g false) (i, g true) = ((Equiv.Perm.sign g : ℤ) : ℂ) := by
  by_cases h : g false = false
  · have h' : g true = true := by
      have hne : g true ≠ false := fun he => (by decide : true ≠ false)
        (g.injective (he.trans h.symm))
      cases hb : g true <;> simp_all
    have hg : g = 1 := by
      apply Equiv.ext
      intro b
      cases b
      · exact h
      · exact h'
    rw [hg]
    simp [boolSkewEntry]
  · have h₀ : g false = true := by cases hb : g false <;> simp_all
    have h₁ : g true = false := by
      have hne : g true ≠ true := fun he => (by decide : true ≠ false)
        (g.injective (he.trans h₀.symm))
      cases hb : g true <;> simp_all
    have hg : g = Equiv.swap false true := by
      apply Equiv.ext
      intro b
      cases b
      · simpa only [Equiv.swap_apply_left] using h₀
      · simpa only [Equiv.swap_apply_right] using h₁
    rw [h₀, h₁, hg, Equiv.Perm.sign_swap (by decide : false ≠ true)]
    simp [boolSkewEntry]

private def boolPfaffianTerm {n : ℕ} (p : Equiv.Perm (BoolPair n)) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ) * ∏ i : Fin n, boolSkewEntry (p (i, false)) (p (i, true))

private theorem boolPfaffianTerm_pack {n : ℕ} (f : Equiv.Perm (Fin n))
    (g : Fin n → Equiv.Perm Bool) : boolPfaffianTerm (packPairs f g) = 1 := by
  simp only [boolPfaffianTerm, packPairs_apply, boolSkewEntry_sign, packPairs_sign,
    Units.coe_prod, Int.cast_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  have h := congrArg (fun s : ℤˣ => ((s : ℤ) : ℂ)) (Int.units_mul_self (Equiv.Perm.sign (g i)))
  simpa only [Units.val_mul, Units.val_one, Int.cast_mul, Int.cast_one] using h

private theorem boolPfaffianTerm_eq_ite {n : ℕ} (p : Equiv.Perm (BoolPair n)) :
    boolPfaffianTerm p = if preservesPairs p then 1 else 0 := by
  classical
  by_cases h : preservesPairs p
  · obtain ⟨q, hq⟩ := (pairPacking_bijective n).2 ⟨p, h⟩
    have he : packPairs q.1 q.2 = p := congrArg Subtype.val hq
    rw [if_pos h, ← he, boolPfaffianTerm_pack]
  · rw [if_neg h]
    have hh : ∃ i : Fin n, (p (i, false)).1 ≠ (p (i, true)).1 := by
      simpa only [preservesPairs, not_forall] using h
    obtain ⟨i, hi⟩ := hh
    have hz : boolSkewEntry (p (i, false)) (p (i, true)) = 0 := by
      simp only [boolSkewEntry, if_neg hi]
    rw [boolPfaffianTerm, Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]

private theorem card_pair_preserving (n : ℕ) :
    Fintype.card {q : Equiv.Perm (BoolPair n) // preservesPairs q} = 2 ^ n * n.factorial := by
  classical
  let e := Equiv.ofBijective (@pairPacking n) (pairPacking_bijective n)
  rw [← Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun]
  simp only [Fintype.card_perm, Fintype.card_fin, Fintype.card_bool]
  rw [show (2 : ℕ).factorial = 2 by decide, Nat.mul_comm]

/-- The signed permutation sum on the standard skew form gives its
normalizing factor, so the Pfaffian is one in every order. -/
theorem complexPfaffian_standardSkewBlocks (n : ℕ) :
    complexPfaffian (standardSkewBlocks n) = 1 := by
  classical
  let b := boolPairEquiv n
  change (∑ p : Equiv.Perm (PfaffianIndex n),
    ((Equiv.Perm.sign p : ℤ) : ℂ) *
      ∏ i : Fin n, standardSkewBlocks n (p (i, 0)) (p (i, 1))) /
      ((2 : ℂ) ^ n * (n.factorial : ℂ)) = 1
  have hsum :
      (∑ p : Equiv.Perm (PfaffianIndex n), ((Equiv.Perm.sign p : ℤ) : ℂ) *
        ∏ i : Fin n, standardSkewBlocks n (p (i, 0)) (p (i, 1))) =
      ∑ p : Equiv.Perm (BoolPair n), boolPfaffianTerm p := by
    apply Fintype.sum_equiv b.permCongr
    intro p
    have hb₀ (i : Fin n) : b.symm (i, false) = (i, 0) := rfl
    have hb₁ (i : Fin n) : b.symm (i, true) = (i, 1) := rfl
    simp only [boolPfaffianTerm, Equiv.Perm.sign_permCongr, Equiv.permCongr_apply, hb₀, hb₁]
    simp only [standardSkewBlocks_bool, b]
  have hsum' : (∑ p : Equiv.Perm (BoolPair n), boolPfaffianTerm p) =
      (2 : ℂ) ^ n * (n.factorial : ℂ) := by
    simp_rw [boolPfaffianTerm_eq_ite]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_one]
    have hcard := card_pair_preserving n
    rw [Fintype.card_subtype] at hcard
    exact_mod_cast hcard
  rw [hsum, hsum', div_self]
  positivity

end

end MOC
