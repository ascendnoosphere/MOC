import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Submodule

/-! The local domain case of Krull's principal ideal theorem.
The proof uses stabilization of contracted powers in the Artinian
principal quotient and applies Nakayama before and after localization.
See also the principal ideal theorem statement in the Stacks Project,
https://stacks.math.columbia.edu/tag/00KD, Lemma 10.60.11. -/

namespace MOC

/-- If the maximal ideal of a Noetherian local domain is the radical of
one principal ideal, then any prime properly below the maximal ideal is
zero. The proof works with ordinary powers in the localization, without
a symbolic-power API. -/
theorem prime_eq_bot_of_lt_maximal_of_radical_principal
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : (Ideal.span ({x} : Set R)).radical = IsLocalRing.maximalIdeal R)
    (p : Ideal R) [p.IsPrime] (hp : p < IsLocalRing.maximalIdeal R) : p = ⊥ := by
  let I : Ideal R := Ideal.span ({x} : Set R)
  let m := IsLocalRing.maximalIdeal R
  have hIm : I ≤ m := by
    change I ≤ IsLocalRing.maximalIdeal R
    rw [← hx]
    exact Ideal.le_radical
  have hxp : x ∉ p := by
    intro h
    have hi : I ≤ p := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
    have hmp : m ≤ p := by
      change IsLocalRing.maximalIdeal R ≤ p
      rw [← hx]
      exact (inferInstance : p.IsPrime).radical_le_iff.mpr hi
    exact (not_le_of_gt hp) hmp
  let S := Localization.AtPrime p
  letI : IsNoetherianRing S := IsLocalization.isNoetherianRing p.primeCompl S inferInstance
  let l := algebraMap R S
  let q := IsLocalRing.maximalIdeal S
  let J (n : ℕ) : Ideal R := Ideal.comap l (q ^ n)
  have hJ (a b : ℕ) (h : a ≤ b) : J b ≤ J a :=
    Ideal.comap_mono (Ideal.pow_le_pow_right h)
  have hlx : IsUnit (l x) := IsLocalization.map_units S (⟨x, hxp⟩ : p.primeCompl)
  let k := Ideal.Quotient.mk I
  let A := R ⧸ I
  have hdim : Ring.KrullDimLE 0 A := by
    apply Ring.krullDimLE_zero_iff.mpr
    intro j hj
    letI : j.IsPrime := hj
    have hcomap : Ideal.comap k j = m := by
      have hle : I ≤ Ideal.comap k j := by
        intro y hy
        change k y ∈ j
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
        exact j.zero_mem
      have hr : m ≤ Ideal.comap k j :=
        by
          change IsLocalRing.maximalIdeal R ≤ Ideal.comap k j
          rw [← hx]
          exact (Ideal.comap_isPrime k j).radical_le_iff.mpr hle
      exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime k j).ne_top) hr
    have himg : Ideal.map k m = j :=
      hcomap ▸ Ideal.map_comap_of_surjective k Ideal.Quotient.mk_surjective j
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective k Ideal.Quotient.mk_surjective
      (I := m) (IsLocalRing.maximalIdeal.isMaximal R) with h | h
    · exact False.elim (hj.ne_top (himg ▸ h))
    · exact himg ▸ h
  letI : Ring.KrullDimLE 0 A := hdim
  letI : IsArtinianRing A := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let F : ℕ →o (Submodule A A)ᵒᵈ :=
    ⟨fun n => Ideal.map k (J n), fun a b h => Ideal.map_mono (hJ a b h)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  have he : Ideal.map k (J n) = Ideal.map k (J (n + 1)) := hn (n + 1) (Nat.le_succ n)
  have hsup : J n ⊔ I = J (n + 1) ⊔ I := by
    have hh := congrArg (Ideal.comap k) he
    rw [Ideal.comap_map_of_surjective k Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective k Ideal.Quotient.mk_surjective] at hh
    change J n ⊔ RingHom.ker (Ideal.Quotient.mk I) =
      J (n + 1) ⊔ RingHom.ker (Ideal.Quotient.mk I) at hh
    rw [Ideal.mk_ker] at hh
    exact hh
  have hle : (J n : Submodule R R) ≤ (J (n + 1) : Submodule R R) ⊔ I • (J n : Submodule R R) := by
    intro y hy
    have hym : y ∈ J (n + 1) ⊔ I := hsup ▸ (show y ∈ J n ⊔ I from Ideal.mem_sup_left hy)
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hym
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hw
    have hz' : z ∈ J n := hJ n (n + 1) (Nat.le_succ n) hz
    have hw' : w ∈ J n := by
      have hh := (J n).sub_mem hy hz'
      rw [← hzw] at hh
      simpa using hh
    have ha' : a ∈ J n := by
      change l a ∈ q ^ n
      have hh : l w ∈ q ^ n := hw'
      rw [ha, map_mul] at hh
      exact ((q ^ n).unit_mul_mem_iff_mem hlx).mp hh
    apply Submodule.mem_sup.mpr
    refine ⟨z, hz, w, ?_, hzw⟩
    rw [ha]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton x)) ha'
  have hEq : J n = J (n + 1) := by
    apply le_antisymm _ (hJ n (n + 1) (Nat.le_succ n))
    exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (hIm.trans (IsLocalRing.maximalIdeal_le_jacobson _)) hle
  have hpow : q ^ n = q ^ (n + 1) := by
    have hh := congrArg (Ideal.map l) hEq
    change Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) (q ^ n)) =
      Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) (q ^ (n + 1))) at hh
    simpa only [IsLocalization.map_comap p.primeCompl S] using hh
  have hzero : q ^ n = ⊥ := by
    have hh : (q ^ n : Submodule S S) ≤ q • (q ^ n : Submodule S S) := by
      rw [Ideal.smul_eq_mul (I := q), ← pow_succ']; exact hpow.le
    exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot q (q ^ n)
      (IsNoetherian.noetherian _) hh (IsLocalRing.maximalIdeal_le_jacobson _)
  apply le_antisymm _ bot_le
  intro y hy
  have hyq : l y ∈ q := by
    have he : Ideal.map l p = q := Localization.AtPrime.map_eq_maximalIdeal (I := p)
    rw [← he]
    exact Ideal.mem_map_of_mem l hy
  have hy0 : (l y) ^ n = 0 := by
    have hmem := Ideal.pow_mem_pow hyq n
    rwa [hzero, Ideal.mem_bot] at hmem
  have hly : l y = 0 := isNilpotent_iff_eq_zero.mp ⟨n, hy0⟩
  exact Ideal.mem_bot.mpr ((IsLocalization.injective S p.primeCompl_le_nonZeroDivisors)
    (hly.trans l.map_zero.symm))

end MOC
