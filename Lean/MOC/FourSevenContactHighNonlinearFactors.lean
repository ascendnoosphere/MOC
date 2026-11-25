import MOC.FourInversePencilCertificates

/-! The four-function Gram certificate for the seven-contact cost with
ordinary ray indices 7, 13, 17, 20, 27, and 31. -/

namespace MOC

/-- A Gram bound for rays 7, 13, and 31 suffices after adding three
nonnegative ordinary coefficients. -/
theorem fourSevenContactHighCost_sos_of_gram_budget
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 < f)
    (hbudget : (a + 1) * (b + 1) ≤ f * (a * b - 1)) :
    IsRealMatchingSOS (fun p =>
      mixedCostRay 0 p + a * ordinaryCostRay 7 p + b * ordinaryCostRay 13 p +
        c * ordinaryCostRay 17 p + d * ordinaryCostRay 20 p +
        e * ordinaryCostRay 27 p + f * ordinaryCostRay 31 p) := by
  have hpos : 0 < (a + 1) * (b + 1) := by positivity
  have hab : 1 < a * b := by
    by_contra! hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hf.le (sub_nonpos.mpr hn)
    exact (not_lt_of_ge (hbudget.trans hnonpos)) hpos
  have hbase := fourMatchingSOS_of_gram_budget ha hab hbudget
  have hc' := fourMatchingSOS_add_ordinaryRay hbase 17 hc
  have hd' := fourMatchingSOS_add_ordinaryRay hc' 20 hd
  have he' := fourMatchingSOS_add_ordinaryRay hd' 27 he
  convert he' using 1
  funext p
  ring

end MOC
