import MOC.WeightedDiamondLowerRows
import MOC.WeightedDiamondPackedCut

/-! Add the inequality at permutation 15 to the order-four ray census. -/

namespace MOC.RayCoefficients

namespace LowerCut3

set_option maxRecDepth 32000
set_option maxHeartbeats 60000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 6, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 3, 0, 4, 0, 0, 0, 0, 5, 0]

private def edges : Array (Crossing 28 34) :=
  #[.keep 22 [1], .keep 23 [1], .keep 24 [1], .keep 25 [1], .keep 26 [1], .keep 27 [1], .keep 28 [1, 4, 4], .skip 6, .skip 12, .keep 29 [1], .skip 0, .keep 30 [1], .skip 3, .skip 8, .skip 2, .keep 31 [1, 4, 4], .skip 9, .keep 32 [1], .keep 33 [1], .skip 15, .skip 16, .skip 18, .skip 20, .skip 11, .skip 24]

private def edgeIndex : Array (Array ℕ) :=
  #[
    #[0, 1, 2, 3, 4, 5],
    #[6, 7, 8, 9, 8, 7],
    #[10, 11, 10, 12, 12, 13],
    #[14, 15, 14, 16, 17, 16],
    #[18, 8, 10, 12, 12, 19],
    #[16, 7, 20, 13, 21, 7],
    #[14, 8, 14, 22, 23, 24]]

private def maskTable : Array ℕ :=
  #[16417, 40, 48, 16640, 512, 532480, 786432, 16387, 5, 10, 18, 4160, 8320, 28672, 262272, 282624, 524385, 225, 524608, 268, 276, 448, 524355, 195, 12300, 12308, 266252, 266260]

private def separators : Array ℕ :=
  #[629456517700461136719133490825791996606912, 224805899178736040589280162215203920055299, 224805899178736080483832209497966685356164, 629456517700461136832580966879208818096584, 404650618521725016681091662205313001760041, 854262409090744534741828103001595895729779, 854262415581121803655188163639223321742963, 629456517700461136567870189421201874532801, 85754030359986440431941540496083010, 132158622115803366525063485151716303801379, 49048684553950222608288097984907917264004, 269767336284418012275399188937663037452684, 584232150721548499640727764923516458546605, 629456517700461137021180478288987072936397, 315211240274247383976544494754244585933394, 629632147309194523968778391670549555792466, 854262398706140898435822907908217458249331, 314728175692350922757323883090133805931751, 854262402600357362308153759321750821785203, 359689438476492341217503475350462420590856, 359689438513413902889189942049328800604424, 359689438360150736325463437115442726150408, 854262392215764874716057050338626624933491, 314727967838217343220631606146836217437415, 584052704942117535997752012075844385551789, 583930415966505323737481755314446012954029, 131458762136940613569373578737875409259090, 6234851110035259052630655065941869152850]

private def kept : Array (Fin 34) :=
  #[0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 13, 14, 0, 15, 0, 16, 0, 17, 18, 19, 20, 0, 21]

private def origin : Array (RayOrigin 28) :=
  #[.kept 0, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 8, .kept 9, .kept 10, .kept 11, .kept 12, .kept 13, .kept 15, .kept 16, .kept 18, .kept 20, .kept 22, .kept 23, .kept 24, .kept 25, .kept 27, .crossing 4 1, .crossing 4 14, .crossing 4 17, .crossing 4 19, .crossing 4 21, .crossing 4 26, .crossing 5 1, .crossing 5 19, .crossing 7 14, .crossing 10 14, .crossing 10 21, .crossing 13 1]

private def mask (p : Fin 28) : ℕ := maskTable.getD p.val 0

private def separator (p k : Fin 28) : Fin 24 :=
  Fin.ofNat' 24 (((separators.getD p.val 0) >>> (5 * k.val)) % 32)

local instance : NeZero lowerStage3.size := ⟨by decide +kernel⟩
local instance : NeZero lowerStage4.size := ⟨by decide +kernel⟩

def plan : RayCutPlan 28 34 where
  kept p := kept.getD p.val 0
  crossing p k := edges.getD ((edgeIndex.getD (positiveIndex.getD p.val 0) #[]).getD
    (negativeIndex.getD k.val 0) 0) (.skip p)
  origin l := origin.getD l.val (.kept 0)

private abbrev old : Fin 28 → Row := lowerStage3.rays
private abbrev nextRows : Fin 34 → Row := lowerStage4.rays
private abbrev imposed := lowerStage3.imposed

private theorem oldSigns : ∀ p i, i ∈ imposed → zero (old p i) = true ∨ positive (old p i) = true := by
  apply checkRayBlocks (n := 28)
  intro k
  fin_cases k <;> decide +kernel

private theorem mask_eq : ∀ p i, (mask p).testBit i.val =
    (decide (i ∈ imposed) && positive (old p i)) := by
  apply checkRayBlocks (n := 28)
  intro k
  fin_cases k <;> decide +kernel

private theorem separate : ∀ p k, p ≠ k → let i := separator p k
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply checkRayBlocks (n := 28)
  intro k
  fin_cases k <;> decide +kernel

private theorem crossing : ∀ p k, positive (old p 15) = true → negative (old k 15) = true →
    maskCrossing old nextRows imposed 15 mask p k (plan.crossing p k) := by
  apply checkRayBlocks (n := 28)
  intro k
  fin_cases k <;> decide +kernel

theorem valid : plan.Valid old nextRows imposed 15 := by
  obtain ⟨sep, cross⟩ := validateRayMasks plan mask separator oldSigns mask_eq separate crossing
  refine ⟨oldSigns, ?_, ?_, ?_, sep, ?_, cross, ?_⟩ <;> apply checkRayBlocks <;>
    intro k <;> fin_cases k <;> decide +kernel

end LowerCut3

end MOC.RayCoefficients
