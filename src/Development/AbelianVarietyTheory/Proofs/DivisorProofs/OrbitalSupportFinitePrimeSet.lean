import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [CommRing K] [Algebra ℚ K]
    (x : K ⊗[ℚ] G.C) : (starT G.star K (starT G.star K x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

end GlobalTheory.FinClsLoc
