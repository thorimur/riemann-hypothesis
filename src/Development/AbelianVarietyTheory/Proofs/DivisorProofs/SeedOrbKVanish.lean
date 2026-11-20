import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open MeasureTheory Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace GlobalTheory.TorusElementPower

theorem torusElt_pow_eq {k : Type} [Field k] {N : ℕ} (ϖ : kˣ) (ν : Fin N → ℤ) (m : ℕ) :
    GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν ^ m = GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (fun a => (m : ℤ) * ν a) := by
  unfold GlobalTheory.GLDoubling.torusElt
  rw [← map_pow]
  congr 1
  funext a
  simp only [Pi.pow_apply, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]

end GlobalTheory.TorusElementPower
