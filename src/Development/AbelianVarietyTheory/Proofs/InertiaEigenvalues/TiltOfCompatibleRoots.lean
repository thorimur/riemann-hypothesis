import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem tilt_of_compatible_roots : ∀ (l : ℕ) [Fact l.Prime] (s : ℕ → OC l),
    (∀ n, s (n + 1) ^ l = s n) → ∃ y : OCb l, ∀ n, GlobalTheory.MemLoc.rootT y n = s n := by
  intro l _ s hs
  exact (GlobalTheory.MemLoc.tilt_facts l).1 s hs

end GlobalTheory
