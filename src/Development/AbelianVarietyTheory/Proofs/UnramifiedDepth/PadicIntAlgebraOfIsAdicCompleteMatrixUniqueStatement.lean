import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicIntAlgebraOfIsAdicCompleteMatrixUnique
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_algebra_of_isAdicComplete_matrix_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O], Nonempty (Algebra ℤ_[p] O) ∧ ∀ [Algebra ℤ_[p] O] (n : ℕ) (f : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]), f c = algebraMap ℤ_[p] O c • (1 : Matrix (Fin n) (Fin n) O) := by
  first | exact @GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique | exact GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique | (intros; apply GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique <;> assumption)
