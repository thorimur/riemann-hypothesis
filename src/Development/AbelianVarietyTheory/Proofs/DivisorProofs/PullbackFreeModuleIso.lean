import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

theorem GlobalTheory.pullback_freeModule_iso_free : ∀ (S T : Scheme.{0}) (f : S ⟶ T) (n : ℕ), Nonempty ((Scheme.Modules.pullback f).obj (GlobalTheory.QCoh.freeModule (X := T) (Fin n)) ≅ GlobalTheory.QCoh.freeModule (X := S) (Fin n)) := by
  intro S T f n
  exact ⟨((VB.isFrame_freeFrame T (Fin n)).pullback f).iso (VB.isFrame_freeFrame S (Fin n))⟩
