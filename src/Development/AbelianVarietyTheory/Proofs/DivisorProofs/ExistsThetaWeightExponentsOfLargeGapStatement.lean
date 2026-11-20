import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWeightExponentsOfLargeGap
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaWeight_exponents_of_large_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (m : ℕ) (la : AllWt.Weight Dw) (hp : 1 ≤ Dw.p), (∀ τ, Antitone (la τ)) → (∀ τ, ((2 * m + 2 : ℕ) : ℤ) ≤ gap (la τ) (Dw.p - 1)) → ∃ a : (E →+* ℂ) × ℕ → ℕ, Dom a (2 * m) ∧ laOf Dw a (2 * m) = la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) ∧ ∀ (τ : Psi H) (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → (((2 * m) / 2 : ℕ) : ℤ) < laOf Dw a (2 * m) τ k := by
  first | exact @GlobalTheory.ThetaWtGap.exists_exponents | exact GlobalTheory.ThetaWtGap.exists_exponents | (intros; apply GlobalTheory.ThetaWtGap.exists_exponents <;> assumption)
