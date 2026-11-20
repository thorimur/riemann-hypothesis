import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightAndFlatExponentSizeBound
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
theorem _root_.GlobalTheory.T.thetaWeight_and_flatExponent_size_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (la : AllWt.Weight Dw) (n₀ : Psi H → ℤ) (hp : 1 ≤ Dw.p), laOf Dw a n = la + GlobalTheory.FlatLine.parWt Dw n₀ → (∀ τ, n₀ τ = 1 + ((n / 2 : ℕ) : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) → sizeK Dw a n ≤ (1 + ((Dw.p + Dw.q : ℕ) : ℝ)) * ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) ∧ ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
  first | exact @GlobalTheory.spanShortSize | exact GlobalTheory.spanShortSize | (intros; apply GlobalTheory.spanShortSize <;> assumption)
