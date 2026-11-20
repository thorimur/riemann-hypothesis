import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroLocusLeOpenPolarisationComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzeroLocus_le_open_polarisation_complex : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (O : P₀.A.left.Opens) (y : P₀.A.left), y ∈ O → ∃ (n : ℕ) (σ : (lbPow P₀.L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ O := by
  first | exact @GlobalTheory.exists_nonzeroLocus_le | exact GlobalTheory.exists_nonzeroLocus_le | (intros; apply GlobalTheory.exists_nonzeroLocus_le <;> assumption)
