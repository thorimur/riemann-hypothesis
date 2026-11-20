import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryConjugateMatrixFamily
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChowHt GlobalTheory.CompHt
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_conjugate_matrix_family : ∀ (K : Type) [Field K] (N n : ℕ) (g : Matrix (Fin N) (Fin n) K) (M : Matrix (Fin n) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), N ≤ n → M.det ≠ 0 →
    g * M = (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0) → (∀ σ, (A σ).det ≠ 0) →
    (∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) →
    ∃ A' : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, (A' σ).det ≠ 0) ∧
      (∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, A' ((starRingEnd ℂ).comp σ) = (A' σ).map (starRingEnd ℂ) * U) ∧
      ∀ σ : K →+* ℂ, g.map σ * A' σ = A σ * (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) := by
  first | exact @GlobalTheory.exists_frames_extend | exact GlobalTheory.exists_frames_extend | (intros; apply GlobalTheory.exists_frames_extend <;> assumption)
