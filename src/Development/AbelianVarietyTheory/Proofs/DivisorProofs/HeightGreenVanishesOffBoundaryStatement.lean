import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightGreenVanishesOffBoundary
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_green_vanishes_off_boundary : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N)
    (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∉ offBd O.Φ c σ → GlobalTheory.HeightParts.psi O x c σ τ i y = 0 := by
  first | exact @GlobalTheory.HeightParts.zero_psi_of_not_mem_offBd | exact GlobalTheory.HeightParts.zero_psi_of_not_mem_offBd | (intros; apply GlobalTheory.HeightParts.zero_psi_of_not_mem_offBd <;> assumption)
