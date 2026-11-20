import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSpaceTransposeInverse
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_space_transpose_inverse : ∀ V : Submodule ℂ (G3 → ℂ), WhA V → WhA (tV V) := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV.whA_tV | exact GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV.whA_tV | (intros; apply GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV.whA_tV <;> assumption)
