import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvr
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | exact GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | (intros; apply GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic <;> assumption)
