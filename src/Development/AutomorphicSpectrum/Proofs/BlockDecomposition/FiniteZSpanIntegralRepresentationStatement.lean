import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteZSpanIntegralRepresentation
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_z_span_integral_representation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
      (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure],
      ∃ κ : AutomorphicForm.archGroup E a → ℂ, Continuous κ ∧ HasCompactSupport κ ∧
        ∀ g : GA E a, φ.1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * κ y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.GrowthKernel.exists_kernel_of_finite | exact GlobalTheory.CompanionTheory.HCRep.GrowthKernel.exists_kernel_of_finite | (intros; apply GlobalTheory.CompanionTheory.HCRep.GrowthKernel.exists_kernel_of_finite <;> assumption)
