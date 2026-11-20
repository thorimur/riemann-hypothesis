import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
open NumberField Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraicHeckeCharOfWeight_of_integer_expo : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) (n : (E →+* ℂ) → ℤ), (∀ τ, expo χ τ = n τ) → IsAlgPos χ n := by
  first | exact @GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo | exact GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo | (intros; apply GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo <;> assumption)
