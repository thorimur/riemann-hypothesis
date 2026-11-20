import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspMultiplicityMemSphericalEigenPartOfValuePara
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspMultiplicity_mem_sphericalEigenPart_of_value_params : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → ForStage D fun c _ s => ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e := by
  first | exact @GlobalTheory.EvenOnto.ValPart.valPart_mem | exact GlobalTheory.EvenOnto.ValPart.valPart_mem | (intros; apply GlobalTheory.EvenOnto.ValPart.valPart_mem <;> assumption)
