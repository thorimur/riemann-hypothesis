import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorFrobeniusSemisimplification
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_frobeniusSemisimplification : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {ρ : ↥(Weil h) → Module.End ℂ V} {N : Module.End ℂ V} {a : WDRep h V} {ρ' : ↥(Weil h) → Module.End ℂ V'} {N' : Module.End ℂ V'} {b : WDRep h V'}, IsFrobSS ρ N a → IsFrobSS ρ' N' b → IsFrobSS (fun g => TensorProduct.map (ρ g) (ρ' g)) (N.rTensor V' + N'.lTensor V) (a.tensor b) := by
  first | exact @GlobalTheory.WeilDeligne.IsFrobSS.tensor | exact GlobalTheory.WeilDeligne.IsFrobSS.tensor | (intros; apply GlobalTheory.WeilDeligne.IsFrobSS.tensor <;> assumption)
