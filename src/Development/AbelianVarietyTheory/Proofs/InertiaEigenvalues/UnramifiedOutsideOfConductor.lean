import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import GroundTheory.AutomorphicForms.AdelicGLn

noncomputable section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ GlobalTheory.ZEul Filter Topology Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.ZEul

open GlobalTheory.CuspRep.CuspidalL2GL in

theorem exists_fundamentalDomain_NE : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (GA E n)) [μ.IsHaarMeasure],
  ∃ 𝓕₀ : Set (GA E n), IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕₀ μ := by
  intro E _ _ n μ _
  haveI := CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := CuspidalL2GL.t2Space_GA E n
  haveI := CuspidalL2GL.secondCountableTopology_GA E n
  haveI : DiscreteTopology (ratGL E n).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n
  have hsub : (GlobalTheory.CellDec.NE E n : Set (GA E n)) ⊆ ((ratGL E n).range : Set (GA E n)) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  haveI : DiscreteTopology (GlobalTheory.CellDec.NE E n) := DiscreteTopology.of_subset (inferInstance : DiscreteTopology ((ratGL E n).range : Set (GA E n))) hsub
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GlobalTheory.CellDec.NE E n)
  exact ⟨𝓕, h𝓕 _⟩

end GlobalTheory.ZEul
