import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJointHighestWeightHarmonicSliceOuterVariables
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isJointHighestWeightHarmonic_slice_outer_variables : ∀ {σ σ₀ : Type} [DecidableEq σ] (ι : σ₀ → σ), Function.Injective ι → ∀ {k l N : ℕ} (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ) (α : Fin k → ℂ) (β : Fin l → ℂ) (P : MvPolynomial σ ℂ), GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P → ∃ (s : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → MvPolynomial σ₀ ℂ) (g : (σ →₀ ℕ) → MvPolynomial σ ℂ), P = ∑ i ∈ s, MvPolynomial.rename ι (f i) * g i ∧ (∀ i ∈ s, GlobalTheory.CompactHarm.JointTop z y κ α β (f i)) ∧ ∀ i ∈ s, ∀ v ∈ (g i).vars, v ∉ Set.range ι := by
  first | exact @GlobalTheory.jointTop_slice | exact GlobalTheory.jointTop_slice | (intros; apply GlobalTheory.jointTop_slice <;> assumption)
