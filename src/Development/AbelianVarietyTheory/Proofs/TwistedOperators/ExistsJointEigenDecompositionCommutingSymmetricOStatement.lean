import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsJointEigenDecompositionCommutingSymmetricO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointEigenDecomposition_commuting_symmetricOps : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (Z : Submodule ℂ E), FiniteDimensional ℂ Z →
    (∀ i, ∀ x ∈ Z, F i x ∈ Z) → (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ Z, F i (a • x) = a • F i x) → (∀ i j, ∀ x ∈ Z, F i (F j x) = F j (F i x)) →
    ∀ b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ, (∀ x ∈ Z, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ Z, ∀ y ∈ Z, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, b x (F i y) = b (F i x) y) →
    ∃ C : Finset (ι → ℂ), ∀ x ∈ Z, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h} := by
  first | exact @GlobalTheory.JointSpectral.exists_finset_joint_eigen | exact GlobalTheory.JointSpectral.exists_finset_joint_eigen | (intros; apply GlobalTheory.JointSpectral.exists_finset_joint_eigen <;> assumption)
