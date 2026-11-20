import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ff_descent_elem : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (a : D'), a ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] a →
      ∃ e : D, algebraMap D D' e = a := by
  intro D D' _ _ _ _ a h
  have hx : FlatDescent.amitsurDiff (A := D) D' D (a ⊗ₜ[D] (1 : D)) = 0 := by
    apply (LinearEquiv.lTensor D' (TensorProduct.rid D D')).injective
    simp [FlatDescent.amitsurDiff_tmul, h]
  obtain ⟨m, hm⟩ := ((FlatDescent.amitsur_exact (A := D) (B := D') (M := D)).2 _).1 hx
  refine ⟨m, ?_⟩
  have := congrArg (TensorProduct.rid D D') hm
  simpa [Algebra.algebraMap_eq_smul_one] using this

end GlobalTheory
