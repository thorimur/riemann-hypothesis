import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMulPf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem deepSubMul_rec_all : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), EtaleWeightGaps.DeepSubMul (recPJ h j hj) ∧ EtaleWeightGaps.DeepSubMul (recPlus h j hj) ∧ ∀ (j' : ℕ) (ka : WeightFamilies.Wt D j') (Nt : NetData (recB h.toLawsCore) j' ka) (hM : NetMax Nt) (hL : NetLeSup Nt), EtaleWeightGaps.DeepSubMul (B := Nt.Bp hM hL) (PJ.tol2NormAlt _ _ _ _ _ _ (recPlus h j hj)) := by
  intro D T h j hj
  have h0 : EtaleWeightGaps.DeepSubMul (recPJ h j hj) := recSubMul D T h j hj
  have h1 : EtaleWeightGaps.DeepSubMul (recPlus h j hj) := h0
  exact ⟨h0, h1, fun j' ka Nt hM hL => h1⟩

end GlobalTheory
