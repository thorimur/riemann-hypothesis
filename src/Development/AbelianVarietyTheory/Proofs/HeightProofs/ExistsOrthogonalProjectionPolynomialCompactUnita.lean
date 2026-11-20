import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

theorem exists_orthProj_polyV {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (p : KG ε → ℂ) (hp : Continuous p) :
    ∃ p' ∈ GlobalTheory.KFourier.polyV ε d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d,
      ∫ k, star (q k) * (p k - p' k) ∂(muK ε) = 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV
  | exact _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV
  | (apply _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV ..)

end GlobalTheory.KFourier

end
