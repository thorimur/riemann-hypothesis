import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnifStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem rank_eq_unif_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (M : LB A.left) (g : ℕ) (u : HolUnif A M g), IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → D.g = g := by
  intro E _ _ _ H L _ _ D σ A _ φ M g u hp h1 h2
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  obtain ⟨Mσ, -⟩ := GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre (Sp (𝓞 L)) D.t.G L (𝟙 _) D.B.carrier D.MB σ
  have hp' : IsGrpPullback A D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) φ := by
    rwa [Category.comp_id]
  obtain ⟨e, -⟩ := GlobalTheory.T.tangent_space_equiv_hol_unif _ D.t.G _ _ Mσ A φ M g u hp' h1 h2
  have hf : Module.finrank ℂ (Fibre σ D.B.carrier) = g := by
    rw [e.finrank_eq, Module.finrank_fin_fun]
  have hr : Module.finrank ℂ (FibreSpace D.B.metric σ) = Module.finrank (𝓞 L) D.B.carrier :=
    GroundTheory.Heights₂.Heights.FibreMahlerForms.finrank_fibreSpace D.B.metric σ
  have hq : Module.finrank ℂ (FibreSpace D.B.metric σ) = Module.finrank ℂ (Fibre σ D.B.carrier) :=
    (FibreSpace.equiv D.B.metric σ).symm.finrank_eq
  change Module.finrank (𝓞 L) D.B.carrier = g
  rw [← hr, hq, hf]

end GlobalTheory.CompanionTheory.Ar.Sl
