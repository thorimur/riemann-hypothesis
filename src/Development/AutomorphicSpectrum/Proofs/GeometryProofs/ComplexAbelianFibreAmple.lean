import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FibrePol

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem exists_fibre_pol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' D.t (emb σ)), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  intro E _ _ _ H L _ _ D σ
  have hC := Out.CubePf.cubePull
  let m₁ := PullbackSections.sabM hC (spMap σ) D.tK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ D.m m₁
  have e : spMap σ ≫ spMap (algebraMap (𝓞 L) L) = emb σ := by
    simp only [emb, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨w, hw, -⟩ := m₁.lin
  refine ⟨PullbackSections.sabT hC (spMap σ) D.tK, e ▸ n, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsProper) m₁.cart.1 D.princ.1
  · exact relAmple_pull m₁.cart.1 D.tK.PP.isLB (PullbackSections.sabT hC (spMap σ) D.tK).PP.isLB ((isGen_iff w).1 hw) ⊤
      (isAffineOpen_top _) (fun _ => trivial) D.princ.2.1

end GlobalTheory.CompanionTheory.Ar.Sl.FibrePol
