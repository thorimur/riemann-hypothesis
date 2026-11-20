import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ i : ℕ, IsSelfDualC V (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) ∧ (∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) ∧ ∀ 𝔪 : Ideal (𝓞 D.host.E), congLev D.sp.cm V.gram (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) 𝔪 = congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual | exact GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual | (intros; apply GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual <;> assumption)
