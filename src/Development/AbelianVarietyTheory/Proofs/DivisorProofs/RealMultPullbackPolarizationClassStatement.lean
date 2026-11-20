import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMultPullbackPolarizationClass

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_mult_pullback_polarization_class : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S) (b : 𝓞 F) (c : 𝔠.elt), GlobalTheory.CechPic.pull (X.rm.act b).left (cls (X.diag c) (pull_isLB (X.isLB c) _)) = cls (X.diag ((b * b) • c)) (pull_isLB (X.isLB _) _) := by
  first | exact @GlobalTheory.RealMult.DiagPull.pull_act_cls_diag | exact GlobalTheory.RealMult.DiagPull.pull_act_cls_diag | (intros; apply GlobalTheory.RealMult.DiagPull.pull_act_cls_diag <;> assumption)
