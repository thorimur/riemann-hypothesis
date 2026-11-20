import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointPreservesHeckeEigenvectorsMatche
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftAdjoint_preserves_heckeEigenvectors_matchedPair : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (cX c0 : List ℤ →₀ ℂ), GlobalTheory.Hk3.MatchE R t P cX c0 → ∀ (x : R.HE.H) (l : ℂ), h P c0 x = l • x → h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
  first | exact @GlobalTheory.Hk3.SysE.matched_keeps_eigen | exact GlobalTheory.Hk3.SysE.matched_keeps_eigen | (intros; apply GlobalTheory.Hk3.SysE.matched_keeps_eigen <;> assumption)
