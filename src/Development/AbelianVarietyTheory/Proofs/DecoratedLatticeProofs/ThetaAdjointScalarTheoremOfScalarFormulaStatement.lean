import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAdjointScalarTheoremOfScalarFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaAdjoint_scalar_theorem_of_scalar_formula : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → AForm R.toRealDat R.SF → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') → R.PThmA := by
  first | exact @GlobalTheory.ThmAFromAForm.pThmA_of_aForm | exact GlobalTheory.ThmAFromAForm.pThmA_of_aForm | (intros; apply GlobalTheory.ThmAFromAForm.pThmA_of_aForm <;> assumption)
