import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

theorem lbIso_lbPow_hecke {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) (k : ℕ) :
    LBIso (lbPow P k) ((Hecke.lbPow P k).pull (𝟙 X)) := by
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have h₁ : LBIso (lbPow P k) (Hecke.lbPow P k) := by
    unfold Hecke.lbPow lbPow
    refine (GlobalTheory.PrimNorm.lbIso_iff hP _ _ _ _).2 ?_
    simp
  exact h₁.trans (LB.isLB_linComb hP _ _) hQ (pull_isLB hQ _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hQ).symm

theorem weilIs_of_hecke_lbPow {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {P : LB A.left} (hP : P.IsLB) (k : ℕ) {T : Over S} {X Y : T ⟶ A} {u : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A (Hecke.lbPow P k) 1 X Y u) : Out.WeilIs A P k X Y u := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have := (GlobalTheory.weilIs_along_hom hG S A A (𝟙 _) P (Hecke.lbPow P k) k 1 T X Y u u hA hA hP hQ inferInstance
    (lbIso_lbPow_hecke hP k) (by simpa using h)).1
  simpa using this

end GlobalTheory.BiextPairing

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

end GlobalTheory.BiextPairing
