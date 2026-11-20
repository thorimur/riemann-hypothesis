import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijectiveStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct ENNReal NNReal ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinkCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuasiFamilyPeriods (conjTr JacobiConj PeriodsAgree PeriodLink PeriodLinkQuasi)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
  {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}

def kapHom (hL : IsLineVec L' ζ') (l : Link B L' ζ') (S : HSp D) : WO S L' →+ WO B.L S :=
  AddMonoidHom.mk' (l.κ S)
    (GlobalTheory.T.hermitianLinkMap_additive_rational_equivariant D B.L L' S l.τ 1 (GlobalTheory.T.besselLineLink_gram_similitude_bijective D ρ B L' ζ' hL l).1 (l.κ S) (fun _ => rfl)).1

def form (s : StepBF ψ B J) (φ : GA D B.A → ℂ) (F : WO B.V₀ J.W₀ → ℂ) : ℂ :=
  ∫ h₀ in B.vA.𝓕, φ h₀ * s.om₀ (B.o.emb (h₀, 1), 1) F 0 ∂B.vA.μ

def iota (hL : IsLineVec L' ζ') (l : Link B L' ζ') (S : HSp D) : WO S L' →+ WO B.V₀ S :=
  (B.o.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (kapHom hL l S))

theorem heisO_heisO (S T : HSp D) (x y : WO S T) (F : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y F) = ψ (symplOH S T x y) • heisO ψ S T (x + y) F := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_left,
    AddChar.map_add_eq_mul, add_assoc]
  ring

end GlobalTheory.LinkCompare

end
