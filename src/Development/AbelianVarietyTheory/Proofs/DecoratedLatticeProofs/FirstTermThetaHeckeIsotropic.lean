import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
open scoped ComplexConjugate Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.Exh
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.FirstTermHeckeIso

theorem theta_chart {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A B : HSp D}
    {χ : (AE D)ˣ →* Circle} {om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)}
    {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} {μ : D.host.E} {κ : GA D (dblSp A) ≃* StdUnn.G D A.rank}
    {omS : StdUnn.G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)}
    (P : Pass ψ θ A B χ om ν 𝓨 μ κ omS) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (Φ : schwartzA θ B.rank A.rank) (hΦ : Φ.1 = sch ψ A B ν 𝓨 f)
    (g p : GA D (dblSp A)) (h : GA D B) : StdUnn.theta omS Φ (κ (g * p)) h = thetaKO om g h (om (p, 1) f) := by
  have e : thetaKO om g h (om (p, 1) f) = thetaKO om (g * p) h f := by
    unfold thetaKO
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, StdUnn.thetaKO_eq_tsum_sch D ψ A B χ om P.weil ν 𝓨 P.cov f hf (g * p) h,
    StdUnn.theta, P.trans (g * p) f hf Φ hΦ]

end GlobalTheory.RegSch.FirstTermHeckeIso

end
