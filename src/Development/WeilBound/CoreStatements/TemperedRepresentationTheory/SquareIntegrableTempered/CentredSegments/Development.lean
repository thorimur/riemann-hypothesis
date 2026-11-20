import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableOfHeckeSpectralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentredSegmentSquareIntegrableStatement

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace Zls.FreeSingleHomotopyEquivDiscreteChains

theorem sspectral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → Zls.MaxExpStrict π → Zls.HeckeSpectral π := by
  exact GlobalTheory.T.hecke_spectral_of_strict_exponent

theorem ssqint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π → Zls.HeckeSpectral π → IsSqIntCoeff π := by
  exact GlobalTheory.T.square_integrable_of_hecke_spectral

theorem casselmanSuffSq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) : Zls.CasselmanSuffSq k := by
  intro N V _ _ π _ hs hi hu he
  exact ssqint k N V π hs hi (hA k N V π hs hi) hu (sspectral k N V π hs hi hA hF he)

theorem sseglink : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  exact GlobalTheory.T.centred_segment_square_integrable

theorem centredSegSqInt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) (hJ : Zc.LSegJacquet k) :
    Zz.CentredSegSqInt k :=
  sseglink k (casselmanSuffSq k hA hF) hA hJ

end Zls.FreeSingleHomotopyEquivDiscreteChains

end
