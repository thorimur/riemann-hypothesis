import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.Columns.DecoFin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OffIdemDen
open GlobalTheory.IdemSupport

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem conjP_eq_cP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ Q = cP Q :=
  HeightOneSpectrum.ext (Ideal.ext fun _ => Iff.rfl)

def evQ (Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    AE D →+* Q.adicCompletion D.host.E where
  toFun z := Φ z Q
  map_one' := by rw [map_one]; rfl
  map_mul' a b := ev_mul a b Q
  map_zero' := ev_zero Q
  map_add' a b := ev_add a b Q

theorem delta_mem {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)}
    {x : AE D} (h : IsDelta Φ P x) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ x Q ∈ Q.adicCompletionIntegers D.host.E := by
  by_cases hQ : Q = P
  · subst hQ; rw [h.2.1]; exact (Q.adicCompletionIntegers D.host.E).one_mem
  · rw [h.2.2 Q hQ]; exact (Q.adicCompletionIntegers D.host.E).zero_mem

end GlobalTheory.OffIdemDen
