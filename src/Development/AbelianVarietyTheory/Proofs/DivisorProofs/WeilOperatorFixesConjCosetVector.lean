import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormUniq

theorem conj_smul_conj_smul {D : D7} (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => GlobalTheory.NormSum.VacMove.conj_conj D x
  rw [smul_smul, h, one_smul]

end GlobalTheory.FunObj.NormUniq
