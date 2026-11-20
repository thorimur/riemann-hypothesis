import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.flat_B : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  intro R _ _ i
  haveI : Module.Flat i.A i.B := IsLocalization.flat i.B i.q.primeCompl
  exact Module.Flat.trans R i.A i.B

end GlobalTheory.Henselisation
