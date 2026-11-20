import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeXiMulDpowSuccStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPowStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open DividedPowers

namespace CrystallineSemistableComparison.Pb.Lat

section Lat
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem ξ_dpE (hl : l ≠ 0) (i : ℕ) : f ξ * dpE f ξ l M i = ((l : B) ^ M * ((i : B) + 1)) * dpE f ξ l M (i + 1) :=
  GlobalTheory.T.lattice_xi_mul_dpow_succ f ξ l M hl i

theorem pdP_B (r : ℕ) : pdP (γB f ξ) r = Ideal.span {f ξ ^ r} := GlobalTheory.T.divided_power_filtration_span_pow f ξ r

theorem dp_ι (hc : DPClosed (ι f ξ l M) (γB f ξ)) : IsDPMorphism (γ f ξ l M hc) (γB f ξ) (ι f ξ l M) :=
  ⟨Ideal.map_le_iff_le_comap.2 fun _ hx => hx, fun {n} a ha => (ι_γ f ξ l M hc ha).symm⟩

end Lat

section Map
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

end Map

end CrystallineSemistableComparison.Pb.Lat
