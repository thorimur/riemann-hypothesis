import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevel
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_coprime_of_congr_mul_one_sub_mod_level : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g → ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  first | exact @GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub | exact GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub | (intros; apply GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub <;> assumption)
