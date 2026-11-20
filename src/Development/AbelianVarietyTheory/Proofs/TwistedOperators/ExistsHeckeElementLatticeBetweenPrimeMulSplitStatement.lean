import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementLatticeBetweenPrimeMulSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeElement_lattice_between_prime_mul_split : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ latG V (g * a₀) ⊓ latG V g = M ∧
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  first | exact @GlobalTheory.HeckeLocStep.exists_hecke | exact GlobalTheory.HeckeLocStep.exists_hecke | (intros; apply GlobalTheory.HeckeLocStep.exists_hecke <;> assumption)
