import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.BCOffT

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

section Rep

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSpherical_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {K : Subgroup G}
    (h : GlobalTheory.LGrp.IsSpherical ρ K) : GlobalTheory.LGrp.IsSpherical σ K := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨φ x, GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_, fun e => hx0 ?_⟩
  · have e := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g x
    rw [GlobalTheory.LGrp.mem_fixed.1 hx g hg] at e
    exact e.symm
  · exact φ.toLinearEquiv.injective (e.trans (map_zero φ.toLinearEquiv).symm)

end Rep

end GlobalTheory.BCOffT

end
