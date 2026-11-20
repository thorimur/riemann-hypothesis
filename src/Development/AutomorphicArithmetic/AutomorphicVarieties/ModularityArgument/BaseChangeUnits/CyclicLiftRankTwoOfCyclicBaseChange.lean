import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadLiftRealToComplexOfBaseChange

open NumberField Formalism.GaloisCohomology UpperTheory.Top

namespace UpperTheory.V.Z.Bc

open UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.HV UpperTheory.V.Lit

instance : Coe DescQ ImagQuadraticDescentGL2 := ⟨imagQuadDescent_of_descentQ⟩

structure HypothesesB : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  descU : Z.Desc.DescWeak
  cyc : CycC
  desc2 : ImagQuadraticDescentGL2
  lift2 : QuadBC2

theorem cyclicLiftRankTwo_of_cyclic_base_change (h : CycC) : CyclicBaseChangeLiftRankTwo := by
  intro F E _ _ hF _ _ hE _ _ hp π hr
  rcases (h F E hp hF 2 one_le_two).1 _ _ (Or.inl ⟨hF, π, rfl, rfl⟩)
    (fun τ => ⟨_, GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (GlobalTheory.CuspRep.CG.mk π) τ, hr τ⟩) with h1 | ⟨sat', inf', hc, hw, hi⟩
  · exact Or.inl h1
  · rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hR, -⟩
    · exact Or.inr ⟨P, hi, hw⟩
    · obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
      exact absurd (hR.isReal v) (InfinitePlace.not_isReal_iff_isComplex.2 (hE.isComplex v))

end UpperTheory.V.Z.Bc
