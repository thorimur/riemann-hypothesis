import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
import Development.AutomorphicArithmetic.BlochKatoExtensions.CardJumps

theorem GlobalTheory.PhtCompare.phtCmp : GlobalTheory.HeightCounting.PhtCmp := fun D _ T Wd =>
  ⟨fun l _ ι a r τ w hr hτ hd => UpperTheory.Prune.card_jumps D T Wd l ι a r τ w hr hτ hd⟩
