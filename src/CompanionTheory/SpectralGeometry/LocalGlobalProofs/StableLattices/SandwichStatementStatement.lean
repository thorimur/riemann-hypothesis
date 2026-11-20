import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SandwichStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SandwichStatement : StSandwich := by
  first | exact @GlobalTheory.CompanionTheory.Lattice.stSandwich | exact GlobalTheory.CompanionTheory.Lattice.stSandwich | (intros; apply GlobalTheory.CompanionTheory.Lattice.stSandwich <;> assumption)
