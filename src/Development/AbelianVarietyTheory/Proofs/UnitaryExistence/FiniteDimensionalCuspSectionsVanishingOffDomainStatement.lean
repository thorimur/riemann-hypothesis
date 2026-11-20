import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalCuspSectionsVanishingOffDomain
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_cuspSections_vanishing_offDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (W : Submodule ℂ (FDSec X)), W ≤ holSub X la → (∀ P ∈ W, ∀ k, ∀ x ∉ (X k).dom, P k x = 0) → FiniteDimensional ℂ W := by
  first | exact @GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub | exact GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub | (intros; apply GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub <;> assumption)
