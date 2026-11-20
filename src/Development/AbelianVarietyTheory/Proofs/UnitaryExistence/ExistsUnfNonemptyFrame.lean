import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyFrPtComplex
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory

theorem exists_unf_nonempty_frame : N1c → Out.SecTwistSt → ∀ (D : D7) (Q : Par D), (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → Nonempty (Data D.host.E D.R.r) → ∀ j (σ : Q.c.F →+* ℂ), ∃ U : Unf (Q.Xo j) Q.c σ D.R.r, Nonempty (Σ k, Frame (U.X k).Ψ D.R.r) := by
  intro hN hT D Q h hX j σ
  obtain ⟨X⟩ := hX
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex hN hT _ _ (Q.Dw j) _ (Q.Xo j) Q.c (h j) σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨⟨(), fun _ => 0⟩⟩⟩

end GlobalTheory
