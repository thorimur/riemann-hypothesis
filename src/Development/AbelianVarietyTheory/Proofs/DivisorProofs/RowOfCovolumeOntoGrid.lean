import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Formalism.LocalToGlobal.Divisibility.TupUsed
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.FourBoundsAtBundles

theorem tupAllUsed_part {D : D7} {O : Obj D} {c : ℝ} (b : Ind.Part D O c) : Formalism.L2.DIV.TupAllUsed b.P := by
  intro t
  rcases b.pt.charW.tup.mu_used t with h | ⟨w, hw⟩
  · left
    subst h
    exact b.P.tied.div.tup.mu0
  · right
    refine ⟨D.plEq.symm w, ?_⟩
    have e1 := b.pt.tupAt (D.plEq.symm w)
    rw [Equiv.apply_symm_apply] at e1
    have e2 := b.pt.tupTie (D.what₂.muAt (D.plEq.symm w)) (Or.inr ⟨_, rfl⟩)
    rw [e1, hw] at e2
    exact e2

theorem pDiv_of {D : D7} {O : Obj D} {c : ℝ} (b : Ind.Part D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : Ind.PDiv D O c b :=
  Formalism.L2.DIV.DivRows3G.toRows (tupAllUsed_part b)
    ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩

end GlobalTheory.Fc.FourBoundsAtBundles

namespace GlobalTheory.Fc.FourBoundsAtBundles

open GlobalTheory.Fc.R1

theorem evW_of_atAll {Bd : BdT} {q : BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} (h : AtAll q 𝒜 σ) : Ind.EvW q 𝒜 σ :=
  Closed.of_all fun Fm _ hc => Ind.ev_of_atAll h Fm (w3_a hc)

end GlobalTheory.Fc.FourBoundsAtBundles
