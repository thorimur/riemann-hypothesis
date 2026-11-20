import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.VB GlobalTheory.ChainPts

namespace GlobalTheory.TanSec

theorem bijective_xAll {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) : Function.Bijective (xAll S) := by
  have hg : Function.Bijective (letters S.Dw).get :=
    ⟨List.nodup_iff_injective_get.1 (GlobalTheory.Proof.LetterConjugation.nodup_letters _),
      fun x => List.get_of_mem (GlobalTheory.Proof.LetterConjugation.mem_letters _ x)⟩
  exact hg.comp (finCongr (length_letters S).symm).bijective

example {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) (h : Nonempty (Letter S.Dw)) : 0 < D.R.f * N :=
  Fin.pos_iff_nonempty.2 ((bijective_xAll S).2 h.some).nonempty

end GlobalTheory.TanSec
