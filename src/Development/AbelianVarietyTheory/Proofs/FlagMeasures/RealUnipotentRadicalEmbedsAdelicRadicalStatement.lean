import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentRadicalEmbedsAdelicRadical
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realUnipotentRadical_embeds_adelicRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F), I.IsIsot W → ∃ Wv : Submodule ℂ (Fin I.n → ℂ), IsIsoC (I.ε v) Wv ∧ ∀ m ∈ NW (I.ε v) Wv, (open Classical in ((Pi.mulSingle v m, 1) : I.GA)) ∈ I.NA W := by
  first | exact @GlobalTheory.RadEmb.radical_embeds | exact GlobalTheory.RadEmb.radical_embeds | (intros; apply GlobalTheory.RadEmb.radical_embeds <;> assumption)
