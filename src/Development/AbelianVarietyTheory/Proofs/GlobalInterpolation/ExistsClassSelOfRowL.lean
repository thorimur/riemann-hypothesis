import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem isSel_of_sAnd {Bd : BdT} {Q R : V4.Slot} {Lk : LkT Bd} {E : Par → BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜}
    (s : IsSel (sAnd Q R) Lk E 𝒜 σ) : IsSel Q Lk E 𝒜 σ := fun Fm hc => by
  obtain ⟨κ, h1, h2, h3⟩ := s Fm hc
  refine ⟨κ, h1, h2, fun x hx i => ⟨?_, (h3 x hx i).2⟩⟩
  obtain ⟨K, β, b, a0, a1, a2, a3⟩ := (h3 x hx i).1
  exact ⟨K, β, b, a0, a1.1, a2, a3⟩

end GlobalTheory.Fc
