import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.VolStabFromSWW

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

def OrbProper : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K →
    IsCompact ((fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0) ⁻¹' K)

end PI.VolStabW
