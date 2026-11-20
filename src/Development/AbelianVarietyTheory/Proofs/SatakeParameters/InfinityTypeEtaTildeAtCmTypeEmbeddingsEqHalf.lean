import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

namespace GlobalTheory.EtaInfType

theorem main : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), NCharTied D cf C tp → ∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)} := by
  intro D cf C tp N t
  have hI : (N.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) := by
    rw [N.etaT]
    exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
  have h1 := (N.infG _ _ hI (D.eTau t)).1
  have e0 : Formalism.L2.embT D t = embPsi D.host (D.eTau t) := rfl
  rw [e0, h1]
  push_cast
  rfl

end GlobalTheory.EtaInfType
