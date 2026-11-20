import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLevelAwayDefiniteUnitaryLevelFromLocalLevels
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevelAway_definiteUnitaryLevelFromLocalLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → IsLevelAway w₀ (GlobalTheory.Cong.AdaptLev.levelOf a w₀ H) := by
  first | (exact @GlobalTheory.Cong.LevAway.isLevelAway_levelOf) | (exact GlobalTheory.Cong.LevAway.isLevelAway_levelOf) | (intros; apply GlobalTheory.Cong.LevAway.isLevelAway_levelOf  <;> assumption)
