import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalVacuumFixedByMaximalCompact
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_vacuum_fixed_by_maximal_compact : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W B.v₁, Acts (evFin F B.v₁) (om' (1, k)) (G.M'.vac B.v₁) (G.M'.vac B.v₁) := by
  first | exact @GlobalTheory.SplitVacFixRight.vac_fixed_good | exact GlobalTheory.SplitVacFixRight.vac_fixed_good | (intros; apply GlobalTheory.SplitVacFixRight.vac_fixed_good <;> assumption)
