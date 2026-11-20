import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeOddMapLe
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_degree_odd_map_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ j : ℕ, (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j + 1)).map R.p ≤
        (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j)).map R.p := by
  first | exact @GlobalTheory.FockParity.map_fockDeg_odd_le | exact GlobalTheory.FockParity.map_fockDeg_odd_le | (intros; apply GlobalTheory.FockParity.map_fockDeg_odd_le <;> assumption)
