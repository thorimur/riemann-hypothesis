import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSingleSegmentIsSegmentRepStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegmentStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

noncomputable section

namespace Zz

theorem zblsegsingle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := GlobalTheory.T.langlands_single_segment_is_segment_rep

theorem zbz1core : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := GlobalTheory.T.square_integrable_single_segment

theorem sqInt_isLSeg (hE : GlobalTheory.Published.LanglandsExhaustionGL) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (hS : Zc.LSocleGL k)
    (hC : Zl.CasselmanNecSq k) (hL : Zc.LSegExists k) (δ : IrrGL k) (h1 : 1 ≤ δ.1) (hδ : IsSqIntCoeff δ.rep) :
    ∃ Δ : Segment k, IsLSeg Δ δ.rep := by
  obtain ⟨𝔪, h𝔪⟩ := hE k δ
  have hc := zbz1core k hS hC hL 𝔪 δ.1 δ.rep h1 δ.2.rep.smooth δ.2.rep.irr hδ h𝔪
  obtain ⟨Δ, rfl⟩ := Multiset.card_eq_one.1 hc
  exact ⟨Δ, zblsegsingle k Δ δ.1 δ.rep h𝔪⟩

end Zz

end
