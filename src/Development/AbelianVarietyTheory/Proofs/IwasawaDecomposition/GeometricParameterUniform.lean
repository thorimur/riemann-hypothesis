import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EtaSizeRecursionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivisionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsEOfHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZetaUniformOfExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLanglandsPrmReductionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

theorem exBL_isLinked_prmR : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → PositionMv p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (IsLinked p) := by
  intro hG hCov hHM hCW hW hD hH hC hA hWb hRF hL N Γ p hp hN hS hM
  have hz := GlobalTheory.T.zeta_uniform_of_extension ⟨hCov, hHM, hCW, hH, hC⟩ hL N SExt.none Γ hN
  subst hp
  refine GlobalTheory.T.eta_size_recursion hA hWb hRF hL _ ?_ ?_ ?_
  · exact witExE_of_witMv _ (GlobalTheory.T.witnesses_pass_along_set_division _ hS)
  · exact GlobalTheory.Fc.EvP.of_all fun _ K _ q => hz K q
  · exact GlobalTheory.T.local_langlands_prm_reduction hG hCov hHM hCW hW hD hH hC hA hRF hL N Γ _ rfl hN hM

end GlobalTheory.Mem.Top.Bl

end
