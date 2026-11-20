import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.GramOneCompact

theorem isCompact_GinfC_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  intro D V hg
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.Ker.CongTop.exists_compact V _ hL.1 hL.2
  refine hC.of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) fun k hk => hCm k ?_ (Or.inr hg)
  have hk1 : finHom V k = 1 := hk
  have h1 : GlobalTheory.Ker.fmt V k = GlobalTheory.Ker.fmt V 1 := by
    rw [GlobalTheory.Ker.CongTop.fmt_eq, GlobalTheory.Ker.CongTop.fmt_eq, hk1, map_one]
  rw [h1]
  exact (GlobalTheory.Ker.CongTop.congSub V (GlobalTheory.SW.stdL D.host.E V.rank) 1).one_mem.1

end GlobalTheory.GramOneCompact
