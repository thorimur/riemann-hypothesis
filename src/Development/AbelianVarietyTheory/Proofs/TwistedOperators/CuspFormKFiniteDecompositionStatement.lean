import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_K_finite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → (∀ τ, GlobalTheory.CuspKFin.KFinAt θ N τ ψ) → ∀ (μ : Measure (GA D N.V)) (𝓕 : Set (GA D N.V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ N.V) 𝓕 μ → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ N.M {k | k ∈ U ∧ k ∈ GfC N.V} 1 μ 𝓕 (T₀ j)) ∧ ψ = ∑ j, T₀ j (u j) := by
  first | exact @GlobalTheory.KFinDecomp.cuspKFin_decomp | exact GlobalTheory.KFinDecomp.cuspKFin_decomp | (intros; apply GlobalTheory.KFinDecomp.cuspKFin_decomp <;> assumption)
