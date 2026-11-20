import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBesselCoreMatrixEqBlockDiagonalOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_besselCore_matrix_eq_blockDiagonal_one : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (β : GlobalTheory.FinPl.Frame p B.A n) (β₀ : GlobalTheory.FinPl.Frame p B.V₀ (n ⊕ Fin 1)), GlobalTheory.FinPl.IsSumFrame B.o B.ζ β β₀ → ∀ (κ : GA D B.A) (g : GL n k), (mt B.A κ).map p.pr = β.b * g.val * β.b' → (mt B.V₀ (B.o.emb (κ, 1))).map p.pr = β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by
  first | exact @GlobalTheory.FinPl.CoreMat.coreMat | exact GlobalTheory.FinPl.CoreMat.coreMat | (intros; apply GlobalTheory.FinPl.CoreMat.coreMat <;> assumption)
