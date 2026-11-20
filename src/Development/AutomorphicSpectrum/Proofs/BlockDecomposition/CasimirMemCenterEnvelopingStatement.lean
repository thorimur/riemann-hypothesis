import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_mem_center_enveloping : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  first | exact @GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | exact GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | (intros; apply GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg <;> assumption)
