import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Kr

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ValuativeRel

variable {F : Type} [Field F]

def S0 (O : Subring F) (ϖ : F) (r d c : ℕ) : Set (Matrix (Fin (r + d)) (Fin (r + c)) F) :=
  {x | bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c}

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

end CompanionTheory.D.Upq.DoubleCosetLemmas.Kr

end
