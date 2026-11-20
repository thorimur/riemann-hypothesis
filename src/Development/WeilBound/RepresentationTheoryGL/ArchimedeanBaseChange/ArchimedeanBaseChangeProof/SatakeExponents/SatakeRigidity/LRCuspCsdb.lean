import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig.B

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev nu (E : Type) [Field E] [NumberField E] (s : ℝ) : Formalism.L2.Host.HChar E := GlobalTheory.CuspRep.Model.absC E (s : ℂ)

theorem infChar_conj {a : ℕ} (P : CuspSub E a) (hn : IsNormalised P) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : P.HasInfChar τ m) (hm' : P.HasInfChar (ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have := h1
  have := h2
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a μ P hn
  exact GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq E a P B hB τ m m' hm hm'

def strSum (d : ℕ) (m : Multiset ℂ) : Multiset ℂ := ∑ k : Fin d, m.map (· + (spehExp d k : ℂ))

end PositivityTheory.Rg.BcB.F.Rig.B

end
