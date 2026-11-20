import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

namespace GlobalTheory.BlockMirabolic

theorem blockGL_mem_mirS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.mirS E S (m + r + 1) := by
  intro E _ _ m r S h hh
  constructor
  · intro w hw
    have hw1 := congrArg Units.val (hh w hw)
    apply Units.ext
    simp only [Units.val_one] at hw1 ⊢
    change ((GroundTheory.Automorphic.FourierWhittaker.blockMat _ h.val).map _) = 1
    change (h.val.map _) = 1 at hw1
    rw [GroundTheory.Automorphic.FourierWhittaker.map_blockMat, hw1, GroundTheory.Automorphic.FourierWhittaker.blockMat_one]
  · intro j
    change GroundTheory.Automorphic.FourierWhittaker.blockMat _ h.val (Fin.last (m + r + 1)) j = _
    rw [GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, dif_neg (by simp)]
    simp only [eq_comm]

end GlobalTheory.BlockMirabolic
