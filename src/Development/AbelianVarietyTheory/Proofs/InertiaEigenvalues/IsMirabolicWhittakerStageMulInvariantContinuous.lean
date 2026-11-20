import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory.GoodMul

theorem good_mul_invariant : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ) (ψ : AddChar (Ad E) ℂ) (f c : GA E a → ℂ),
    Good ψ m f → Continuous c → (∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, c (ratGL E a γ * g) = c g) →
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex a r l → Ad E) (g : GA E a), c (blkU y * g) = c g) → Good ψ m (fun g => c g * f g) := by
  intro E _ _ a m ψ f c hf hc hl hu
  refine ⟨hc.mul hf.cont, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hrm g => ?_⟩
  · show c _ * f _ = c g * f g
    rw [hl γ hγ g, hf.left γ hγ g]
  · show c _ * f _ = _ * (c g * f g)
    rw [hu k k y g, hf.law k hk y g]; ring
  · have h : (fun x : UnipotentBlockColumnIndex a r m → Ad E => c (blkU x * g) * f (blkU x * g)) =
        fun x => c g * f (blkU x * g) := by
      funext x; rw [hu r m x g]
    show avg _ (fun x : UnipotentBlockColumnIndex a r m → Ad E => c (blkU x * g) * f (blkU x * g)) = 0
    rw [h, avg_const_mul, hf.van r hr hrm g, mul_zero]

end GlobalTheory.GoodMul
