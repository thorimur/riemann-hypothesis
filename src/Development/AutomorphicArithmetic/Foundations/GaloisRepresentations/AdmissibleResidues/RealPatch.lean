import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ComplexConjAlgebraMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

theorem hodgeTate : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a), π.IsRegAlg → ∃ HTF : (F →+* Qbar l) → Multiset ℤ, (∀ τ, (HTF τ).card = a) ∧ (∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m → (HTF τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z) ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ (P : CuspSub K a), IsBC π P → ∀ (χ : HChar (maximalRealSubfield K)) (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), UpperTheory.GalN.IsGalU P χ ι r wt HT → (∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))) ∧ ∀ τ : F →+* Qbar l, HTF τ = (HTF τ).map (wt - ·) := by
  intro F Ω _ _ _ _ _ _ l _ ι a π hπ
  choose HTF hHTF using fun τ : F →+* Qbar l => exists_hodgeTate π hπ (InfinitePlace.mk (ι.toRingHom.comp τ))
  have key : ∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m →
      (HTF τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z := by
    intro τ m hm
    obtain ⟨m0, hm0, e⟩ := hHTF τ
    rw [e, TR.CuspSub.HasInfChar.unique hm0 hm]
  refine ⟨HTF, fun τ => ?_, key, ?_⟩
  · obtain ⟨m0, hm0, e⟩ := hHTF τ
    have := congrArg Multiset.card e
    simpa [hm0.1] using this
  · intro K _ _ _ _ _ _ _ h2 P hBC χ r wt HT hG
    have hK : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K)) := by
      intro τ
      obtain ⟨m0, hm0, e⟩ := hHTF (τ.comp (algebraMap F K))
      have h1 : P.HasInfChar (ι.toRingHom.comp τ) m0 := hBC.inf _ _ hm0
      have h3 : (CG.mk P).infChar (ι.toRingHom.comp τ) = m0 := CG.HasInfChar.infChar_eq h1
      apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
      rw [hG.weights τ, h3, e]
    refine ⟨hK, fun τ => ?_⟩
    letI : Algebra F (Qbar l) := τ.toAlgebra
    haveI : Module.Finite F K := Module.finite_of_finrank_pos (by omega)
    haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
    let τ' : K →ₐ[F] Qbar l := IsAlgClosed.lift
    have hτ' : (τ' : K →+* Qbar l).comp (algebraMap F K) = τ := RingHom.ext fun x => τ'.commutes x
    have hc : ((τ' : K →+* Qbar l).comp (IsCMField.complexConj K).toRingEquiv.toRingHom).comp (algebraMap F K) = τ := by
      rw [← hτ']
      ext x
      simp only [RingHom.comp_apply]
      exact congrArg τ' (complexConj_algebraMap (K := K) x)
    have := hG.weights_conj (τ' : K →+* Qbar l)
    rw [hK, hK, hc, hτ'] at this
    exact this

end UpperTheory.GalN.V
