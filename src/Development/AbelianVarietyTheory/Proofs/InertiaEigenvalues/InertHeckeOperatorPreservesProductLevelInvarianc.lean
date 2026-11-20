import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorPreservesLevelInvariants
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertSatInv.heckeFunI_rt_invariant_prod : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ b ∈ U ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ κ ∈ U, NG.rt L n κ (heckeFunI L n U Dv h f) = heckeFunI L n U Dv h f := by
  intro L _ _ _ n v w Dv U hU hsplit W _ _ h hh f hf κ hκ
  refine GlobalTheory.heckeFunI_rt_invariant L n v w Dv U hU ?_ W h hh f hf κ hκ
  intro u hu
  obtain ⟨a, b, rfl, haM, hat, hbU, hbc⟩ := hsplit u hu
  exact ⟨a, b, rfl, (hU a hat).2 haM, hat, hbU, fun x hx => (hbc x hx).symm⟩
