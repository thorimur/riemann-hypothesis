import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateModuleEigenspaceDimEqLieAlgebraSum
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModule_eigenspace_dim_eq_lieAlgebra_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (τ : OE →+* C), eigDim C (fun a : OE => (H.ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) τ = eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) τ + eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) := by
  first | exact @GlobalTheory.ChF.eigDim_tate | exact GlobalTheory.ChF.eigDim_tate | (intros; apply GlobalTheory.ChF.eigDim_tate <;> assumption)
