import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.AtLOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Ord.useAtL' {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A w}
    {r : Dec (F := L) A →* GL (Fin n) (Qbar l)} {lam : Wt L l n} {σ : SmIrr (GL (Fin n) (w.adicCompletion L))}
    (H : UpperTheory.V.Z.Ord.AtLT ι h r lam σ)
    (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (hs : ∀ i, IsSmoothChar (ω i))
    (hd : ∀ i j, i ≠ j → ∃ y : Uo (w.adicCompletion L), ω i y ≠ ω j y) (he : Nonempty (σ.ρ.Equiv (PS ω)))
    (rc : IrrGL (w.adicCompletion L) → WD h) (hrc : UpperTheory.Zero.LLC.IsRecT h rc) (hab : Lev.AbW (rc (algNorm σ))) :
    DRat ι h r (fun τ => Finset.univ.val.map fun j => htW lam j τ) fun s => (rc (algNorm σ)).charPol s :=
  H ω hs hd he rc hrc hab
