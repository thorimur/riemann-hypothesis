import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacBridge

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def adaptQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (t : E →ₐ[F] Fv F v) {d d₁ : ℕ} (H' : Plane E d d₁) : Matrix (Fin d) (Fin d) (Fv F v) :=
  Matrix.of fun r i =>
    if i.1 = 0 then t (H'.x r) else if i.1 + 1 = d then t (H'.y r)
    else if h : i.1 - 1 < d₁ then t (H'.ι r ⟨i.1 - 1, h⟩) else 0

end GlobalTheory.JacBridge
