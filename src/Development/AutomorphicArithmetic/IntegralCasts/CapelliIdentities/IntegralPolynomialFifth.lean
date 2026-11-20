import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.IsIntP :
    {p : Nat} → [inst : Fact (Nat.Prime p)] → @PadicComplex p inst → Prop :=
    fun {p : Nat} [inst : Fact (Nat.Prime p)] (x : @PadicComplex p inst) ↦
      @LE.le Real Real.instLE
        (@Norm.norm (@PadicComplex p inst)
          (@UniformSpace.Completion.instNorm (@PadicAlgCl p inst)
            (@Valued.toUniformSpace (@PadicAlgCl p inst)
              (@DivisionRing.toRing (@PadicAlgCl p inst)
                (@Field.toDivisionRing (@PadicAlgCl p inst)
                  (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
              NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
            (@NormedField.toNorm (@PadicAlgCl p inst) (@PadicAlgCl.normedField p inst)))
          x)
        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))

theorem UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 :
    ∀ {p : Nat} [inst : Fact (Nat.Prime p)],
      @IsTopologicalDivisionRing (@PadicAlgCl p inst)
        (@Field.toDivisionRing (@PadicAlgCl p inst) (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst)))
        (@UniformSpace.toTopologicalSpace (@PadicAlgCl p inst)
          (@Valued.toUniformSpace (@PadicAlgCl p inst)
            (@DivisionRing.toRing (@PadicAlgCl p inst)
              (@Field.toDivisionRing (@PadicAlgCl p inst)
                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
            NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))) := by
  intro p inst
  exact Valued.isTopologicalDivisionRing

theorem UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 :
    ∀ {p : Nat} [inst : Fact (Nat.Prime p)],
      @CompletableTopField (@PadicAlgCl p inst) (@NormedField.toField (@PadicAlgCl p inst) (@PadicAlgCl.normedField p inst))
        (@PseudoMetricSpace.toUniformSpace (@PadicAlgCl p inst)
          (@SeminormedRing.toPseudoMetricSpace (@PadicAlgCl p inst)
            (@SeminormedCommRing.toSeminormedRing (@PadicAlgCl p inst)
              (@NormedCommRing.toSeminormedCommRing (@PadicAlgCl p inst)
                (@NormedField.toNormedCommRing (@PadicAlgCl p inst) (@PadicAlgCl.normedField p inst)))))) := by
  intro p inst
  exact NormedField.instCompletableTopField

theorem UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 :
    ∀ {p : Nat} [inst : Fact (Nat.Prime p)],
      @IsUniformAddGroup (@PadicAlgCl p inst)
        (@Valued.toUniformSpace (@PadicAlgCl p inst)
          (@DivisionRing.toRing (@PadicAlgCl p inst)
            (@Field.toDivisionRing (@PadicAlgCl p inst)
              (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
          NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
        (@AddGroupWithOne.toAddGroup (@PadicAlgCl p inst)
          (@Ring.toAddGroupWithOne (@PadicAlgCl p inst)
            (@DivisionRing.toRing (@PadicAlgCl p inst)
              (@Field.toDivisionRing (@PadicAlgCl p inst)
                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst)))))) := by
  intro p inst
  exact Valued.toIsUniformAddGroup

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : Nat} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ (@PadicComplex p inst) → Prop :=
    fun {σ : Type u_1} {p : Nat} [inst : Fact (Nat.Prime p)] (F : MvPowerSeries σ (@PadicComplex p inst)) ↦
      ∀ (n : @Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)),
        @UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.IsIntP p inst
          (@DFunLike.coe
            (@LinearMap (@PadicComplex p inst) (@PadicComplex p inst)
              (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                  (@Field.toSemifield (@PadicComplex p inst)
                    (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                      (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                      (@Valued.toUniformSpace (@PadicAlgCl p inst)
                        (@DivisionRing.toRing (@PadicAlgCl p inst)
                          (@Field.toDivisionRing (@PadicAlgCl p inst)
                            (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                        NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                      (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))
              (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                  (@Field.toSemifield (@PadicComplex p inst)
                    (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                      (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                      (@Valued.toUniformSpace (@PadicAlgCl p inst)
                        (@DivisionRing.toRing (@PadicAlgCl p inst)
                          (@Field.toDivisionRing (@PadicAlgCl p inst)
                            (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                        NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                      (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))
              (@RingHom.id (@PadicComplex p inst)
                (@Semiring.toNonAssocSemiring (@PadicComplex p inst)
                  (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                    (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                      (@Field.toSemifield (@PadicComplex p inst)
                        (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                          (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                          (@Valued.toUniformSpace (@PadicAlgCl p inst)
                            (@DivisionRing.toRing (@PadicAlgCl p inst)
                              (@Field.toDivisionRing (@PadicAlgCl p inst)
                                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                            NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))))
              (MvPowerSeries σ (@PadicComplex p inst)) (@PadicComplex p inst)
              (@MvPowerSeries.instAddCommMonoid σ (@PadicComplex p inst)
                (@Semiring.toAddCommMonoid (@PadicComplex p inst)
                  (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                    (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                      (@Field.toSemifield (@PadicComplex p inst)
                        (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                          (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                          (@Valued.toUniformSpace (@PadicAlgCl p inst)
                            (@DivisionRing.toRing (@PadicAlgCl p inst)
                              (@Field.toDivisionRing (@PadicAlgCl p inst)
                                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                            NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))))
              (@Semiring.toAddCommMonoid (@PadicComplex p inst)
                (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                  (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                    (@Field.toSemifield (@PadicComplex p inst)
                      (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                        (@Valued.toUniformSpace (@PadicAlgCl p inst)
                          (@DivisionRing.toRing (@PadicAlgCl p inst)
                            (@Field.toDivisionRing (@PadicAlgCl p inst)
                              (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                          NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst))))))
              (@MvPowerSeries.instModule σ (@PadicComplex p inst) (@PadicComplex p inst)
                (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                  (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                    (@Field.toSemifield (@PadicComplex p inst)
                      (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                        (@Valued.toUniformSpace (@PadicAlgCl p inst)
                          (@DivisionRing.toRing (@PadicAlgCl p inst)
                            (@Field.toDivisionRing (@PadicAlgCl p inst)
                              (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                          NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))
                (@Semiring.toAddCommMonoid (@PadicComplex p inst)
                  (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                    (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                      (@Field.toSemifield (@PadicComplex p inst)
                        (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                          (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                          (@Valued.toUniformSpace (@PadicAlgCl p inst)
                            (@DivisionRing.toRing (@PadicAlgCl p inst)
                              (@Field.toDivisionRing (@PadicAlgCl p inst)
                                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                            NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst))))))
                (@Semiring.toModule (@PadicComplex p inst)
                  (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                    (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                      (@Field.toSemifield (@PadicComplex p inst)
                        (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                          (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                          (@Valued.toUniformSpace (@PadicAlgCl p inst)
                            (@DivisionRing.toRing (@PadicAlgCl p inst)
                              (@Field.toDivisionRing (@PadicAlgCl p inst)
                                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                            NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))))
              (@Semiring.toModule (@PadicComplex p inst)
                (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                  (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                    (@Field.toSemifield (@PadicComplex p inst)
                      (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                        (@Valued.toUniformSpace (@PadicAlgCl p inst)
                          (@DivisionRing.toRing (@PadicAlgCl p inst)
                            (@Field.toDivisionRing (@PadicAlgCl p inst)
                              (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                          NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))))
            (MvPowerSeries σ (@PadicComplex p inst))
            (fun (x : MvPowerSeries σ (@PadicComplex p inst)) ↦ @PadicComplex p inst)
            (@LinearMap.instFunLike (@PadicComplex p inst) (@PadicComplex p inst) (MvPowerSeries σ (@PadicComplex p inst))
              (@PadicComplex p inst)
              (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                  (@Field.toSemifield (@PadicComplex p inst)
                    (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                      (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                      (@Valued.toUniformSpace (@PadicAlgCl p inst)
                        (@DivisionRing.toRing (@PadicAlgCl p inst)
                          (@Field.toDivisionRing (@PadicAlgCl p inst)
                            (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                        NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                      (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))
              (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                  (@Field.toSemifield (@PadicComplex p inst)
                    (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                      (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                      (@Valued.toUniformSpace (@PadicAlgCl p inst)
                        (@DivisionRing.toRing (@PadicAlgCl p inst)
                          (@Field.toDivisionRing (@PadicAlgCl p inst)
                            (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                        NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                      (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))
              (@MvPowerSeries.instAddCommMonoid σ (@PadicComplex p inst)
                (@Semiring.toAddCommMonoid (@PadicComplex p inst)
                  (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                    (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                      (@Field.toSemifield (@PadicComplex p inst)
                        (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                          (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                          (@Valued.toUniformSpace (@PadicAlgCl p inst)
                            (@DivisionRing.toRing (@PadicAlgCl p inst)
                              (@Field.toDivisionRing (@PadicAlgCl p inst)
                                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                            NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))))
              (@Semiring.toAddCommMonoid (@PadicComplex p inst)
                (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                  (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                    (@Field.toSemifield (@PadicComplex p inst)
                      (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                        (@Valued.toUniformSpace (@PadicAlgCl p inst)
                          (@DivisionRing.toRing (@PadicAlgCl p inst)
                            (@Field.toDivisionRing (@PadicAlgCl p inst)
                              (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                          NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst))))))
              (@MvPowerSeries.instModule σ (@PadicComplex p inst) (@PadicComplex p inst)
                (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                  (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                    (@Field.toSemifield (@PadicComplex p inst)
                      (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                        (@Valued.toUniformSpace (@PadicAlgCl p inst)
                          (@DivisionRing.toRing (@PadicAlgCl p inst)
                            (@Field.toDivisionRing (@PadicAlgCl p inst)
                              (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                          NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))
                (@Semiring.toAddCommMonoid (@PadicComplex p inst)
                  (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                    (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                      (@Field.toSemifield (@PadicComplex p inst)
                        (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                          (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                          (@Valued.toUniformSpace (@PadicAlgCl p inst)
                            (@DivisionRing.toRing (@PadicAlgCl p inst)
                              (@Field.toDivisionRing (@PadicAlgCl p inst)
                                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                            NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst))))))
                (@Semiring.toModule (@PadicComplex p inst)
                  (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                    (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                      (@Field.toSemifield (@PadicComplex p inst)
                        (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                          (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                          (@Valued.toUniformSpace (@PadicAlgCl p inst)
                            (@DivisionRing.toRing (@PadicAlgCl p inst)
                              (@Field.toDivisionRing (@PadicAlgCl p inst)
                                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                            NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))))
              (@Semiring.toModule (@PadicComplex p inst)
                (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                  (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                    (@Field.toSemifield (@PadicComplex p inst)
                      (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                        (@Valued.toUniformSpace (@PadicAlgCl p inst)
                          (@DivisionRing.toRing (@PadicAlgCl p inst)
                            (@Field.toDivisionRing (@PadicAlgCl p inst)
                              (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                          NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                        (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst))))))
              (@RingHom.id (@PadicComplex p inst)
                (@Semiring.toNonAssocSemiring (@PadicComplex p inst)
                  (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                    (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                      (@Field.toSemifield (@PadicComplex p inst)
                        (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                          (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                          (@Valued.toUniformSpace (@PadicAlgCl p inst)
                            (@DivisionRing.toRing (@PadicAlgCl p inst)
                              (@Field.toDivisionRing (@PadicAlgCl p inst)
                                (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                            NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst)
                          (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst))))))))
            (@MvPowerSeries.coeff σ (@PadicComplex p inst)
              (@DivisionSemiring.toSemiring (@PadicComplex p inst)
                (@Semifield.toDivisionSemiring (@PadicComplex p inst)
                  (@Field.toSemifield (@PadicComplex p inst)
                    (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                      (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                      (@Valued.toUniformSpace (@PadicAlgCl p inst)
                        (@DivisionRing.toRing (@PadicAlgCl p inst)
                          (@Field.toDivisionRing (@PadicAlgCl p inst)
                            (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                        NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                      (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux3 p inst) (@UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4 p inst)))))
              n)
            F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.intMv_X.{u_1} :
    ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {σ : Type u_1} (i : σ),
      @UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.IntegralMv σ p inst
        (@MvPowerSeries.X σ (@PadicComplex p inst)
          (@DivisionSemiring.toSemiring (@PadicComplex p inst)
            (@Semifield.toDivisionSemiring (@PadicComplex p inst)
              (@Field.toSemifield (@PadicComplex p inst)
                (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                  (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                  (@Valued.toUniformSpace (@PadicAlgCl p inst)
                    (@DivisionRing.toRing (@PadicAlgCl p inst)
                      (@Field.toDivisionRing (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                    NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                  (@Valued.isTopologicalDivisionRing (@PadicAlgCl p inst)
                    (@Field.toDivisionRing (@PadicAlgCl p inst)
                      (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst)))
                    NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                  (@NormedField.instCompletableTopField (@PadicAlgCl p inst) (@PadicAlgCl.normedField p inst))
                  (@Valued.toIsUniformAddGroup (@PadicAlgCl p inst)
                    (@DivisionRing.toRing (@PadicAlgCl p inst)
                      (@Field.toDivisionRing (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                    NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))))))
          i) := by
  intro p inst σ i n
  classical
  change ‖(MvPowerSeries.coeff n (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) : ℂ_[p])‖ ≤ 1
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact norm_one.le
  · rw [norm_zero]
    exact zero_le_one
