import Proof.NativeTaylorGeneratorSystem
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def taylorGeneratorFixedBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (C : ℝ) : ℝ :=
  1+|C|+‖sphereSobolevShiftedDegreeL (1/2:ℝ)‖+4*Real.sqrt 2+
    ‖closedHalfRadialScalarCommutatorL F0 ha0‖+
    ∑ i : I,∑ j : I,‖closedCoefficientAngularHalfL i j‖

lemma taylorGeneratorFixedBudget_bounds (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (C : ℝ) :
    1 ≤ taylorGeneratorFixedBudget F0 ha0 C ∧ C ≤ taylorGeneratorFixedBudget F0 ha0 C ∧
    ‖sphereSobolevShiftedDegreeL (1/2:ℝ)‖ ≤ taylorGeneratorFixedBudget F0 ha0 C ∧
    4*Real.sqrt 2 ≤ taylorGeneratorFixedBudget F0 ha0 C ∧
    ‖closedHalfRadialScalarCommutatorL F0 ha0‖ ≤ taylorGeneratorFixedBudget F0 ha0 C ∧
    ∀ i j : I,‖closedCoefficientAngularHalfL i j‖ ≤ taylorGeneratorFixedBudget F0 ha0 C := by
  have hSum : 0 ≤ ∑ i : I,∑ j : I,‖closedCoefficientAngularHalfL i j‖ := by positivity
  have hMem (i j : I) : ‖closedCoefficientAngularHalfL i j‖ ≤
      ∑ k : I,∑ l : I,‖closedCoefficientAngularHalfL k l‖ :=
    (Finset.single_le_sum (fun k _ => norm_nonneg (closedCoefficientAngularHalfL i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => norm_nonneg (closedCoefficientAngularHalfL k l)))
        (Finset.mem_univ i))
  unfold taylorGeneratorFixedBudget
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linarith [abs_nonneg C,norm_nonneg (sphereSobolevShiftedDegreeL (1/2:ℝ)),
      Real.sqrt_nonneg 2,norm_nonneg (closedHalfRadialScalarCommutatorL F0 ha0)]
  · linarith [le_abs_self C,abs_nonneg C,norm_nonneg (sphereSobolevShiftedDegreeL (1/2:ℝ)),
      Real.sqrt_nonneg 2,norm_nonneg (closedHalfRadialScalarCommutatorL F0 ha0)]
  · linarith [abs_nonneg C,norm_nonneg (sphereSobolevShiftedDegreeL (1/2:ℝ)),
      Real.sqrt_nonneg 2,norm_nonneg (closedHalfRadialScalarCommutatorL F0 ha0)]
  · linarith [abs_nonneg C,norm_nonneg (sphereSobolevShiftedDegreeL (1/2:ℝ)),
      Real.sqrt_nonneg 2,norm_nonneg (closedHalfRadialScalarCommutatorL F0 ha0)]
  · linarith [abs_nonneg C,norm_nonneg (sphereSobolevShiftedDegreeL (1/2:ℝ)),
      Real.sqrt_nonneg 2,norm_nonneg (closedHalfRadialScalarCommutatorL F0 ha0)]
  · intro i j
    linarith [hMem i j,abs_nonneg C,norm_nonneg (sphereSobolevShiftedDegreeL (1/2:ℝ)),
      Real.sqrt_nonneg 2,norm_nonneg (closedHalfRadialScalarCommutatorL F0 ha0)]

namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma generator_weight_bounds (A : NativeTaylorGeneratorBounds s h hK C)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    let CB := taylorGeneratorFixedBudget F0 ha0 C
    let G := taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0))
    let KG := taylorGeneratorCommutator
      (A.domain.degreeFamily h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)).adjoint
      (fun i j => fderiv ℝ s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeAngularTangent d.γ ((y,frameVectorLinear d.frame y),0) i j))
    (∀ a,‖G a‖ ≤ CB*taylorGeneratorWeight (d.radius y) a) ∧
    (∀ a b,‖KG a b‖ ≤ CB*(taylorGeneratorWeight (d.radius y) a*taylorGeneratorWeight (d.radius y) b)) ∧
    ∀ a Q,‖taylorGeneratorScalarCommutator A.scalar F0 ha0 a Q‖ ≤
      CB*(taylorGeneratorWeight (d.radius y) a*‖Q‖) := by
  obtain ⟨hCB,hCC,hD,hR,hS,hAng⟩ := taylorGeneratorFixedBudget_bounds F0 ha0 C
  let CB := taylorGeneratorFixedBudget F0 ha0 C
  have hCB0 : 0 ≤ CB := zero_le_one.trans hCB
  have hRT : Real.sqrt 2 ≤ CB := by linarith [Real.sqrt_nonneg 2]
  have hPa := A.low_bound.trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg _))
  have hDegree : ‖(A.domain.degreeFamily h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)).adjoint‖ ≤
      CB*(d.radius y)^2 := by
    rw [LinearIsometryEquiv.norm_map]
    exact A.degree_bound.trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg _))
  have hRotation (i j : I) := (A.angular_bound i j).trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg _))
  refine ⟨?_,?_,?_⟩
  · intro a
    cases a
    · exact hPa
    · simpa only [taylorGeneratorLow,taylorGeneratorWeight,mul_one] using hD
    · simpa only [taylorGeneratorLow,taylorGeneratorWeight,mul_one] using (norm_sphereSobolevRotationL_le _ _ _).trans hRT
  · intro a b
    cases a <;> cases b
    · simp only [taylorGeneratorCommutator,taylorGeneratorWeight,norm_zero]
      exact mul_nonneg hCB0 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · simpa only [taylorGeneratorCommutator,taylorGeneratorWeight,mul_one] using hDegree
    · simpa only [taylorGeneratorCommutator,taylorGeneratorWeight,mul_one,norm_neg] using hRotation _ _
    · simpa only [taylorGeneratorCommutator,taylorGeneratorWeight,one_mul,norm_neg] using hDegree
    · simp only [taylorGeneratorCommutator,taylorGeneratorWeight,norm_zero,mul_one];exact hCB0
    · simp only [taylorGeneratorCommutator,taylorGeneratorWeight,norm_zero,mul_one];exact hCB0
    · simpa only [taylorGeneratorCommutator,taylorGeneratorWeight,one_mul] using hRotation _ _
    · simp only [taylorGeneratorCommutator,taylorGeneratorWeight,norm_zero,mul_one];exact hCB0
    · simpa only [taylorGeneratorCommutator,taylorGeneratorWeight,mul_one] using
        (norm_rotationLieRemainderL_le _ _ _ _ _).trans hR
  · intro a Q
    cases a
    · exact (A.scalar_bound Q).trans
        ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (norm_nonneg Q)) (sq_nonneg _)).trans_eq
          (by simp only [taylorGeneratorWeight];ring))
    · simpa only [taylorGeneratorScalarCommutator,taylorGeneratorWeight,one_mul] using
        ((closedHalfRadialScalarCommutatorL F0 ha0).le_opNorm Q).trans
          (mul_le_mul_of_nonneg_right hS (norm_nonneg Q))
    · simpa only [taylorGeneratorScalarCommutator,taylorGeneratorWeight,one_mul] using
        ((closedCoefficientAngularHalfL _ _).le_opNorm Q).trans
          (mul_le_mul_of_nonneg_right (hAng _ _) (norm_nonneg Q))
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
