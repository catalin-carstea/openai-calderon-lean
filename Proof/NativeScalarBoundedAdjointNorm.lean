import Proof.NativeScalarBoundedAdjointForm
import Proof.NativeAdjointRemainderHalfNorm
import Proof.NativeTaylorScalarAdjointRemainderBound
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

/-- A common budget for generator norms, both adjoint remainders and the
unsigned bounded correction of the full actual first-base coefficient. -/
def nativeScalarBoundedAdjointBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CK CQ CI CW CQB CZB : ℝ) : ℝ :=
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  1+|CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CQB|+
    |(‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB)*CQB+CZB|+
    |(‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW)*CQB+CZB|+
    |CZB|

lemma nativeScalarBoundedAdjointBudget_bounds (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CK CQ CI CW CQB CZB : ℝ) :
    let CB := taylorGeneratorFixedBudget F0 ha0 CG
    let CP := nativeScalarBoundedAdjointBudget F0 ha0 CG CK CQ CI CW CQB CZB
    1 ≤ CP ∧ CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CQB ≤ CP ∧
    (‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB)*CQB+CZB ≤ CP ∧
    (‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW)*CQB+CZB ≤ CP ∧
    CZB ≤ CP := by
  dsimp only [nativeScalarBoundedAdjointBudget]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith only [le_abs_self (taylorGeneratorFixedBudget F0 ha0 CG*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CQB),
    le_abs_self ((‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+taylorGeneratorFixedBudget F0 ha0 CG)*CQB+CZB),
    le_abs_self ((‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW)*CQB+CZB),
    le_abs_self CZB,abs_nonneg (taylorGeneratorFixedBudget F0 ha0 CG*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CQB),
    abs_nonneg ((‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+taylorGeneratorFixedBudget F0 ha0 CG)*CQB+CZB),
    abs_nonneg ((‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW)*CQB+CZB),
    abs_nonneg CZB]

lemma NativeScalarBoundedEndpointData.norm_adjoint_remainders
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG} {CQB CZB scale : ℝ}
    {L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
    (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2) :
    let CB := taylorGeneratorFixedBudget F0 ha0 CG
    ‖B.adjointRemainderHalfL ha0 KN‖ ≤
      ((‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB)*CQB+CZB)*scale ∧
    ‖B.adjointRemainderNegativeL ha0 KN‖ ≤
      ((‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW)*CQB+CZB)*scale := by
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let Rp := ‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB
  let Rn := ‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW
  have hCB : 0 ≤ CB := zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
  have hCN : 0 ≤ nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW :=
    add_nonneg (zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 _).1) (norm_nonneg _)
  have hRp : 0 ≤ Rp := add_nonneg (mul_nonneg (norm_nonneg _) hCK) hCB
  have hRn : 0 ≤ Rn := add_nonneg (mul_nonneg (norm_nonneg _) hCK) hCN
  have hp := (T.scalar_adjoint_remainder_half_bound ha0 KN CK hCK hKN (B.coefficient)).trans
    (mul_le_mul_of_nonneg_left (B.coefficient_bound) hRp)
  have hn := (s.native_scalar_adjoint_remainder_bound hF0 ha0 hCQ hCI hCW hr hr1 KN CK hCK hKN
    (B.coefficient)).trans (mul_le_mul_of_nonneg_left (B.coefficient_bound) hRn)
  have hZp : ‖(B.boundedNegative).adjoint‖ ≤ CZB*scale := by
    simpa only [LinearIsometryEquiv.norm_map] using (B.bounded_bounds).2
  have hZn : ‖(B.boundedHalf).adjoint‖ ≤ CZB*scale := by
    simpa only [LinearIsometryEquiv.norm_map] using (B.bounded_bounds).1
  constructor
  · exact (norm_add_le _ _).trans ((add_le_add hp hZp).trans_eq (by ring))
  · exact (norm_add_le _ _).trans ((add_le_add hn hZn).trans_eq (by ring))
end ShrinkingSpheres
