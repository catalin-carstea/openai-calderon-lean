import Proof.ParallelModelFirstZeroComparison
import Proof.ParallelModelFirstLeadingIntegral
import Proof.ParallelModelFirstDefectIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Integrability of the actual zero-model pair follows from the exact
complete physical split, whose other terms already have genuine L2 domains. -/
lemma modelFirstZeroDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0)
    (hP : ∀ b y,y ∈ Y →
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
        (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    IntegrableOn (modelFirstZeroDensity P WF U) Y := by
  have hI := modelFirstCorrectedDensity_integrableOn hY hΩ hSub hd hK P WF W hCG hCK U hU S hS hSY h0U
  have hL := (model_first_leading_integral_reduction hY hΩ hSub hd hK P WF W U hU S hS hSY h0U hP).1
  have hD := modelFirstDefectDensity_integrableOn hY hΩ hSub hd hK P WF W hCG hCK U hU S hS hSY h0U
  apply (((hI.const_mul (1/4:ℝ)).sub hL).add hD).congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  have hSplit := modelFirstCorrectedDensity_split hY hd P WF W U hy (hU.differentiable (by simp) y)
    (hd.1.2.2.2.2.2.2.2 y (hSub hy)) (fun b => hP b y hy)
  change (1/4:ℝ)*modelFirstCorrectedDensity P WF W U y-modelFirstLeadingDensity P WF U y+modelFirstDefectDensity P WF W U y=_
  linarith only [hSplit]

/-- Complete zero-model reduction: the actual residual is integrated
alongside the SAME-WF paired quadratic Green remainder. -/
theorem model_first_zero_integral_reduction
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK CE : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (hJ : FirstSelfCompleteAdjointJetBound WF CE)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0)
    (hP : ∀ b y,y ∈ Y →
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
        (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    IntegrableOn (modelFirstZeroDensity P WF U) Y ∧
      IntegrableOn (fun y => modelFirstZeroResidualDensity P WF U y+modelFirstZeroPairedRemainder WF hJ U y) Y ∧
      (∫ y in Y,modelFirstZeroDensity P WF U y)=
        ∫ y in Y,modelFirstZeroResidualDensity P WF U y+modelFirstZeroPairedRemainder WF hJ U y := by
  have hZ := modelFirstZeroDensity_integrableOn hY hΩ hSub hd hK P WF W hCG hCK U hU S hS hSY h0U hP
  have hGreen := model_first_zero_paired_integral_reduction hY hΩ hSub hd hK P WF W hJ U hU S hS hSY h0U
  have hRes : IntegrableOn (modelFirstZeroResidualDensity P WF U) Y := hZ.sub hGreen.1
  refine ⟨hZ,hRes.add hGreen.2.1,?_⟩
  have hEq : modelFirstZeroDensity P WF U=fun y => modelFirstZeroResidualDensity P WF U y+modelFirstZeroPairedDensity P WF U y := by
    funext y
    unfold modelFirstZeroResidualDensity
    ring
  calc
    _ = ∫ y in Y,modelFirstZeroResidualDensity P WF U y+modelFirstZeroPairedDensity P WF U y :=
      integral_congr_ae (Eventually.of_forall (fun y => congrFun hEq y))
    _ = (∫ y in Y,modelFirstZeroResidualDensity P WF U y)+(∫ y in Y,modelFirstZeroPairedDensity P WF U y) :=
      integral_add hRes hGreen.1
    _ = (∫ y in Y,modelFirstZeroResidualDensity P WF U y)+(∫ y in Y,modelFirstZeroPairedRemainder WF hJ U y) := by rw [hGreen.2.2]
    _ = _ := (integral_add hRes hGreen.2.1).symm

end ShrinkingSpheres.ParallelEnergy
