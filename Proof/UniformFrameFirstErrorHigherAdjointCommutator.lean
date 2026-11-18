import Proof.UniformActualFirstErrorHigherAdjointCommutator
import Proof.GradedHigherWeightedThreeCrossCommutator
import Proof.UniformFrameFirstErrorSelfCommutator
import Proof.UniformActualFirstErrorAdjointCommutator
import Proof.FrameAdjointEndpointCombination
import Proof.GradedWeightedThreeCrossCommutator
import Proof.FrameEndpointCombination
import Proof.ActualFrameErrorEndpointPair
import Proof.CompatibleEndpointUniqueness
import Proof.UniformPhysicalPrincipalData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact point data for SAME selected frame first-error endpoints. -/
def FrameFirstErrorHigherAdjointCommutatorData {Y : Set X} {d : Data}
    {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {CE : ℝ}
    (P : ActualFrameErrorEndpointPair Y d A G CE) (y : X) (B : ℝ) : Prop :=
        (∀ j : I,∃ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
            (P.low j y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
        ∀ j k : I,∀ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
            (P.low j y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
          GradedHigherEndpointCommutatorBound (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
            (P.low j y).adjoint (P.low k y) Ha (P.high k y) B

/-- SAME selected moving-frame first-error endpoints admit higher adjoint
endpoints and retain the uniform quadratic mixed adjoint commutator. Only
frame values enter the quantitative transfer. -/
theorem uniform_actual_frame_first_error_higher_adjoint_commutator {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) →
      ∀ CE : ℝ,∀ P : ActualFrameErrorEndpointPair Y d A G CE,∀ y ∈ Y,
        FrameFirstErrorHigherAdjointCommutatorData P y (CS*(d.radius y)^2) := by
  classical
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hEndpoints⟩ := uniform_actual_first_adjoint_error_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηS,CSLow,hηS,hηS1,hCSLow,hSelf⟩ := uniform_actual_first_error_adjoint_commutator
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηH,CS,hηH,_hηH1,hCS,hSelfHigher⟩ := uniform_actual_first_error_higher_adjoint_commutator
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηE (min ηS ηH),9*K^2*CS,lt_min hηE (lt_min hηS hηH),
    (min_le_left _ _).trans hηE1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd R A G hR hA hG C0 P y hy
  choose Lo Hi hLS hHS hAll using fun a : I => hEndpoints floor hf ε hε
    (hSmall.trans (min_le_left _ _)) d hd (axis a) R A (G a) hR hA (hG a)
  have hPoint (a b : I) := hSelf floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd (axis a) (axis b)
    R A (G a) (G b) hR hA (hG a) (hG b) y hy (Lo a y) (Lo b y) (hAll a y hy).1 (hAll b y hy).1
  have hPointHigher (a b : I) := hSelfHigher floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd (axis a) (axis b)
    R A (G a) (G b) hR hA (hG a) (hG b) y hy (Lo a y) (Lo b y) (hAll a y hy).1 (hAll b y hy).1
  choose Adj hAdj using fun a : I => (hPoint a a).1
  have hComm (a b : I) : GradedHigherEndpointCommutatorBound
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (Lo a y).adjoint (Lo b y) (Adj a) (Hi b y) (CS*(d.radius y)^2) := by
    have hh := (hPointHigher a b) (Adj a) (Hi b y) (hAdj a) (hAll b y hy).2.1
    simpa only [norm_axis,mul_one] using hh
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hCoeff (l a : I) : |d.frame y l a| ≤ K := hd.1.1.frame_component_abs_le hK d.frame (hSub hy) hFrame l a
  have hLEq (l : I) := half_endpoint_unique_of_coarse (actualFrameFirstAdjointErrorFamily d A G l y)
    (P.low l y) (∑ a : I,d.frame y l a • Lo a y) (P.low_coarse l y hy)
    (frame_low_endpoint_combination d A G l y (fun a => Lo a y) (fun a => (hAll a y hy).1))
  have hHEq (l : I) := higher_endpoint_unique_of_coarse (actualFrameFirstAdjointErrorFamily d A G l y)
    (P.high l y) (∑ a : I,d.frame y l a • Hi a y) (P.high_coarse l y hy)
    (frame_high_endpoint_combination d A G l y (fun a => Hi a y) (fun a => (hAll a y hy).2.1))
  have hLAEq (l : I) : (P.low l y).adjoint=∑ a : I,d.frame y l a • (Lo a y).adjoint := by
    rw [hLEq l,map_sum]
    simp only [map_smul]
  let H (l : I) := ∑ a : I,d.frame y l a • Adj a
  have hH (l : I) : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H l)=
      (P.low l y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    have hh := finite_real_adjoint_balanced_combination
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) (fun a => Lo a y) Adj hAdj
      (fun a => d.frame y l a)
    exact hh.trans (congrArg (fun T => T.adjoint.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) (hLEq l).symm)
  constructor
  · intro j
    exact ⟨H j,hH j⟩
  · intro j k Ha hHa
    have hFin := graded_higher_weighted_three_cross_commutator
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (fun a => (Lo a y).adjoint) (fun b => Lo b y) Adj (fun b => Hi b y) (CS*(d.radius y)^2) K
      (mul_nonneg hCS (sq_nonneg _)) (zero_le_one.trans hK) hComm
      (fun a => d.frame y j a) (fun a => d.frame y k a) (hCoeff j) (hCoeff k)
    have hHAeq : Ha=H j := by
      apply ContinuousLinearMap.ext
      intro u
      apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      exact DFunLike.congr_fun (hHa.trans (hH j).symm) u
    exact (hFin.mono (le_of_eq (by ring))).congr
      (hLAEq j).symm (hLEq k).symm hHAeq.symm (hHEq k).symm

end ShrinkingSpheres
