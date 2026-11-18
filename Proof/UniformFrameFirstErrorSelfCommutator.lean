import Proof.UniformActualFirstErrorSelfCommutator
import Proof.GradedWeightedThreeCommutator
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

/-- The SAME selected moving-frame error endpoints retain the quadratic
radius-gained self commutator. Quantitative constants use frame values only. -/
theorem uniform_actual_frame_first_error_self_commutator {Y Ω : Set X}
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
      ∀ CE : ℝ,∀ P : ActualFrameErrorEndpointPair Y d A G CE,∀ y ∈ Y,∀ j k : I,
        GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
          (P.low j y) (P.low k y) (P.high j y) (P.high k y) (CS*(d.radius y)^2) := by
  classical
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hEndpoints⟩ := uniform_actual_first_adjoint_error_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηS,CS,hηS,hηS1,hCS,hSelf⟩ := uniform_actual_first_error_self_commutator
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηE ηS,9*K^2*CS,lt_min hηE hηS,(min_le_left _ _).trans hηE1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd R A G hR hA hG C0 P y hy j k
  choose Lo Hi hLS hHS hAll using fun a : I => hEndpoints floor hf ε hε
    (hSmall.trans (min_le_left _ _)) d hd (axis a) R A (G a) hR hA (hG a)
  have hComm (a b : I) : GradedEndpointCommutatorBound
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (Lo a y) (Lo b y) (Hi a y) (Hi b y) (CS*(d.radius y)^2) := by
    have hh := hSelf floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd (axis a) (axis b)
      R A (G a) (G b) hR hA (hG a) (hG b) y hy (Lo a y) (Lo b y) (Hi a y) (Hi b y)
      (hAll a y hy).1 (hAll b y hy).1 (hAll a y hy).2.1 (hAll b y hy).2.1
    simpa only [norm_axis,mul_one] using hh
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hCoeff (l a : I) : |d.frame y l a| ≤ K := hd.1.1.frame_component_abs_le hK d.frame (hSub hy) hFrame l a
  have hFin := graded_weighted_three_commutator
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (fun a => Lo a y) (fun a => Hi a y) (CS*(d.radius y)^2) K
    (mul_nonneg hCS (sq_nonneg _)) (zero_le_one.trans hK) hComm
    (fun a => d.frame y j a) (fun a => d.frame y k a) (hCoeff j) (hCoeff k)
  have hLEq (l : I) := half_endpoint_unique_of_coarse (actualFrameFirstAdjointErrorFamily d A G l y)
    (P.low l y) (∑ a : I,d.frame y l a • Lo a y) (P.low_coarse l y hy)
    (frame_low_endpoint_combination d A G l y (fun a => Lo a y) (fun a => (hAll a y hy).1))
  have hHEq (l : I) := higher_endpoint_unique_of_coarse (actualFrameFirstAdjointErrorFamily d A G l y)
    (P.high l y) (∑ a : I,d.frame y l a • Hi a y) (P.high_coarse l y hy)
    (frame_high_endpoint_combination d A G l y (fun a => Hi a y) (fun a => (hAll a y hy).2.1))
  exact (hFin.mono (le_of_eq (by ring))).congr (hLEq j).symm (hLEq k).symm (hHEq j).symm (hHEq k).symm

/-- Closed common physical principal data and its SAME uniformly gained
first-error self commutators, all produced before the physical test. -/
theorem uniform_physical_principal_self_commutator_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CF CT CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CF ∧ 0 ≤ CT ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∃ D : PhysicalPrincipalData Y d CF CT,∀ y ∈ Y,∀ j k : I,
        GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
          (D.first.low j y) (D.first.low k y) (D.first.high j y) (D.first.high k y) (CS*(d.radius y)^2) := by
  obtain ⟨ηD,CF,CT,hηD,hηD1,hCF,hCT,hData⟩ := uniform_physical_principal_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηS,CS,hηS,hηS1,hCS,hSelf⟩ := uniform_actual_frame_first_error_self_commutator hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηD ηS,CF,CT,CS,lt_min hηD hηS,(min_le_left _ _).trans hηD1,hCF,hCT,hCS,?_⟩
  intro floor hf ε hε hSmall d hd
  obtain ⟨D⟩ := hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd
  exact ⟨D,hSelf floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd D.radial D.adjoint D.center
    D.radial_actual D.adjoint_pair D.center_actual CF D.first⟩
end ShrinkingSpheres
