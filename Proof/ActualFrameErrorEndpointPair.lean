import Proof.FrameErrorRaisingHalfCross
import Proof.Smallness
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Shared genuine endpoints of one actual physical first-adjoint frame error. -/
structure ActualFrameErrorEndpointPair (Y : Set X) (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (CE : ℝ) where
  low : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  high : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  low_smooth : ∀ i,ContDiffOn ℝ ∞ (low i) Y
  high_smooth : ∀ i,ContDiffOn ℝ ∞ (high i) Y
  low_coarse : ∀ i,∀ x ∈ Y,
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFrameFirstAdjointErrorFamily d A G i x)=
      (low i x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  high_coarse : ∀ i,∀ x ∈ Y,
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (high i x)=
      (actualFrameFirstAdjointErrorFamily d A G i x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))
  low_bound : ∀ i,∀ x ∈ Y,‖low i x‖ ≤ CE*d.radius x
  high_bound : ∀ i,∀ x ∈ Y,‖high i x‖ ≤ CE*d.radius x

namespace ActualFrameErrorEndpointPair
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {CE : ℝ}

def raisingCrossL (P : ActualFrameErrorEndpointPair Y d A G CE) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := frameErrorRaisingHalfCrossL P.low P.high x

lemma raisingCross_smooth (P : ActualFrameErrorEndpointPair Y d A G CE) :
    ContDiffOn ℝ ∞ P.raisingCrossL Y := contDiffOn_frameErrorRaisingHalfCrossL P.low P.high P.low_smooth P.high_smooth

lemma norm_raisingCross_le (P : ActualFrameErrorEndpointPair Y d A G CE) (hCE : 0 ≤ CE)
    {x : X} (hx : x ∈ Y) (hr : 0 ≤ d.radius x) :
    ‖P.raisingCrossL x‖ ≤
      3*(10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ)))*CE*d.radius x := by
  exact (norm_frameErrorRaisingHalfCrossL_le P.low P.high x (CE*d.radius x) (mul_nonneg hCE hr)
    (fun i => P.low_bound i x hx) (fun i => P.high_bound i x hx)).trans_eq (by ring)

lemma norm_raisingCross_small {Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : ActualFrameErrorEndpointPair Y d A G CE) (hCE : 0 ≤ CE)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hf : 1 ≤ floor) {x : X} (hx : x ∈ Y) :
    ‖P.raisingCrossL x‖ ≤
      3*(10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ)))*CE*ε := by
  have hr := (hd.2.2.2.2.1.2 x hx).1
  have hrε := (radius_bounds (d.radius x) (beta d.γ d.radius x) floor ε hr.le hf
    (hd.2.2.2.2.1.2 x hx).2.1 (hd.2.2.2.2.2 x hx).2).2.2
  have hB (s : ℝ) : 0 ≤ radialDriftSobolevBound s := zero_le_one.trans (le_max_left _ _)
  have hBlo := hB (-(1/2:ℝ))
  have hBhi := hB (-(3/2:ℝ))
  exact (P.norm_raisingCross_le hCE hx hr.le).trans
    (mul_le_mul_of_nonneg_left hrε (by positivity))

/-- The controlled half-order cross map is exactly the two actual physical
    compositions after genuine inclusion into H(-1), on the common H2 core. -/
lemma raisingCross_coarse (P : ActualFrameErrorEndpointPair Y d A G CE)
    {x : X} (hx : x ∈ Y) :
    (sphereSobolevInclusionL (-(1/2:ℝ)) (-1:ℝ) (by norm_num)).comp
      ((P.raisingCrossL x).comp (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)))=
    ∑ i : I,((flatZeroRaisingL i).comp
      ((actualFrameFirstAdjointErrorFamily d A G i x).comp (sphereSobolevInclusionL 2 1 (by norm_num)))+
      (sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num)).comp
        ((actualFrameFirstAdjointErrorFamily d A G i x).comp (flatTwoRaisingL i))) := by
  apply DFunLike.ext
  intro u
  simp only [raisingCrossL,frameErrorRaisingHalfCrossL,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.add_apply,map_sum,map_add]
  apply Finset.sum_congr rfl
  intro i _
  have hLo := DFunLike.congr_fun (flatHalfRaisingL_coarse i)
    (P.high i x (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u))
  have hHi := DFunLike.congr_fun (flatThreeHalfRaisingL_high i) u
  have hEHi := DFunLike.congr_fun (P.high_coarse i x hx)
    (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)
  have hELo := DFunLike.congr_fun (P.low_coarse i x hx) (flatTwoRaisingL i u)
  simp only [ContinuousLinearMap.comp_apply] at hLo hHi hEHi hELo
  rw [sphereSobolevInclusionL_trans_apply] at hEHi
  rw [hLo,hEHi,hHi,← hELo,sphereSobolevInclusionL_trans_apply]
end ActualFrameErrorEndpointPair

/-- The physical endpoint producer supplies one shared package; no new
    external premise is introduced into the selected theorem. -/
theorem uniform_actual_frame_error_endpoint_pair {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) →
      Nonempty (ActualFrameErrorEndpointPair Y d A G CE) := by
  obtain ⟨η,CE,hη,hη1,hCE,hProduce⟩ :=
    uniform_actual_frame_first_adjoint_error_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A G hR hA hG
  obtain ⟨L,H,hLS,hHS,hAll⟩ := hProduce floor hf ε hε hSmall d hd R A G hR hA hG
  exact ⟨⟨L,H,hLS,hHS,(fun i x hx => (hAll i x hx).1),(fun i x hx => (hAll i x hx).2.1),
    (fun i x hx => (hAll i x hx).2.2.1),(fun i x hx => (hAll i x hx).2.2.2)⟩⟩
end ShrinkingSpheres
