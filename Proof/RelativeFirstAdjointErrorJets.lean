import Proof.RadiusScaledFiniteJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open scoped ContDiff
namespace ShrinkingSpheres
variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']

def relativeFirstAdjointErrorOperator (r R b : ℝ)
    (A : E →L[ℝ] F) (M : E →L[ℝ] E) (G : E →L[ℝ] F) : E →L[ℝ] F :=
  (r⁻¹ • (R • A.comp M)+b • A)+G

lemma relativeFirstAdjointErrorOperator_compatible (r R b : ℝ)
    (A : E →L[ℝ] F) (M : E →L[ℝ] E) (G : E →L[ℝ] F)
    (A' : E' →L[ℝ] F') (M' : E' →L[ℝ] E') (G' : E' →L[ℝ] F')
    (J : F →L[ℝ] F') (I : E →L[ℝ] E')
    (hA : J.comp A = A'.comp I) (hM : I.comp M = M'.comp I) (hG : J.comp G = G'.comp I) :
    J.comp (relativeFirstAdjointErrorOperator r R b A M G) =
      (relativeFirstAdjointErrorOperator r R b A' M' G').comp I := by
  apply ContinuousLinearMap.ext
  intro u
  have hA0 (v : E) := congrArg (fun T : E →L[ℝ] F' => T v) hA
  have hM0 := congrArg (fun T : E →L[ℝ] E' => T u) hM
  have hG0 := congrArg (fun T : E →L[ℝ] F' => T u) hG
  simp only [ContinuousLinearMap.comp_apply] at hA0 hM0 hG0
  simp only [relativeFirstAdjointErrorOperator,ContinuousLinearMap.comp_apply,
    _root_.add_apply,_root_.smul_apply,map_add,map_smul,hA0,hM0,hG0]

lemma relativeFirstAdjointError_scaled_three_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {R b : P → ℝ} {A G : P → E →L[ℝ] F} {M : P → E →L[ℝ] E} {p : P}
    {r β c BR BP BM Bb BG : ℝ} (hr : 0 < r) (hβ : 1 ≤ β) (hrβ : r*β ≤ 1)
    (hc : 0 ≤ c) (hBR : 0 ≤ BR) (hBP : 0 ≤ BP) (hBM : 0 ≤ BM) (hBb : 0 ≤ Bb) (hBG : 0 ≤ BG)
    (hR : SmoothFiniteJetBound R p 3 BR)
    (hA : SmoothFiniteJetBound A p 3 (BP*r^2))
    (hM : SmoothFiniteJetBound M p 3 (BM*c))
    (hb : SmoothFiniteJetBound b p 3 (Bb*c))
    (hG : SmoothFiniteJetBound G p 3 (BG*c*r)) :
    SmoothFiniteJetBound (fun x => relativeFirstAdjointErrorOperator r (R x) (β*b x) (A x) (M x) (G x))
      p 3 ((2^3*BR*(2^3*BP*BM)+2^3*Bb*BP+BG)*c*r) := by
  have hβ0 := zero_le_one.trans hβ
  have hFirst := hR.scalar (hA.comp hM)
  have hBudget : 2^3*BR*(2^3*(BP*r^2)*(BM*c)) = (2^3*BR*(2^3*BP*BM)*c)*r^2 := by ring
  rw [hBudget] at hFirst
  have hFirst' := hFirst.radius_rescale hr
  have hSecond := (hb.scalar hA).const_smul β
  rw [abs_of_pos (zero_lt_one.trans_le hβ)] at hSecond
  have hGain : β*r^2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hrβ hr.le]
  have hSecondBudget : β*(2^3*(Bb*c)*(BP*r^2)) ≤ (2^3*Bb*BP)*c*r := by
    calc
      _ = (2^3*Bb*BP*c)*(β*r^2) := by ring
      _ ≤ (2^3*Bb*BP*c)*r := mul_le_mul_of_nonneg_left hGain (by positivity)
      _ = _ := by ring
  have hSecond' := hSecond.weaken hSecondBudget
  have hSum := (hFirst'.add hSecond').add hG
  have hFinalBudget : (2^3*BR*(2^3*BP*BM)*c)*r+(2^3*Bb*BP)*c*r+BG*c*r =
      (2^3*BR*(2^3*BP*BM)+2^3*Bb*BP+BG)*c*r := by ring
  rw [hFinalBudget] at hSum
  simpa only [relativeFirstAdjointErrorOperator,smul_smul] using hSum
end ShrinkingSpheres
