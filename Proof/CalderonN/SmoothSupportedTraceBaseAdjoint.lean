module

public import Proof.CalderonN.SmoothSupportedTraceFiberAction

import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

/-! The weighted base derivative adjoint on supported sphere sections.
The density and its logarithmic derivative need only be smooth on Y. -/

public section

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

@[expose] def smoothSupportedTraceBaseMul (hY : IsOpen Y) (a : X dim → ℝ)
    (ha : ContDiffOn ℝ ∞ a Y) : Module.End ℝ (SmoothSupportedTraceSection Y) :=
  smoothSupportedTraceFiberAction hY _ (smoothSupportedTraceFiberRegular_smul hY ha)

theorem smoothSupportedTraceBaseMul_fiber (hY : IsOpen Y) (a : X dim → ℝ)
    (ha : ContDiffOn ℝ ∞ a Y) (u : SmoothSupportedTraceSection Y) (x : X dim) :
    smoothSupportedTraceFiberL x (smoothSupportedTraceBaseMul hY a ha u) =
      a x • smoothSupportedTraceFiberL x u := by
  rw [smoothSupportedTraceBaseMul,smoothSupportedTraceFiberAction_fiber,LinearMap.smul_apply,Module.End.one_apply]

theorem smoothSupportedTracePairing_congr_on_support (hn : 3 ≤ dim)
    {μ ν : X dim → ℝ} (u v : SmoothSupportedTraceSection Y) {K : Set (X dim)}
    (h : EqOn μ ν K) (hZero : ∀ x ∉ K, ∀ z, u.1 (x,z) = 0) :
    smoothSupportedTracePairing hn μ u v = smoothSupportedTracePairing hn ν u v := by
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    by_cases hx : x ∈ K
    · rw [h hx]
    · have hFiber : smoothSupportedTraceFiberL x u = 0 := Subtype.ext (funext (hZero x hx))
      simp only [smoothSupportedTraceL2,hFiber,map_zero,inner_zero_left,mul_zero]

theorem standardTraceBaseDiff_eq_zero_off_compact (u : SmoothSupportedTraceSection Y)
    (a : X dim) {K : Set (X dim)} (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ z, u.1 (x,z) = 0)
    (x : X dim) (hx : x ∉ K) (z : ↥(standardSphere dim)) :
    (smoothSupportedTraceBaseDiff a u).1 (x,z) = 0 := by
  have hz : (fun y => u.1 (y,z)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hZero y hy z
  rw [smoothSupportedTraceBaseDiff_apply,standardTraceBaseDiff,hz.fderiv_eq]
  simp

theorem smoothSupportedTrace_basePairing_IBP_local (hn : 3 ≤ dim) (hY : IsOpen Y)
    (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
    (u v : SmoothSupportedTraceSection Y) (i : I dim) :
    smoothSupportedTracePairing hn μ (smoothSupportedTraceBaseDiff (axis i) u) v =
      -smoothSupportedTracePairing hn μ u (smoothSupportedTraceBaseDiff (axis i) v)-
      smoothSupportedTracePairing hn (coordDeriv i μ) u v := by
  obtain ⟨K,hK,hKY,hZero⟩ := smoothSupportedTraceSection_compact u
  obtain ⟨ν,hν,_,V,hV,hKV,_,hEq⟩ := exists_contDiff_extension_near_compact hY hK hKY hμ
  have hE := hEq.mono hKV
  have hD : EqOn (coordDeriv i ν) (coordDeriv i μ) K := by
    intro x hx
    have hG : ν =ᶠ[𝓝 x] μ := by
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      exact hEq hy
    exact congrArg (fun L : X dim →L[ℝ] ℝ => L (axis i)) hG.fderiv_eq
  let D := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  have hDZero (x : X dim) (hx : x ∉ K) (z : ↥(standardSphere dim)) : (D u).1 (x,z) = 0 :=
    standardTraceBaseDiff_eq_zero_off_compact u _ hK hZero x hx z
  have h := smoothSupportedTrace_basePairing_IBP hn ν hν u v i
  change smoothSupportedTracePairing hn ν (D u) v =
    -smoothSupportedTracePairing hn ν u (D v)-smoothSupportedTracePairing hn (coordDeriv i ν) u v at h
  rw [smoothSupportedTracePairing_congr_on_support hn (D u) v hE hDZero,
    smoothSupportedTracePairing_congr_on_support hn u (D v) hE hZero,
    smoothSupportedTracePairing_congr_on_support hn u v hD hZero] at h
  exact h

theorem smoothSupportedTrace_basePairing_mul_right (hn : 3 ≤ dim) (hY : IsOpen Y)
    (μ a : X dim → ℝ) (ha : ContDiffOn ℝ ∞ a Y) (u v : SmoothSupportedTraceSection Y) :
    smoothSupportedTracePairing hn μ u (smoothSupportedTraceBaseMul hY a ha v) =
      smoothSupportedTracePairing hn (fun x => μ x*a x) u v := by
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [smoothSupportedTraceL2,smoothSupportedTraceBaseMul_fiber,map_smul,real_inner_smul_right]
    ring

theorem smoothSupportedTrace_basePairing_self_nonneg_local (hn : 3 ≤ dim)
    (μ : X dim → ℝ) (hμ : ∀ x ∈ Y, 0 ≤ μ x) (u : SmoothSupportedTraceSection Y) :
    0 ≤ smoothSupportedTracePairing hn μ u u := by
  apply integral_nonneg
  intro x
  change (0:ℝ) ≤ μ x*⟪smoothSupportedTraceL2 hn u x,smoothSupportedTraceL2 hn u x⟫_ℝ
  by_cases hx : x ∈ Y
  · exact mul_nonneg (hμ x hx) real_inner_self_nonneg
  · simp only [smoothSupportedTraceL2_eq_zero_off hn u hx,inner_zero_left,mul_zero,le_refl]

theorem smoothSupportedTrace_coordinate_adjoint (hn : 3 ≤ dim) (hY : IsOpen Y)
    (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y) (hPos : ∀ x ∈ Y, 0 < μ x)
    (i : I dim) (u v : SmoothSupportedTraceSection Y) :
    let a (x : X dim) := coordDeriv i μ x/μ x
    let ha : ContDiffOn ℝ ∞ a Y :=
      ((hμ.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const).div hμ
        (fun x hx => (hPos x hx).ne')
    smoothSupportedTracePairingL hn hY μ hμ (smoothSupportedTraceBaseDiff (axis i) u) v =
      smoothSupportedTracePairingL hn hY μ hμ u
        ((-smoothSupportedTraceBaseDiff (Y:=Y) (axis i)-smoothSupportedTraceBaseMul hY a ha :
          Module.End ℝ (SmoothSupportedTraceSection Y)) v) := by
  dsimp only
  rw [LinearMap.sub_apply,LinearMap.neg_apply,map_sub,map_neg]
  let a (x : X dim) := coordDeriv i μ x/μ x
  let ha : ContDiffOn ℝ ∞ a Y :=
    ((hμ.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const).div hμ (fun x hx => (hPos x hx).ne')
  change smoothSupportedTracePairing hn μ (smoothSupportedTraceBaseDiff (axis i) u) v =
    -smoothSupportedTracePairing hn μ u (smoothSupportedTraceBaseDiff (axis i) v)-
      smoothSupportedTracePairing hn μ u (smoothSupportedTraceBaseMul hY a ha v)
  rw [smoothSupportedTrace_basePairing_mul_right hn hY μ a ha]
  have hE : EqOn (fun x => μ x*a x) (coordDeriv i μ) Y := by
    intro x hx
    change μ x*(coordDeriv i μ x/μ x) = coordDeriv i μ x
    field_simp [(hPos x hx).ne']
  rw [smoothSupportedTracePairing_congr_density hn hE]
  exact smoothSupportedTrace_basePairing_IBP_local hn hY μ hμ u v i

end CalderonN
