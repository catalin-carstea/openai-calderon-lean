module

public import Proof.CalderonN.SmoothSupportedTraceSections

import Proof.CalderonN.SmoothSphereFields
import Proof.CalderonN.SmoothZonalSobolev
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! The global real pairing on smooth, compactly base-supported sphere
sections. Coordinate integration by parts holds against a smooth density. -/

public section

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 5100000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)}

@[expose] def smoothSupportedTraceL2 (hn : 3 ≤ dim) (u : SmoothSupportedTraceSection Y) (x : X dim) :
    SphereL2 dim := smoothSphereTraceL2 hn (smoothSupportedTraceFiberL x u)

theorem smoothSupportedTraceL2_eq_ambient (hn : 3 ≤ dim) (u : SmoothSupportedTraceSection Y)
    {G : X dim × X dim → ℝ} (hG : ContDiff ℝ ∞ G) (h : ∀ x z, u.1 (x,z) = G (x,z)) (x : X dim) :
    smoothSupportedTraceL2 hn u x = ambientSphereL2 G hG x := by
  let g : SmoothData dim := ⟨fun z => G (x,z),hG.comp (contDiff_const.prodMk contDiff_id)⟩
  have hFiber : smoothSupportedTraceFiberL x u = smoothSphereTrace g := by
    apply Subtype.ext
    exact funext fun z => h x z
  rw [smoothSupportedTraceL2,hFiber,smoothSphereTraceL2_apply,ambientSphereL2_eq_smoothSphereLift]

theorem contDiff_smoothSupportedTraceL2 (hn : 3 ≤ dim) (u : SmoothSupportedTraceSection Y) :
    ContDiff ℝ ∞ (smoothSupportedTraceL2 hn u) := by
  obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
  rw [funext (smoothSupportedTraceL2_eq_ambient hn u hG hu)]
  exact contDiff_ambientSphereL2 G hG

theorem hasCompactSupport_smoothSupportedTraceL2 (hn : 3 ≤ dim) (u : SmoothSupportedTraceSection Y) :
    HasCompactSupport (smoothSupportedTraceL2 hn u) := by
  obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
  obtain ⟨K,hK,_,hZero⟩ := smoothSupportedTraceSection_compact u
  rw [funext (smoothSupportedTraceL2_eq_ambient hn u hG hu)]
  exact hasCompactSupport_ambientSphereL2 G hG K hK (fun x hx z => (hu x z).symm.trans (hZero x hx z))

theorem fderiv_smoothSupportedTraceL2 (hn : 3 ≤ dim) (u : SmoothSupportedTraceSection Y) (x a : X dim) :
    fderiv ℝ (smoothSupportedTraceL2 hn u) x a = smoothSupportedTraceL2 hn (smoothSupportedTraceBaseDiff a u) x := by
  obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
  let D (p : X dim × X dim) := fderiv ℝ G p (a,0)
  have hD : ContDiff ℝ ∞ D := (hG.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hdu (y : X dim) (z : ↥(standardSphere dim)) :
      (smoothSupportedTraceBaseDiff a u).1 (y,z) = D (y,z) :=
    (smoothSupportedTraceBaseDiff_apply a u y z).trans (standardTraceBaseDiff_of_repr a hG hu y z)
  rw [funext (smoothSupportedTraceL2_eq_ambient hn u hG hu),
    smoothSupportedTraceL2_eq_ambient hn (smoothSupportedTraceBaseDiff a u) hD hdu]
  apply Lp.ext
  exact (fderiv_ambientSphereL2_ae G hG x a).trans (ambientSphereL2_ae D hD x).symm

@[expose] def smoothSupportedTracePairing (hn : 3 ≤ dim) (μ : X dim → ℝ)
    (u v : SmoothSupportedTraceSection Y) : ℝ :=
  ∫ x, μ x*⟪smoothSupportedTraceL2 hn u x,smoothSupportedTraceL2 hn v x⟫_ℝ

theorem smoothSupportedTracePairing_symm (hn : 3 ≤ dim) (μ : X dim → ℝ)
    (u v : SmoothSupportedTraceSection Y) :
    smoothSupportedTracePairing hn μ u v = smoothSupportedTracePairing hn μ v u := by
  unfold smoothSupportedTracePairing
  simp_rw [real_inner_comm]

theorem smoothSupportedTracePairing_self_nonneg (hn : 3 ≤ dim) (μ : X dim → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (u : SmoothSupportedTraceSection Y) :
    0 ≤ smoothSupportedTracePairing hn μ u u := by
  apply integral_nonneg
  exact fun x => mul_nonneg (hμ x) real_inner_self_nonneg

theorem integrable_smoothSupportedTracePairing_integrand (hn : 3 ≤ dim)
    (μ : X dim → ℝ) (hμ : Continuous μ)
    (u v : SmoothSupportedTraceSection Y) :
    Integrable (fun x => μ x*⟪smoothSupportedTraceL2 hn u x,smoothSupportedTraceL2 hn v x⟫_ℝ) := by
  have hu := contDiff_smoothSupportedTraceL2 hn u
  have hv := contDiff_smoothSupportedTraceL2 hn v
  have hSup : HasCompactSupport (fun x =>
      ⟪smoothSupportedTraceL2 hn u x,smoothSupportedTraceL2 hn v x⟫_ℝ) := by
    apply HasCompactSupport.intro (hasCompactSupport_smoothSupportedTraceL2 hn u)
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx,inner_zero_left]
  exact (hμ.mul (hu.continuous.inner hv.continuous)).integrable_of_hasCompactSupport hSup.mul_left

theorem smoothSupportedTraceL2_eq_zero_off (hn : 3 ≤ dim)
    (u : SmoothSupportedTraceSection Y) {x : X dim} (hx : x ∉ Y) :
    smoothSupportedTraceL2 hn u x = 0 := by
  obtain ⟨K,_,hKY,hZero⟩ := smoothSupportedTraceSection_compact u
  have hFiber : smoothSupportedTraceFiberL x u = 0 := by
    apply Subtype.ext
    funext z
    exact hZero x (fun hxK => hx (hKY hxK)) z
  rw [smoothSupportedTraceL2,hFiber,map_zero]

theorem smoothSupportedTracePairing_congr_density (hn : 3 ≤ dim) {μ ν : X dim → ℝ}
    (h : EqOn μ ν Y) (u v : SmoothSupportedTraceSection Y) :
    smoothSupportedTracePairing hn μ u v = smoothSupportedTracePairing hn ν u v := by
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    by_cases hx : x ∈ Y
    · rw [h hx]
    · rw [smoothSupportedTraceL2_eq_zero_off hn u hx,inner_zero_left,mul_zero,mul_zero]

theorem integrable_smoothSupportedTracePairing_integrand_local (hn : 3 ≤ dim) (hY : IsOpen Y)
    (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y) (u v : SmoothSupportedTraceSection Y) :
    Integrable (fun x => μ x*⟪smoothSupportedTraceL2 hn u x,smoothSupportedTraceL2 hn v x⟫_ℝ) := by
  obtain ⟨K,hK,hKY,hZero⟩ := smoothSupportedTraceSection_compact u
  obtain ⟨ν,hν,_,V,_,hKV,_,hEq⟩ := exists_contDiff_extension_near_compact hY hK hKY hμ
  apply (integrable_smoothSupportedTracePairing_integrand hn ν hν.continuous u v).congr
  exact ae_of_all _ fun x => by
    dsimp only
    by_cases hx : x ∈ K
    · rw [hEq (hKV hx)]
    · have hFiber : smoothSupportedTraceFiberL x u = 0 := by
        apply Subtype.ext
        exact funext (hZero x hx)
      simp only [smoothSupportedTraceL2,hFiber,map_zero,inner_zero_left,mul_zero]

@[expose] def smoothSupportedTracePairingL (hn : 3 ≤ dim) (hY : IsOpen Y)
    (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y) :
    SmoothSupportedTraceSection Y →ₗ[ℝ] SmoothSupportedTraceSection Y →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := smoothSupportedTracePairing hn μ u
      map_add' v w := by
        unfold smoothSupportedTracePairing
        simp only [smoothSupportedTraceL2,map_add,inner_add_right,mul_add]
        exact integral_add (integrable_smoothSupportedTracePairing_integrand_local hn hY μ hμ u v)
          (integrable_smoothSupportedTracePairing_integrand_local hn hY μ hμ u w)
      map_smul' c v := by
        unfold smoothSupportedTracePairing
        simp only [smoothSupportedTraceL2,map_smul,real_inner_smul_right,RingHom.id_apply,smul_eq_mul]
        simp_rw [mul_left_comm (μ _) c]
        exact integral_const_mul c _ }
  map_add' u v := by
    ext w : 1
    change smoothSupportedTracePairing hn μ (u+v) w =
      smoothSupportedTracePairing hn μ u w+smoothSupportedTracePairing hn μ v w
    unfold smoothSupportedTracePairing
    simp only [smoothSupportedTraceL2,map_add,inner_add_left,mul_add]
    exact integral_add (integrable_smoothSupportedTracePairing_integrand_local hn hY μ hμ u w)
      (integrable_smoothSupportedTracePairing_integrand_local hn hY μ hμ v w)
  map_smul' c u := by
    ext w : 1
    change smoothSupportedTracePairing hn μ (c • u) w = c • smoothSupportedTracePairing hn μ u w
    unfold smoothSupportedTracePairing
    simp only [smoothSupportedTraceL2,map_smul,real_inner_smul_left,smul_eq_mul]
    simp_rw [mul_left_comm (μ _) c]
    exact integral_const_mul c _

theorem smoothSupportedTrace_basePairing_IBP (hn : 3 ≤ dim)
    (μ : X dim → ℝ) (hμ : ContDiff ℝ ∞ μ)
    (u v : SmoothSupportedTraceSection Y) (i : I dim) :
    smoothSupportedTracePairing hn μ (smoothSupportedTraceBaseDiff (axis i) u) v =
      -smoothSupportedTracePairing hn μ u (smoothSupportedTraceBaseDiff (axis i) v)-
      smoothSupportedTracePairing hn (coordDeriv i μ) u v := by
  let U := smoothSupportedTraceL2 hn u
  let V := smoothSupportedTraceL2 hn v
  let P (x : X dim) := μ x*⟪U x,V x⟫_ℝ
  have hU := contDiff_smoothSupportedTraceL2 hn u
  have hV := contDiff_smoothSupportedTraceL2 hn v
  have hUV : ContDiff ℝ ∞ (fun x => ⟪U x,V x⟫_ℝ) := ContDiff.inner ℝ hU hV
  have hP : ContDiff ℝ ∞ P := hμ.mul hUV
  have hPc : HasCompactSupport P := by
    apply HasCompactSupport.intro (hasCompactSupport_smoothSupportedTraceL2 hn u)
    intro x hx
    have hZero : U x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [P,hZero,inner_zero_left,mul_zero]
  have h0 := integral_mul_coordDeriv_eq_neg (U:=univ) isOpen_univ
    (f:=fun _ : X dim => (1:ℝ)) contDiffOn_const hP hPc (subset_univ _) i
  simp only [one_mul,coordDeriv,fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.zero_apply,
    zero_mul,integral_zero,neg_zero] at h0
  have hDer (x : X dim) :
      fderiv ℝ P x (axis i) =
        (coordDeriv i μ x)*⟪U x,V x⟫_ℝ+
        (μ x*⟪smoothSupportedTraceL2 hn (smoothSupportedTraceBaseDiff (axis i) u) x,V x⟫_ℝ+
          μ x*⟪U x,smoothSupportedTraceL2 hn (smoothSupportedTraceBaseDiff (axis i) v) x⟫_ℝ) := by
    unfold P
    rw [fderiv_fun_mul (hμ.differentiable (by simp) x) (hUV.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    rw [fderiv_inner_apply ℝ (hU.differentiable (by simp) x) (hV.differentiable (by simp) x)]
    simp only [U,V,fderiv_smoothSupportedTraceL2,coordDeriv]
    ring
  have hIC : Continuous (coordDeriv i μ) :=
    ((hμ.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).continuous
  let D := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  have h₀ := integrable_smoothSupportedTracePairing_integrand hn _ hIC u v
  have h₁ := integrable_smoothSupportedTracePairing_integrand hn μ hμ.continuous (D u) v
  have h₂ := integrable_smoothSupportedTracePairing_integrand hn μ hμ.continuous u (D v)
  simp_rw [hDer] at h0
  let f₀ (x : X dim) := coordDeriv i μ x*⟪U x,V x⟫_ℝ
  let f₁ (x : X dim) := μ x*⟪smoothSupportedTraceL2 hn (D u) x,V x⟫_ℝ
  let f₂ (x : X dim) := μ x*⟪U x,smoothSupportedTraceL2 hn (D v) x⟫_ℝ
  have hInt : (∫ x,f₀ x+(f₁ x+f₂ x)) = (∫ x,f₀ x)+((∫ x,f₁ x)+(∫ x,f₂ x)) :=
    (integral_add (f:=f₀) (g:=f₁+f₂) h₀ (h₁.add h₂)).trans
      (congrArg ((∫ x,f₀ x)+·) (integral_add (f:=f₁) (g:=f₂) h₁ h₂))
  have h0' := hInt.symm.trans h0
  change smoothSupportedTracePairing hn (coordDeriv i μ) u v+
    (smoothSupportedTracePairing hn μ (D u) v+smoothSupportedTracePairing hn μ u (D v)) = 0 at h0'
  unfold smoothSupportedTracePairing
  unfold smoothSupportedTracePairing at h0'
  linarith only [h0']

end CalderonN
