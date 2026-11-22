module

public import Proof.CalderonN.ActualPhysicalRotatedConormalJets
public import Proof.CalderonN.ActualConormalFiberDerivativeWeak
public import Proof.CalderonN.SmoothSupportedFiberRotationDerivative

import Mathlib.Tactic

/-! The rotated weak jets bound the matrix elements of the rotation
commutator of the actual differentiated conormal family. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

@[expose] def actualPhysicalRotatedConormalEntry {Y : Set (X dim)} {d : Data dim}
    (D : ∀ x ∈ Y,ActualGaussFiberData d x) (i j : I dim) (f g : HarmonicFiniteCoefficients dim) (x : X dim) : ℝ :=
  if hx : x ∈ Y then ((d.radius x)^2)⁻¹*unitSphereArea dim *
    ∫ w : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 w*
      ((smoothSphereTraceRotation i j*(D x hx).conormalRemainder-
        (D x hx).conormalRemainder*smoothSphereTraceRotation i j) (finiteHarmonicSmoothTraceL f)).1 w
      ∂(sphereProbability dim)
  else 0

theorem ActualPhysicalRotatedConormalJet.matrix_entry_bound
    {Y : Set (X dim)} {d : Data dim} {x : X dim} {N : ℕ} {C : ℝ}
    {D : ∀ x ∈ Y, ActualGaussFiberData d x} {i j : I dim} (H : ActualPhysicalRotatedConormalJet d Y x N C D i j)
    (f g : HarmonicFiniteCoefficients dim) :
    let Q := actualPhysicalRotatedConormalEntry D i j f g
    let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
    ContDiffAt ℝ ∞ Q x ∧
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n Q x‖ ≤ C*(beta d.γ d.radius x)^n*‖L f‖*‖L g‖ := by
  dsimp only
  let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
  let E := weakHalfConormalEvaluateL (L f) (L g)
  let Q := actualPhysicalRotatedConormalEntry D i j f g
  have hEq : E ∘ H.form =ᶠ[𝓝 x] Q := by
    filter_upwards [H.openNeighborhood.mem_nhds H.center_mem] with y hy
    change H.form y (L f) (L g) = Q y
    unfold Q actualPhysicalRotatedConormalEntry
    rw [dite_eq_left (H.sub hy)]
    exact H.eq_finite y hy f g
  refine ⟨(E.contDiff.contDiffAt.comp x H.smooth).congr_of_eventuallyEq hEq.symm,fun n hn => ?_⟩
  rw [← (hEq.iteratedFDeriv ℝ n).eq_of_nhds]
  have h := E.norm_iteratedFDeriv_comp_left (H.smooth.of_le (by simp : (n:ℕ∞ω) ≤ ∞)) (n:=n) le_rfl
  have hC : 0 ≤ C*(beta d.γ d.radius x)^n := (norm_nonneg _).trans (H.bound n hn)
  exact (h.trans (mul_le_mul (norm_weakHalfConormalEvaluateL_le (L f) (L g)) (H.bound n hn)
    (norm_nonneg _) (by positivity))).trans_eq (by ring)


theorem actualPhysicalRotatedConormalEntry_trace_germ (hn : 3 ≤ dim) (hY : IsOpen Y)
    {x : X dim} (hx : x ∈ Y) (D : ∀ x ∈ Y,ActualGaussFiberData d x)
    (i j : I dim) (f g : HarmonicFiniteCoefficients dim) :
    actualPhysicalRotatedConormalEntry D i j f g =ᶠ[𝓝 x] fun y => unitSphereArea dim * ⟪smoothSphereTraceL2 hn
      (supportedFiberRotationComm (actualGaussScaledConormalFamily D) i j y (finiteHarmonicSmoothTraceL f)),
      smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ := by
  let F := actualGaussScaledConormalFamily D
  let G := supportedFiberRotationComm F i j
  filter_upwards [hY.mem_nhds hx] with y hy
  let T := (D y hy).conormalRemainder
  let R := smoothSphereTraceRotation (dim:=dim) i j
  let r := ((d.radius y)^2)⁻¹
  have hG' : G y = r • (R*T-T*R) := by
    simp only [G,F,T,R,r,supportedFiberRotationComm,actualGaussScaledConormalFamily,dite_eq_left hy,
      mul_smul_comm,smul_mul_assoc,smul_sub]
  change actualPhysicalRotatedConormalEntry D i j f g y = _
  unfold actualPhysicalRotatedConormalEntry
  change _ = unitSphereArea dim * ⟪smoothSphereTraceL2 hn (G y (finiteHarmonicSmoothTraceL f)),
    smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ
  rw [dite_eq_left hy,hG',LinearMap.smul_apply,map_smul,real_inner_smul_left,
    smoothSphereTraceL2_inner_eq_integral,finiteHarmonicSmoothTraceL_apply g]
  have hSwap : (∫ w : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 w*
      ((R*T-T*R) (finiteHarmonicSmoothTraceL f)).1 w ∂(sphereProbability dim)) =
      ∫ w : ↥(standardSphere dim),
        ((R*T-T*R) (finiteHarmonicSmoothTraceL f)).1 w*(harmonicFiniteSmooth g).1 w ∂(sphereProbability dim) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun w => mul_comm _ _)
  change r*unitSphereArea dim*(∫ w : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 w*
      ((R*T-T*R) (finiteHarmonicSmoothTraceL f)).1 w ∂(sphereProbability dim)) =
    unitSphereArea dim*(r*(∫ w : ↥(standardSphere dim),
      ((R*T-T*R) (finiteHarmonicSmoothTraceL f)).1 w*(harmonicFiniteSmooth g).1 w ∂(sphereProbability dim)))
  rw [hSwap]
  ring

theorem ActualPhysicalRotatedConormalJet.fiberDerivative_weak_pair (hn : 3 ≤ dim)
    (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y) {N : ℕ} (hN : 1 ≤ N) {C : ℝ}
    {D : ∀ x ∈ Y,ActualGaussFiberData d x} {i j : I dim}
    (H : ActualPhysicalRotatedConormalJet d Y x N C D i j)
    (hF : SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily D))
    (a : X dim) (ha : ‖a‖ ≤ 1) (f g : HarmonicFiniteCoefficients dim) :
    let T := smoothSupportedTraceFiberDerivative hY (actualGaussScaledConormalFamily D) hF a x
    let G := smoothSphereTraceRotation i j*T-T*smoothSphereTraceRotation i j
    let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
    |⟪smoothSphereTraceL2 hn (G (finiteHarmonicSmoothTraceL f)),
      smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ| ≤
      (C/unitSphereArea dim)*beta d.γ d.radius x*‖L f‖*‖L g‖ := by
  dsimp only
  let F := actualGaussScaledConormalFamily D
  let G := supportedFiberRotationComm F i j
  let hG := supportedFiberRotationComm_regular hY F hF i j
  let E := actualPhysicalRotatedConormalEntry D i j f g
  let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
  let β := beta d.γ d.radius x
  have h := H.matrix_entry_bound f g
  have hB : ‖iteratedFDeriv ℝ 1 E x‖ ≤ C*β*‖L f‖*‖L g‖ := by
    simpa only [pow_one] using h.2 1 hN
  have hEq := actualPhysicalRotatedConormalEntry_trace_germ hn hY hx D i j f g
  have hBound := abs_weak_fiberDerivative_pair_of_entry hn hY hx G hG a ha _ _ E _ hEq hB
  rw [supportedFiberRotationComm_derivative hn hY F hF i j a hx] at hBound
  exact hBound.trans_eq (by ring)

end CalderonN
