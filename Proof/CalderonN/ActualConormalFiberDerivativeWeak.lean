module

public import Proof.CalderonN.ActualSupportedConormalRemainder
public import Proof.CalderonN.PhysicalConormalMatrixJetBounds
public import Proof.CalderonN.SmoothSupportedFiberMatrixDerivative

import Proof.CalderonN.SmoothTraceSobolevCompletion
import Mathlib.Tactic

/-! The weak matrix-entry bounds control the actual derivative
of the scaled conormal fiber operator. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem smoothSphereTraceL2_inner_eq_integral (hn : 3 ≤ dim) (u v : SmoothSphereTrace dim) :
    ⟪smoothSphereTraceL2 hn u,smoothSphereTraceL2 hn v⟫_ℝ =
      ∫ w : ↥(standardSphere dim),u.1 w*v.1 w ∂(sphereProbability dim) := by
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  obtain ⟨g,rfl⟩ := smoothSphereTraceL_surjective v
  let u : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  let v : SmoothData dim := ⟨g.1,smoothBallData_contDiff g⟩
  change ⟪smoothSphereTraceL2 hn (smoothSphereTrace u),smoothSphereTraceL2 hn (smoothSphereTrace v)⟫_ℝ =
    ∫ w : ↥(standardSphere dim),(smoothSphereTrace u).1 w*(smoothSphereTrace v).1 w ∂(sphereProbability dim)
  simp only [smoothSphereTraceL2_apply,smoothSphereTrace_apply,smoothSphereLift_inner]
  rfl

theorem abs_weak_fiberDerivative_pair_of_entry (hn : 3 ≤ dim)
    (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y)
    (F : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hF : SmoothSupportedTraceFiberRegular Y F)
    (a : X dim) (ha : ‖a‖ ≤ 1) (u v : SmoothSphereTrace dim) (E : X dim → ℝ) (C : ℝ)
    (hE : E =ᶠ[𝓝 x] fun y => unitSphereArea dim *
      ⟪smoothSphereTraceL2 hn (F y u),smoothSphereTraceL2 hn v⟫_ℝ)
    (hB : ‖iteratedFDeriv ℝ 1 E x‖ ≤ C) :
    |⟪smoothSphereTraceL2 hn (smoothSupportedTraceFiberDerivative hY F hF a x u),
      smoothSphereTraceL2 hn v⟫_ℝ| ≤ C/unitSphereArea dim := by
  let p (y : X dim) := ⟪smoothSphereTraceL2 hn (F y u),smoothSphereTraceL2 hn v⟫_ℝ
  let σ := unitSphereArea dim
  have hσ : 0 < σ := unitSphereArea_pos
  have hp := (contDiffAt_smoothTrace_fiber_matrix_element hn hY hx F hF u v).differentiableAt (by simp)
  have hT : fderiv ℝ E x a = σ*fderiv ℝ p x a := by
    rw [hE.fderiv_eq]
    change DifferentiableAt ℝ p x at hp
    change fderiv ℝ (σ • p) x a = _
    rw [(hp.hasFDerivAt.const_smul σ).fderiv]
    rfl
  rw [norm_iteratedFDeriv_one] at hB
  have hA : |fderiv ℝ E x a| ≤ C := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ E x).le_opNorm a).trans
      ((mul_le_of_le_one_right (norm_nonneg _) ha).trans hB)
  rw [hT,abs_mul,abs_of_pos hσ] at hA
  rw [← fderiv_smoothTrace_fiber_matrix_element hn hY hx F hF a u v]
  exact (le_div_iff₀ hσ).mpr (by rwa [mul_comm])

theorem actualPhysicalWeakConormalEntry_trace_germ (hn : 3 ≤ dim) (hY : IsOpen Y)
    {x : X dim} (hx : x ∈ Y) (D : ∀ x ∈ Y,ActualGaussFiberData d x)
    (f g : HarmonicFiniteCoefficients dim) :
    actualPhysicalWeakConormalEntry D f g =ᶠ[𝓝 x] fun y => unitSphereArea dim * ⟪smoothSphereTraceL2 hn
      ((actualGaussScaledConormalFamily D y) (finiteHarmonicSmoothTraceL f)),
      smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ := by
  filter_upwards [hY.mem_nhds hx] with y hy
  unfold actualPhysicalWeakConormalEntry actualGaussScaledConormalFamily
  rw [dite_eq_left hy,dite_eq_left hy,LinearMap.smul_apply,map_smul,real_inner_smul_left,
    smoothSphereTraceL2_inner_eq_integral,finiteHarmonicSmoothTraceL_apply f,finiteHarmonicSmoothTraceL_apply g]
  simp only [smoothSphereTrace_apply]
  have hSwap : (∫ w : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 w*
      ((D y hy).conormalRemainder (smoothSphereTrace (harmonicFiniteSmooth f))).1 w ∂(sphereProbability dim)) =
      ∫ w : ↥(standardSphere dim),
        ((D y hy).conormalRemainder (smoothSphereTrace (harmonicFiniteSmooth f))).1 w*
          (harmonicFiniteSmooth g).1 w ∂(sphereProbability dim) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun w => mul_comm _ _)
  rw [hSwap]
  ring

theorem ActualPhysicalWeakConormalJet.fiberDerivative_weak_pair (hn : 3 ≤ dim)
    (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y) {N : ℕ} (hN : 1 ≤ N) {C : ℝ}
    {D : ∀ x ∈ Y,ActualGaussFiberData d x} (H : ActualPhysicalWeakConormalJet d Y x N C D)
    (hF : SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily D))
    (a : X dim) (ha : ‖a‖ ≤ 1) (f g : HarmonicFiniteCoefficients dim) :
    let T := smoothSupportedTraceFiberDerivative hY (actualGaussScaledConormalFamily D) hF a x
    let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
    |⟪smoothSphereTraceL2 hn (T (finiteHarmonicSmoothTraceL f)),
      smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ| ≤
      (C/unitSphereArea dim)*beta d.γ d.radius x*‖L f‖*‖L g‖ := by
  dsimp only
  let E := actualPhysicalWeakConormalEntry D f g
  let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
  let β := beta d.γ d.radius x
  have h := H.matrix_entry_bound f g
  have hB : ‖iteratedFDeriv ℝ 1 E x‖ ≤ C*β*‖L f‖*‖L g‖ := by
    simpa only [pow_one] using h.2 1 hN
  have hEq := actualPhysicalWeakConormalEntry_trace_germ hn hY hx D f g
  exact (abs_weak_fiberDerivative_pair_of_entry hn hY hx _ hF a ha _ _ E _ hEq hB).trans_eq (by ring)

end CalderonN
