module

public import Proof.CalderonN.ActualPhysicalWeakConormalJets

import Proof.CalderonN.FiniteSmoothTraceAngularModel
import Mathlib.Tactic

/-! Evaluation of the physical weak conormal jets on fixed smooth
harmonic packets preserves the weighted derivative estimates. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def weakHalfConormalEvaluateL (f g : SphereSobolev dim (1/2:ℝ)) :
    WeakHalfConormal dim →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ g).comp (ContinuousLinearMap.apply ℝ _ f)

omit [Nontrivial (Fin dim)] in
theorem norm_weakHalfConormalEvaluateL_le (f g : SphereSobolev dim (1/2:ℝ)) :
    ‖weakHalfConormalEvaluateL f g‖ ≤ ‖f‖*‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro T
  change ‖T f g‖ ≤ ‖f‖*‖g‖*‖T‖
  exact (T.le_opNorm₂ f g).trans_eq (by ring)

@[expose] def actualPhysicalWeakConormalEntry {Y : Set (X dim)} {d : Data dim}
    (D : ∀ x ∈ Y,ActualGaussFiberData d x) (f g : HarmonicFiniteCoefficients dim) (x : X dim) : ℝ :=
  if hx : x ∈ Y then ((d.radius x)^2)⁻¹*unitSphereArea dim *
    ∫ w : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 w*
      ((D x hx).conormalRemainder (smoothSphereTrace (harmonicFiniteSmooth f))).1 w
      ∂(sphereProbability dim)
  else 0

theorem ActualPhysicalWeakConormalJet.matrix_entry_bound
    {Y : Set (X dim)} {d : Data dim} {x : X dim} {N : ℕ} {C : ℝ}
    {D : ∀ x ∈ Y, ActualGaussFiberData d x} (H : ActualPhysicalWeakConormalJet d Y x N C D)
    (f g : HarmonicFiniteCoefficients dim) :
    let Q := actualPhysicalWeakConormalEntry D f g
    let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
    ContDiffAt ℝ ∞ Q x ∧
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n Q x‖ ≤ C*(beta d.γ d.radius x)^n*‖L f‖*‖L g‖ := by
  dsimp only
  let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
  let E := weakHalfConormalEvaluateL (L f) (L g)
  let Q := actualPhysicalWeakConormalEntry D f g
  have hEq : E ∘ H.form =ᶠ[𝓝 x] Q := by
    filter_upwards [H.openNeighborhood.mem_nhds H.center_mem] with y hy
    change H.form y (L f) (L g) = Q y
    unfold Q actualPhysicalWeakConormalEntry
    rw [dite_eq_left (H.sub hy)]
    exact H.eq_finite y hy f g
  refine ⟨(E.contDiff.contDiffAt.comp x H.smooth).congr_of_eventuallyEq hEq.symm,fun n hn => ?_⟩
  rw [← (hEq.iteratedFDeriv ℝ n).eq_of_nhds]
  have h := E.norm_iteratedFDeriv_comp_left (H.smooth.of_le (by simp : (n:ℕ∞ω) ≤ ∞)) (n:=n) le_rfl
  have hC : 0 ≤ C*(beta d.γ d.radius x)^n := (norm_nonneg _).trans (H.bound n hn)
  exact (h.trans (mul_le_mul (norm_weakHalfConormalEvaluateL_le (L f) (L g)) (H.bound n hn)
    (norm_nonneg _) (by positivity))).trans_eq (by ring)

end CalderonN
