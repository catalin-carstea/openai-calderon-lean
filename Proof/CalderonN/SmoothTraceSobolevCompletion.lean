module

public import Proof.CalderonN.FiniteSmoothTraceAngularModel
public import Proof.CalderonN.SmoothTraceLinearAdjunction

import Proof.CalderonN.ActualFiniteRadialMidpoint
import Mathlib.Tactic

/-! Finite harmonic testing and interpolation for compatible maps on
the same smooth trace core. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 5900000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

def smoothSphereTraceRepresentative (u : SmoothSphereTrace dim) : SmoothData dim :=
  let v := Classical.choose (smoothSphereTraceL_surjective u)
  ⟨v.1,smoothBallData_contDiff v⟩

theorem smoothSphereTrace_representative (u : SmoothSphereTrace dim) :
    smoothSphereTrace (smoothSphereTraceRepresentative u) = u :=
  Classical.choose_spec (smoothSphereTraceL_surjective u)

theorem abs_smoothTrace_inner_le_sobolev (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2) (hns : -s ≤ 2)
    (u v : SmoothSphereTrace dim) :
    |⟪smoothSphereTraceL2 hn u,smoothSphereTraceL2 hn v⟫_ℝ| ≤
      ‖smoothSphereTraceSobolev hn (-s) hns u‖*‖smoothSphereTraceSobolev hn s hs v‖ := by
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  obtain ⟨g,rfl⟩ := smoothSphereTraceL_surjective v
  let F : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  let G : SmoothData dim := ⟨g.1,smoothBallData_contDiff g⟩
  change |⟪smoothSphereTraceL2 hn (smoothSphereTrace F),smoothSphereTraceL2 hn (smoothSphereTrace G)⟫_ℝ| ≤
    ‖smoothSphereTraceSobolev hn (-s) hns (smoothSphereTrace F)‖*
      ‖smoothSphereTraceSobolev hn s hs (smoothSphereTrace G)‖
  rw [smoothSphereTraceL2_apply,smoothSphereTraceL2_apply,smoothSphereTraceSobolev_apply,
    smoothSphereTraceSobolev_apply,smoothSphereLift_inner]
  exact abs_integral_mul_le_smoothBoundarySobolev hn s hs hns F G

theorem smoothSphereTraceSobolev_inclusion (hn : 3 ≤ dim) (s t : ℝ) (hs : s ≤ 2) (ht : t ≤ 2)
    (hts : t ≤ s) (u : SmoothSphereTrace dim) :
    sphereSobolevInclusionL s t hts (smoothSphereTraceSobolev hn s hs u) =
      smoothSphereTraceSobolev hn t ht u := by
  obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective u
  let f : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  change sphereSobolevInclusionL s t hts (smoothSphereTraceSobolev hn s hs (smoothSphereTrace f)) =
    smoothSphereTraceSobolev hn t ht (smoothSphereTrace f)
  rw [smoothSphereTraceSobolev_apply,smoothSphereTraceSobolev_apply]
  exact sphereSobolevInclusionL_smoothBoundarySobolev hn s t hs ht hts f

theorem norm_finite_smoothTrace_midpoint (hn : 3 ≤ dim) (T : Module.End ℝ (SmoothSphereTrace dim))
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (h₀ : ∀ f, ‖smoothSphereTraceSobolev hn (-(1/2) : ℝ) (by norm_num)
      (T (finiteHarmonicSmoothTraceL f))‖ ≤ C₀*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖)
    (h₁ : ∀ f, ‖smoothSphereTraceSobolev hn (1/2 : ℝ) (by norm_num)
      (T (finiteHarmonicSmoothTraceL f))‖ ≤ C₁*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖)
    (f : HarmonicFiniteCoefficients dim) :
    ‖smoothSphereTraceSobolev hn 0 (by norm_num) (T (finiteHarmonicSmoothTraceL f))‖ ≤
      ((C₀+C₁)/2)*‖harmonicBoundaryFiniteL 1 f‖ := by
  let P (s : ℝ) (hs : s ≤ 2) := (smoothSphereTraceSobolev hn s hs).comp (T.comp finiteHarmonicSmoothTraceL)
  have hneg : (-1/2 : ℝ) = -(1/2) := by ring
  have h₀' : ∀ g, ‖P (-1/2 : ℝ) (by norm_num) g‖ ≤ C₀*‖harmonicBoundaryFiniteL (1/2 : ℝ) g‖ := by
    intro g
    change ‖smoothSphereTraceSobolev hn (-1/2 : ℝ) (by norm_num) (T (finiteHarmonicSmoothTraceL g))‖ ≤ _
    exact Eq.rec (motive:=fun s _ => ∀ hs : s ≤ 2,
      ‖smoothSphereTraceSobolev hn s hs (T (finiteHarmonicSmoothTraceL g))‖ ≤
        C₀*‖harmonicBoundaryFiniteL (1/2 : ℝ) g‖) (fun _ => h₀ g) hneg.symm (by norm_num)
  exact norm_finiteSphere_midpoint_le (P (-1/2 : ℝ) (by norm_num)) (P 0 (by norm_num)) (P (1/2 : ℝ) (by norm_num))
    (fun g => smoothSphereTraceSobolev_inclusion hn 0 (-1/2 : ℝ) (by norm_num) (by norm_num) (by norm_num) _)
    (fun g => smoothSphereTraceSobolev_inclusion hn (1/2 : ℝ) (-1/2 : ℝ) (by norm_num) (by norm_num) (by norm_num) _)
    C₀ C₁ hC₀ hC₁ h₀' h₁ f

theorem smoothSphereTraceSobolev_order_eq (hn : 3 ≤ dim) {s t : ℝ}
    (h : s = t) (hs : s ≤ 2) (ht : t ≤ 2) (u : SmoothSphereTrace dim) :
    smoothSphereTraceSobolev hn s hs u = (smoothSphereTraceSobolev hn t ht u : SphereSobolev dim s) := by
  subst t
  rfl

theorem norm_smoothTraceOperator_le_of_finite (hn : 3 ≤ dim) (s t : ℝ)
    (hs : s ≤ 2) (ht : t ≤ 2) (hnt : -t ≤ 2)
    (T Tad : Module.End ℝ (SmoothSphereTrace dim)) (hAdj : SmoothTraceAdjoint hn T Tad)
    (C : ℝ) (hC : 0 ≤ C)
    (hFin : ∀ f, ‖smoothSphereTraceSobolev hn t ht (T (finiteHarmonicSmoothTraceL f))‖ ≤
      C*‖harmonicBoundaryFiniteL s f‖)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn t ht (T u)‖ ≤ C*‖smoothSphereTraceSobolev hn s hs u‖ := by
  let Z (w : SmoothData dim) := smoothSphereLift w.1 w.2
  let F (w : SmoothData dim) := smoothSphereTraceRepresentative (T (smoothSphereTrace w))
  let G (w : SmoothData dim) := smoothSphereTraceRepresentative (Tad (smoothSphereTrace w))
  let L := smoothSphereTraceL2 (dim:=dim) hn
  have hF (w : SmoothData dim) : Z (F w) = L (T (smoothSphereTrace w)) := by
    change Z (F w) = L (T (smoothSphereTrace w))
    rw [← smoothSphereTrace_representative (T (smoothSphereTrace w)),smoothSphereTraceL2_apply]
  have hG (w : SmoothData dim) : Z (G w) = L (Tad (smoothSphereTrace w)) := by
    change Z (G w) = L (Tad (smoothSphereTrace w))
    rw [← smoothSphereTrace_representative (Tad (smoothSphereTrace w)),smoothSphereTraceL2_apply]
  have hAdj' (x y : SmoothData dim) : ⟪Z (F x),Z y⟫_ℝ = ⟪Z x,Z (G y)⟫_ℝ := by
    rw [hF,hG,show Z y = L (smoothSphereTrace y) from (smoothSphereTraceL2_apply hn y).symm,
      show Z x = L (smoothSphereTrace x) from (smoothSphereTraceL2_apply hn x).symm]
    exact hAdj (smoothSphereTrace x) (smoothSphereTrace y)
  have hPair (f g : HarmonicFiniteCoefficients dim) :
      |⟪Z (F (harmonicFiniteSmooth f)),finiteHarmonicSphereL hn g⟫_ℝ| ≤
        C*‖harmonicBoundaryFiniteL s f‖*‖harmonicBoundaryFiniteL (-t) g‖ := by
    rw [hF,finiteHarmonicSphereL_apply,
      ← smoothSphereTraceL2_apply hn (harmonicFiniteSmooth g),← finiteHarmonicSmoothTraceL_apply f,
      ← finiteHarmonicSmoothTraceL_apply g]
    have H := abs_smoothTrace_inner_le_sobolev hn (-t) hnt (by linarith)
      (T (finiteHarmonicSmoothTraceL f)) (finiteHarmonicSmoothTraceL g)
    have hc : smoothSphereTraceSobolev hn (- -t) (by linarith) (T (finiteHarmonicSmoothTraceL f)) =
        (smoothSphereTraceSobolev hn t ht (T (finiteHarmonicSmoothTraceL f)) : SphereSobolev dim (- -t)) := by
      exact smoothSphereTraceSobolev_order_eq hn (neg_neg t) _ ht _
    rw [finiteHarmonicSmoothTraceL_sobolev,hc] at H
    exact H.trans (mul_le_mul_of_nonneg_right (hFin f) (norm_nonneg _))
  have hAll := abs_smooth_pair_le_of_finite_harmonic hn F G hAdj' s (-t) C hs hnt hPair
  let U := smoothSphereTraceRepresentative u
  let V := F U
  have hU : smoothSphereTrace U = u := smoothSphereTrace_representative u
  have hV : smoothSphereTrace V = T u := by
    change smoothSphereTrace (smoothSphereTraceRepresentative (T (smoothSphereTrace U))) = T u
    rw [smoothSphereTrace_representative,hU]
  have hNorm := norm_smoothBoundarySobolev_le_of_finite_tests hn (-t) hnt (by linarith) V
    (C*‖smoothBoundarySobolev hn s hs U‖) (by positivity) (fun g => by
      have h := hAll U (harmonicFiniteSmooth g)
      rw [smoothSphereLift_inner,smoothBoundarySobolev_harmonicFiniteSmooth] at h
      exact h)
  rw [smoothBoundarySobolev_order_eq hn (neg_neg t) _ ht,← smoothSphereTraceSobolev_apply,← smoothSphereTraceSobolev_apply,
    hU,hV] at hNorm
  exact hNorm

end CalderonN
