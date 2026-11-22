module

public import Proof.CalderonN.SmoothSupportedTraceHorizontal
public import Proof.CalderonN.MovingBallFamilies

import Proof.CalderonN.MetricSmooth
import Mathlib.Tactic

/-! Restriction of a physical sphere field to the common smooth
trace domain, for arbitrary real or imaginary components. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim}
variable (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
  (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)

@[expose] def TraceComponentMatches (e : Frame dim) (L : ℂ →L[ℝ] ℝ)
    (φ : Field dim) (u : SmoothSupportedTraceSection Y) : Prop :=
  ∀ x ∈ Y, ∀ z : UnitSphere dim,u.1 (x,z) = L (φ (x,frameVector e x z))

include hframe in
theorem supportedHorizontal_matches_physical
    (a : X dim → X dim) (ha : ContDiffOn ℝ ∞ a Y)
    {φ : Field dim} (hφ : smoothNear φ (bundle Y g)) (L : ℂ →L[ℝ] ℝ) (u : SmoothSupportedTraceSection Y)
    (hu : TraceComponentMatches e L φ u) :
    TraceComponentMatches e L (fun p => horizontal g φ p.1 p.2 (a p.1))
      (supportedHorizontal hY hg hK he a ha u) := by
  intro x hx z
  obtain ⟨G,hG,hRep⟩ := smoothSupportedTraceSection_repr u
  let F : X dim × X dim → ℂ := fun q => φ (q.1,frameVector e q.1 q.2)
  have hφ' : DifferentiableAt ℝ φ (x,frameVector e x z) := by
    obtain ⟨U,hU,hBU,hS⟩ := hφ
    exact (hS.contDiffAt (hU.mem_nhds (hBU
      ⟨hx,frameVector_mem_sphere g e x (hframe x hx) z⟩))).differentiableAt (by simp)
  have he' : ∀ j,DifferentiableAt ℝ (fun x => e x j) x :=
    fun j => ((he j).contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  have hF := differentiableAt_frame_pullback e φ x (z:X dim) he' hφ'
  have hω := frameConnection_skew hY hg hK e he hframe hx (a x)
  have hEq : ∀ y ∈ Y,∀ w : UnitSphere dim,(L ∘ F) (y,w) = G (y,w) :=
    fun y hy w => (hu y hy w).symm.trans (hRep y w)
  have hDer := fderiv_covariant_eq_of_eqOn_spheres hY hx z (L ∘ F) G
    (L.differentiableAt.comp _ hF) (hG.differentiable (by simp) _) hEq _ hω (a x)
  change _ = L (horizontal g φ x (frameVector e x z) (a x))
  rw [supportedHorizontal_apply_of_repr hY hg hK he hframe a ha u hG hRep hx,← hDer,
    horizontal_eq_frame_pullback g e φ x (z:X dim) (a x) he' (hframe x hx) hφ',
    fderiv_comp _ L.differentiableAt hF,L.fderiv]
  rfl

include hg he in
theorem contDiffOn_movingBallToFrame_local :
    ContDiffOn ℝ ∞ (movingBallToFrame g e) (Prod.fst ⁻¹' Y) := by
  let P := X dim × X dim
  let U : Set P := Prod.fst ⁻¹' Y
  have hCoords : ContDiffOn ℝ ∞ (fun q : P => frameCoordinates g q.1 (e q.1) q.2) U := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    change ContDiffOn ℝ ∞ (fun q : P => metricPair g q.1 q.2 (e q.1 i)) U
    exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
      (((hg.1 j k).comp contDiff_fst.contDiffOn (fun _ h => h)).mul
        ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp contDiff_snd).contDiffOn).mul
          ((contDiffOn_vector_component _ (he i) k).comp contDiff_fst.contDiffOn (fun _ h => h))
  exact contDiff_fst.contDiffOn.prodMk hCoords

include he in
theorem contDiffOn_movingBallFromFrame_local :
    ContDiffOn ℝ ∞ (movingBallFromFrame e) (Prod.fst ⁻¹' Y) := by
  let P := X dim × X dim
  let U : Set P := Prod.fst ⁻¹' Y
  have hVec : ContDiffOn ℝ ∞ (fun q : P => frameVector e q.1 q.2) U := by
    unfold frameVector
    exact ContDiffOn.sum fun i _ =>
      (((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp contDiff_snd).contDiffOn).smul
        ((he i).comp contDiff_fst.contDiffOn (fun _ h => h))
  exact contDiff_fst.contDiffOn.prodMk hVec

include hY hg he hframe in
theorem exists_physical_real_trace_representative (u : SmoothSupportedTraceSection Y) :
    ∃ φ : Field dim, smoothNear φ (bundle Y g) ∧ TraceComponentMatches e Complex.reCLM φ u := by
  obtain ⟨G,hG,hRep⟩ := smoothSupportedTraceSection_repr u
  let φ : Field dim := fun p => (G (movingBallToFrame g e p) : ℂ)
  refine ⟨φ,⟨Prod.fst ⁻¹' Y,hY.preimage continuous_fst,fun _ hq => hq.1,?_⟩,?_⟩
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hG.comp_contDiffOn (contDiffOn_movingBallToFrame_local hg he))
  · intro x hx z
    have hz := movingBallToFrame_fromFrame (w:=(z:X dim)) (hframe x hx)
    change u.1 (x,z) = G (movingBallToFrame g e (movingBallFromFrame e (x,z)))
    rw [hz]
    exact hRep x z

end CalderonN
