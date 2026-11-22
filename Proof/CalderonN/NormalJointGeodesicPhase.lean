module

public import Proof.CalderonN.NormalGeodesicVariation
public import Proof.CalderonN.EnlargedNormalInverse

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalJointGeodesicPhase.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The actual geodesic phase with both center and velocity retained as parameters. -/
@[expose] def normalJointPhase (expMap : (X dim) × (X dim) → (X dim)) (p : ((X dim) × (X dim)) × ℝ) : (X dim) × (X dim) :=
  (expMap (p.1.1,p.2 • p.1.2),fderiv ℝ expMap (p.1.1,p.2 • p.1.2) (0,p.1.2))

lemma normalJointPhase_eq_phase (expMap : (X dim) × (X dim) → (X dim)) (y v : (X dim)) (t : ℝ)
    (hE : DifferentiableAt ℝ expMap (y,t • v)) :
    normalJointPhase expMap ((y,v),t) = normalGeodesicPhase expMap y (v,t) := by
  have hF : HasFDerivAt (fun p : (X dim) × ℝ => p.1) (ContinuousLinearMap.fst ℝ (X dim) ℝ) (v,t) := hasFDerivAt_fst
  have hS : HasFDerivAt (fun p : (X dim) × ℝ => p.2) (ContinuousLinearMap.snd ℝ (X dim) ℝ) (v,t) := hasFDerivAt_snd
  have hScaled : HasFDerivAt (fun p : (X dim) × ℝ => p.2 • p.1)
      (t • ContinuousLinearMap.fst ℝ (X dim) ℝ+(ContinuousLinearMap.snd ℝ (X dim) ℝ).smulRight v) (v,t) := hS.smul hF
  have hd := hE.hasFDerivAt.comp (v,t) ((hasFDerivAt_const (𝕜:=ℝ) y (v,t)).prodMk hScaled)
  refine Prod.ext (by rfl) ?_
  have hh := congrArg (fun L : ((X dim) × ℝ) →L[ℝ] (X dim) => L (0,1)) hd.fderiv
  change fderiv ℝ (normalGeodesicPosition expMap y) (v,t) (0,1) =
    fderiv ℝ expMap (y,t • v) (0,t • (0:(X dim))+(1:ℝ) • v) at hh
  change fderiv ℝ expMap (y,t • v) (0,v) =
    fderiv ℝ (normalGeodesicPosition expMap y) (v,t) (0,1)
  simpa only [smul_zero,one_smul,zero_add] using hh.symm

lemma NormalCoordinates.contDiffAt_jointPhase {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (t : ℝ) (hv : t • v ∈ disk g y (R y)) :
    ContDiffAt ℝ ∞ (normalJointPhase expMap) ((y,v),t) := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ expMap (y,t • v) :=
    hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))
  have hInput : ContDiffAt ℝ ∞ (fun p : ((X dim) × (X dim)) × ℝ => (p.1.1,p.2 • p.1.2)) ((y,v),t) :=
    contDiffAt_fst.fst.prodMk (contDiffAt_snd.smul contDiffAt_fst.snd)
  have hVector : ContDiffAt ℝ ∞ (fun p : ((X dim) × (X dim)) × ℝ => ((0:(X dim)),p.1.2)) ((y,v),t) :=
    contDiffAt_const.prodMk contDiffAt_fst.snd
  exact (hE.comp ((y,v),t) hInput).prodMk (((hE.fderiv_right (m:=∞) (by simp)).comp ((y,v),t) hInput).clm_apply hVector)

lemma NormalCoordinates.jointPhase_eq_phase {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (t : ℝ) (hv : t • v ∈ disk g y (R y)) :
    normalJointPhase expMap ((y,v),t) = normalGeodesicPhase expMap y (v,t) := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  exact normalJointPhase_eq_phase expMap y v t
    ((hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))).differentiableAt (by simp))

lemma NormalCoordinates.hasDerivAt_jointPhase {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => normalJointPhase expMap ((y,v),s))
      (coordinateGeodesicSpray g (normalJointPhase expMap ((y,v),t))) t := by
  have hvT := smul_mem_disk_of_mem g y v (R y) t hv ht
  have hEq : (fun s => normalJointPhase expMap ((y,v),s)) =ᶠ[𝓝 t]
      (fun s => normalGeodesicPhase expMap y (v,s)) := by
    obtain ⟨U,hU,hTube,hReg⟩ := hN.1
    have hNear : ∀ᶠ s in 𝓝 t,(y,s • v) ∈ U :=
      (continuous_const.prodMk (continuous_id.smul continuous_const)).continuousAt.eventually
        (hU.mem_nhds (hTube ⟨hy,hvT⟩))
    filter_upwards [hNear] with s hs
    exact normalJointPhase_eq_phase expMap y v s
      ((hReg.contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp))
  have h := hN.hasDerivAt_phase hy v hv ht
  rw [← hN.jointPhase_eq_phase hy v t hvT] at h
  exact h.congr_of_eventuallyEq hEq

/-- A strict interior normal velocity remains in the admitted disks under a
    small simultaneous change of the center and initial velocity. -/
lemma NormalCoordinates.eventually_joint_disk {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v : (X dim)) (hv : metricPair g y v v < (R y)^2) :
    ∀ᶠ p : (X dim) × (X dim) in 𝓝 (y,v),p.1 ∈ Y ∧ p.2 ∈ disk g p.1 (R p.1) := by
  have hG (i j : (I dim)) : ContDiffAt ℝ ∞ (fun p : (X dim) × (X dim) => g p.1 i j) (y,v) := by
    have hgi : ContDiffAt ℝ ∞ (fun x : (X dim) => g x i j) y :=
      (hg.1 i j).contDiffAt (hΩ.mem_nhds (hN.center_mem hy))
    exact hgi.comp (y,v) contDiffAt_fst
  have hV (i : (I dim)) : ContDiffAt ℝ ∞ (fun p : (X dim) × (X dim) => p.2 i) (y,v) :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.contDiffAt.comp (y,v) contDiffAt_snd
  have hPair : ContinuousAt (fun p : (X dim) × (X dim) => metricPair g p.1 p.2 p.2) (y,v) := by
    exact (ContDiffAt.sum (fun i _ => ContDiffAt.sum
      (fun j _ => ((hG i j).mul (hV i)).mul (hV j)))).continuousAt
  have hDiff := hPair.sub ((hR.comp continuousAt_fst).pow 2)
  have hNear : ∀ᶠ p : (X dim) × (X dim) in 𝓝 (y,v),metricPair g p.1 p.2 p.2-(R p.1)^2 < 0 :=
    hDiff.eventually (isOpen_Iio.mem_nhds (sub_neg.mpr hv))
  have hBase : ∀ᶠ p : (X dim) × (X dim) in 𝓝 (y,v),p.1 ∈ Y :=
    continuousAt_fst.eventually (hY.mem_nhds hy)
  filter_upwards [hNear,hBase] with p hp hpy
  exact ⟨hpy,(sub_neg.mp hp).le⟩

/-- Full center/velocity variations of the actual normal map solve the linearized
    spray equation. The radius is used only to justify the local ODE germ. -/
theorem NormalCoordinates.hasDerivAt_joint_variation {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v a b : (X dim)) (hv : metricPair g y v v < (R y)^2)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => fderiv ℝ (normalJointPhase expMap) ((y,v),s) ((a,b),0))
      (fderiv ℝ (coordinateGeodesicSpray g) (normalJointPhase expMap ((y,v),t))
        (fderiv ℝ (normalJointPhase expMap) ((y,v),t) ((a,b),0))) t := by
  have hvd : v ∈ disk g y (R y) := hv.le
  have hvT := smul_mem_disk_of_mem g y v (R y) t hvd ht
  have hPhase := hN.contDiffAt_jointPhase hy v t hvT
  have hPos : (normalJointPhase expMap ((y,v),t)).1 ∈ Ω := hN.path_image hy v hvd ht
  have hSpray := (hg.contDiffAt_coordinateGeodesicSpray hΩ hK _ hPos).differentiableAt (by simp)
  have hODE : (fun p => fderiv ℝ (normalJointPhase expMap) (p,t) (0,1)) =ᶠ[𝓝 (y,v)]
      (fun p => coordinateGeodesicSpray g (normalJointPhase expMap (p,t))) := by
    filter_upwards [hN.eventually_joint_disk hY hΩ hg hy hR v hv] with p hp
    have hPx := hN.contDiffAt_jointPhase hp.1 p.2 t
      (smul_mem_disk_of_mem g p.1 p.2 (R p.1) t hp.2 ht)
    exact (hasDerivAt_time_slice (normalJointPhase expMap) p t (hPx.differentiableAt (by simp))).unique
      (hN.hasDerivAt_jointPhase hp.1 p.2 hp.2 ht)
  exact hasDerivAt_parameter_variation (normalJointPhase expMap) (coordinateGeodesicSpray g)
    (y,v) (a,b) t hPhase hSpray hODE

end CalderonN
