module

public import Proof.CalderonN.ActualFramedCenterVelocityRemainder
public import Proof.CalderonN.TraceFrameCoefficients

import Mathlib.Tactic

/-! Joint smoothness of the actual frame velocity along the physical
radius graph, obtained from the checked quadratic center expansion. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def actualPhysicalScaledVelocity (d : Data dim) (i : I dim) (p : X dim × X dim) : X dim :=
  scaledNormalTraceVelocity d.γ d.expMap d.frame p.1 (d.radius p.1)
    (fderiv ℝ d.radius p.1 (axis i)) p.2 (axis i)

theorem uniform_actual_physicalScaledVelocity_smooth
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ i : I dim,∀ p ∈ Y ×ˢ standardSphere dim,
        ContDiffAt ℝ ∞ (actualPhysicalScaledVelocity d i) p := by
  obtain ⟨η,_,hη,_,hVel⟩ := uniform_actual_framedCenterVelocity_radialRemainder hY hΩ hYc 0 hm
    K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,hη,?_⟩
  intro floor hf ε he hs d hd hFrame i p hp
  let U := Y ×ˢ ball (0:X dim) 2
  have hpU : p ∈ U := ⟨hp.1, by
    change dist p.2 0 < 2
    rw [dist_zero_right,mem_sphere_zero_iff_norm.mp hp.2]
    norm_num⟩
  have hU : IsOpen U := hY.prod isOpen_ball
  have hYO : Y ⊆ Ω := fun _ hx => hd.2.1.center_mem hx
  have hγ : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hYO,
    fun _ hx => hd.1.1.2 _ (hYO hx)⟩
  have hE (a : I dim) := (hd.1.2.2.2.2.2.2.1 a).mono hYO
  let r := d.radius
  let v (q : X dim × X dim) := ((q.1,r q.1),q.2)
  have hr := hd.2.2.2.2.1.1
  have hrU : ContDiffOn ℝ ∞ (fun q : X dim × X dim => r q.1) U :=
    hr.comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hv : ContDiffOn ℝ ∞ v U :=
    (contDiff_fst.contDiffOn.prodMk hrU).prodMk contDiff_snd.contDiffOn
  have hPack (q : X dim × X dim) (hq : q ∈ U) :=
    hVel floor hf ε he hs d hd hFrame q.1 hq.1 (r q.1)
      (by have h := (hd.2.2.2.2.1.2 q.1 hq.1).1; rw [abs_of_pos h]; linarith)
      q.2 (ball_subset_closedBall hq.2)
  let B (q : X dim × X dim) := actualFramedCenterVelocityRemainder d (v q) (axis i)
  have hB : ContDiffOn ℝ ∞ B U := by
    intro q hq
    have hR := (hPack q hq).1.smooth.comp_contDiffWithinAt q (hv q hq)
    exact hR.clm_apply contDiffWithinAt_const
  let E (q : X dim × X dim) (w : X dim) := frameCoordinatesL d.γ q.1 (d.frame q.1) w
  have hCoords (G : X dim × X dim → X dim) (hG : ContDiffOn ℝ ∞ G U) :
      ContDiffOn ℝ ∞ (fun q => E q (G q)) U := by
    apply (contDiffOn_piLp 2).mpr
    intro a
    have hPt (q : X dim × X dim) :
        E q (G q) a = ∑ b : I dim,G q b*traceFrameCoordinate d.γ d.frame a b q.1 := by
      let L := (EuclideanSpace.proj (𝕜:=ℝ) a).comp (frameCoordinatesL d.γ q.1 (d.frame q.1))
      change L (G q) = _
      calc
        L (G q) = L (∑ b : I dim,G q b • axis b) :=
          congrArg L (axis_sum_chart (G q)).symm
        _ = _ := by
          simp only [map_sum,map_smul,smul_eq_mul]
          rfl
    have hSum : ContDiffOn ℝ ∞ (fun q : X dim × X dim =>
        ∑ b : I dim,G q b*traceFrameCoordinate d.γ d.frame a b q.1) U :=
      ContDiffOn.sum fun b _ => ((EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.comp_contDiffOn hG).mul
        ((contDiffOn_traceFrameCoordinate hγ hE a b).comp contDiff_fst.contDiffOn (fun _ h => h.1))
    exact hSum.congr (fun q _ => hPt q)
  let b (x : X dim) := fderiv ℝ r x (axis i)
  have hb : ContDiffOn ℝ ∞ b Y :=
    (hr.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
  have hbU : ContDiffOn ℝ ∞ (fun q : X dim × X dim => b q.1) U :=
    hb.comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hSmooth : ContDiffOn ℝ ∞ (fun q : X dim × X dim =>
      E q (axis i)+b q.1 • q.2+(r q.1)^2 • E q (B q)) U :=
    ((hCoords _ contDiffOn_const).add (hbU.smul contDiff_snd.contDiffOn)).add
      ((hrU.pow 2).smul (hCoords B hB))
  exact (hSmooth.congr (fun q hq => (hPack q hq).2 (axis i) (b q.1))).contDiffAt (hU.mem_nhds hpU)

end CalderonN
