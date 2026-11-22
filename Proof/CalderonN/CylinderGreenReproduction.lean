module

public import Proof.CalderonN.NormalGreenTransfer
public import Proof.CalderonN.NormalGreenFlux
public import Proof.CalderonN.MovingSphere.GreenContinuation
public import Proof.CalderonN.DilatedGreenBounds
import Proof.CalderonN.LowerCrossGreen

import Proof.CalderonN.CrossProductWeak
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.CylinderCutoff
import Proof.CalderonN.DilationHarmonic
import Proof.CalderonN.ChartUniqueContinuation
import Proof.CalderonN.MetricPair
import Mathlib.Tactic

/-! Adapted from `CylinderGreenReproduction` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2200000

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

open FixedTube MovingSphere

private theorem convex_coordinateCylinder : Convex ℝ (coordinateCylinder normal) := by
  intro x hx y hy a b ha hb hab
  have hquad (s t : ℝ) : (a*s+b*t)^2 ≤ a*s^2+b*t^2 := by
    have he : (a*s+b*t)^2 = a*s^2+b*t^2-a*b*(s-t)^2 := by
      linear_combination (a*s^2+b*t^2) * hab
    rw [he]
    exact sub_le_self _ (mul_nonneg (mul_nonneg ha hb) (sq_nonneg _))
  have hSum : transversePair normal (a • x + b • y) (a • x + b • y) ≤
      a * transversePair normal x x + b * transversePair normal y y := by
    simp only [transversePair,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib,← pow_two]
    exact Finset.sum_le_sum fun i _ => hquad (x i) (y i)
  change transversePair normal (a • x + b • y) (a • x + b • y) ≤ 1 ∧
    -1 ≤ a*x normal+b*y normal ∧ a*x normal+b*y normal ≤ 1
  exact ⟨hSum.trans (by linarith [mul_le_mul_of_nonneg_left hx.1 ha,mul_le_mul_of_nonneg_left hy.1 hb]),
    by linarith [mul_le_mul_of_nonneg_left hx.2.1 ha,mul_le_mul_of_nonneg_left hy.2.1 hb],
    by linarith [mul_le_mul_of_nonneg_left hx.2.2 ha,mul_le_mul_of_nonneg_left hy.2.2 hb]⟩

private theorem cylinder_lower_open_nonempty :
    ({y : X dim | y normal < -(1/4 : ℝ)} ∩ interior (coordinateCylinder normal)).Nonempty := by
  let z : X dim := (-(1/2 : ℝ)) • axis normal
  have hv : z normal = -(1/2 : ℝ) := by simp [z,axis]
  have hz : transversePair normal z z = 0 := by
    unfold transversePair
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i ≠ normal := Finset.ne_of_mem_erase hi
    simp [z,axis,PiLp.single_apply,hne]
  refine ⟨z,show z normal < -(1/4 : ℝ) by rw [hv]; norm_num,?_⟩
  exact mem_coordinateCylinder_interior (by rw [hz]; norm_num)
    (by rw [hv]; norm_num) (by rw [hv]; norm_num)

theorem NormalCoordinates.mono_ambient {Y Ω Ω' : Set (X dim)}
    {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω γ E r) (h : Ω ⊆ Ω') : NormalCoordinates Y Ω' γ E r := by
  refine ⟨hN.1,fun y hy => ?_⟩
  obtain ⟨hr,hi,hLoc⟩ := hN.2 y hy
  exact ⟨hr,hi,fun v hv => ⟨h (hLoc v hv).1,(hLoc v hv).2⟩⟩

/-- Small dilations carry the fixed lower part of the cylinder into the
known side and the full ambient ball into the original chart. -/
theorem eventually_cylinder_green_chart
    {Ω W : Set (X dim)} (hΩ : IsOpen Ω) (hside : ContainsAlignedSide normal Ω W) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ball (0 : (X dim)) 3 ⊆ {x | lam • x ∈ Ω} ∧
      ∀ y ∈ interior (coordinateCylinder normal), y normal < -(1/4 : ℝ) → lam • y ∈ W := by
  have hLower := eventually_dilated_mem_side_of_negative_coordinate hside 3 (by norm_num : (0 : ℝ) < 1/4)
  obtain ⟨U,s,hU,h₀U,hUΩ,hs,hs₀,hD,hW⟩ := hside
  have hChart : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ x ∈ closedBall (0 : (X dim)) 3, lam • x ∈ Ω := by
    apply (isCompact_closedBall (0 : (X dim)) 3).eventually_forall_of_forall_eventually
    intro x _
    have hcont : ContinuousAt (fun q : ℝ × (X dim) => q.1 • q.2) (0,x) :=
      (continuous_fst.smul continuous_snd).continuousAt
    exact hcont.preimage_mem_nhds (by simpa only [zero_smul] using hΩ.mem_nhds (hUΩ h₀U))
  filter_upwards [hChart,hLower] with lam hLam hSide hpos
  exact ⟨fun x hx => hLam x (ball_subset_closedBall hx),
    fun y hy hlo => hSide hpos y
      ((closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 3))
        (coordinateCylinder_subset_closedBall (interior_subset hy))) hlo.le⟩

set_option maxHeartbeats 1200000 in
/-- A Green continuation on the literal cylinder spheres transfers every
globally paired harmonic function. The value is represented locally by
any admissible compact test on that same sphere family. -/
theorem exists_cylinder_green_cutoffs_reproduce (hn : 3 ≤ dim)
    {Ω W : Set (X dim)} (hΩ : IsOpen Ω)
    {g₁ g₂ γ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hγ : SmoothMetric univ γ)
    {G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁)
    {lam : ℝ} (hlam : 0 < lam)
    (hChart : ball (0 : (X dim)) 3 ⊆ {x | lam • x ∈ Ω})
    (hLower : ∀ y ∈ interior (coordinateCylinder normal), y normal < -(1/4 : ℝ) → lam • y ∈ W)
    {E : (X dim) × (X dim) → (X dim)} (hE : Continuous E) {ρ : ℝ}
    (hNorm : NormalCoordinates (interior (coordinateCylinder normal)) (ball (0 : (X dim)) 3) γ E (fun _ => ρ))
    {Y' : Set (X dim)} (hY' : interior (coordinateCylinder normal) ⊆ Y')
    {r : (X dim) → ℝ} (hrc : ContinuousOn r (interior (coordinateCylinder normal)))
    (hr : ∀ y ∈ interior (coordinateCylinder normal), 0 < r y ∧ r y < ρ)
    {e : (Frame dim)} (he : ∀ y ∈ interior (coordinateCylinder normal), ∀ i j,
      metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContinuousOn (fun y => e y i) (interior (coordinateCylinder normal)))
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O)
    {F : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O F)
    (hSphere : ∀ y ∈ interior (coordinateCylinder normal), ∀ w : ↥(standardSphere dim),
      (E (y,r y • frameVector e y w),y) ∈ O)
    (hKnown : EqOn F (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal (normalPairDomain Y' γ ρ E))) :
    let Y := interior (coordinateCylinder normal)
    let D := {x : (X dim) | lam • x ∈ Ω}
    let N := normalPairDomain Y γ ρ E
    ∃ V : (X dim) × (X dim) → (X dim), IsOpen N ∧ N ⊆ D ×ˢ Y ∧ ContDiffOn ℝ ∞ V N ∧
      (∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2) ∧
      (∀ q ∈ N, (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1) ∧
      ∀ {u v : (X dim) → ℝ}, Harmonic D (dilatedMetric g₁ lam) u →
        Harmonic D (dilatedMetric g₂ lam) v → EqOn u v {y | lam • y ∈ W} →
        (∀ y ∈ Y, ∃ η φ, NormalGreenCutoff Y γ ρ E V O r u y η φ) ∧
        ∀ y ∈ Y, ∀ η φ, NormalGreenCutoff Y γ ρ E V O r u y η φ →
          greenCutoffPairing (dilatedMetric g₁ lam) F φ y = v y := by
  let Y := interior (coordinateCylinder normal)
  let D := {x : (X dim) | lam • x ∈ Ω}
  let N := normalPairDomain Y γ ρ E
  let gA := dilatedMetric g₁ lam
  let gB := dilatedMetric g₂ lam
  let U := {y : (X dim) | y normal < -(1/4 : ℝ)} ∩ Y
  have hY : IsOpen Y := isOpen_interior
  have hU : IsOpen U := (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) normal).continuous continuous_const).inter hY
  have hD : IsOpen D := hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous)
  have hYD : Y ⊆ D := (interior_subset.trans
    ((coordinateCylinder_subset_closedBall (normal := normal)).trans (closedBall_subset_ball (by norm_num)))).trans hChart
  have hgA : SmoothMetric univ gA := by simpa only [mem_univ, ofPred_true] using smoothMetric_dilated hg₁ lam
  have hgB : SmoothMetric Y gB :=
    smoothMetric_restrict (smoothMetric_dilated (smoothMetric_restrict hg₂ (subset_univ Ω)) lam) hYD
  obtain ⟨hN,hNball,V,hV,hExact,hInv⟩ :=
    exists_normal_inverse_velocity hY (smoothMetric_restrict hγ (subset_univ Y)) hNorm
  have hND : N ⊆ D ×ˢ Y := hNball.trans (Set.prod_mono hChart Subset.rfl)
  have hG := hG₁.dilated (by omega : 2 ≤ dim) hΩ (smoothMetric_restrict hg₁ (subset_univ Ω)) hlam
  refine ⟨V,hN,hND,hV,hExact,hInv,?_⟩
  intro u v hu hv heq
  obtain ⟨T,hT,hEq⟩ := exists_harmonic_normalGreenTransfer hY hD hγ hgA hE hN hND hV.continuousOn
    hExact hInv hO hF he hec hrc hr hSphere hu
  have hTests (y : (X dim)) (hy : y ∈ Y) : ∃ η φ, NormalGreenCutoff Y γ ρ E V O r u y η φ := by
    obtain ⟨η,φ,hφ⟩ := exists_eventually_normalGreenCutoff hY hD hγ hE hN hND hV.continuousOn
      hExact hInv hO hy he (fun i => (hec i).continuousAt (hY.mem_nhds hy))
      (hrc.continuousAt (hY.mem_nhds hy)) (hr _ hy).1 (hr _ hy).2 (hSphere y hy) hu.1
    have hMem : y ∈ {z : (X dim) | NormalGreenCutoff Y γ ρ E V O r u z η φ} :=
      mem_of_mem_nhds hφ
    exact ⟨η,φ,hMem⟩
  have hConn : IsConnected Y :=
    ((convex_coordinateCylinder (normal := normal)).interior).isConnected (cylinder_lower_open_nonempty.mono inter_subset_right)
  have hTy : EqOn T v U := by
    intro y hy
    obtain ⟨η,φ,hφ⟩ := hTests y hy.2
    have hyW := hLower y hy.2 hy.1
    have hCenter : E (y,(0 : (X dim))) = y := by
      have hz : (0 : (X dim)) ∈ disk γ y ρ := by simp [disk,metricPair,sq_nonneg]
      simpa only [zero_smul] using ((hNorm.2 y hy.2).2.2 0 hz).2.2.1
    refine (hEq y hy.2 η φ hφ).trans ((hφ.pairing_eq_value hD hND hExact hInv hy.2 hCenter hu hG ?_).trans (heq hyW))
    intro x hx hxy
    have hx' : (x,y) ∈ normalPairDomain Y' γ ρ E := by
      obtain ⟨z,hz,heq⟩ := hx
      exact ⟨z,⟨hY' hz.1,hz.2⟩,heq⟩
    exact (hKnown ⟨⟨hx',hy.1⟩,hxy⟩).trans (dilatedInitialGreen_eq_left _ _ hyW)
  have hAll := harmonic_eqOn_of_eqOn_open hY hConn hU cylinder_lower_open_nonempty
    inter_subset_right hgB hT ⟨hv.1.mono hYD,fun y hy => hv.2 y (hYD hy)⟩ hTy
  exact ⟨hTests,fun y hy η φ hφ => (hEq y hy η φ hφ).symm.trans (hAll hy)⟩

/-- The actual first-metric sphere flux reproduces harmonic pairs on
the entire connected cylinder. -/
theorem cylinderGreenFlux_reproduces (hn : 3 ≤ dim)
    {Ω W : Set (X dim)} (hΩ : IsOpen Ω)
    {g₁ g₂ γ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hγ : SmoothMetric univ γ)
    {G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁)
    {lam : ℝ} (hlam : 0 < lam)
    (hChart : ball (0 : (X dim)) 3 ⊆ {x | lam • x ∈ Ω})
    (hLower : ∀ y ∈ interior (coordinateCylinder normal), y normal < -(1/4 : ℝ) → lam • y ∈ W)
    {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E) {ρ : ℝ}
    (hNorm : NormalCoordinates (interior (coordinateCylinder normal)) (ball (0 : (X dim)) 3) γ E (fun _ => ρ))
    {Y' : Set (X dim)} (hY' : interior (coordinateCylinder normal) ⊆ Y')
    {r : (X dim) → ℝ} (hrc : ContinuousOn r (interior (coordinateCylinder normal)))
    (hr : ∀ y ∈ interior (coordinateCylinder normal), 0 < r y ∧ r y < ρ)
    {e : (Frame dim)} (he : ∀ y ∈ interior (coordinateCylinder normal), ∀ i j,
      metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContinuousOn (fun y => e y i) (interior (coordinateCylinder normal)))
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O)
    {F : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O F)
    (hSphere : ∀ y ∈ interior (coordinateCylinder normal), ∀ w : ↥(standardSphere dim),
      (E (y,r y • frameVector e y w),y) ∈ O)
    (hKnown : EqOn F (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal (normalPairDomain Y' γ ρ E))) :
    let D := {x : (X dim) | lam • x ∈ Ω}
    ∀ {u v : (X dim) → ℝ}, Harmonic D (dilatedMetric g₁ lam) u →
      Harmonic D (dilatedMetric g₂ lam) v → EqOn u v {y | lam • y ∈ W} →
      EqOn (fun y => normalSphereGreenFlux (dilatedMetric g₁ lam) E e r F y u) v
        (interior (coordinateCylinder normal)) := by
  let D := {x : (X dim) | lam • x ∈ Ω}
  have hD : IsOpen D := hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous)
  have hgA : SmoothMetric D (dilatedMetric g₁ lam) :=
    smoothMetric_dilated (smoothMetric_restrict hg₁ (subset_univ Ω)) lam
  obtain ⟨V,_,_,_,hExact,hInv,hRep⟩ := exists_cylinder_green_cutoffs_reproduce hn hΩ hg₁ hg₂ hγ hG₁
    hlam hChart hLower hE.continuous hNorm hY' hrc hr he hec hO hF hSphere hKnown
  dsimp only
  intro u v hu hv heq y hy
  obtain ⟨hCutoff,hValues⟩ := hRep hu hv heq
  obtain ⟨η,φ,hφ⟩ := hCutoff y hy
  exact (hφ.pairing_eq_normalSphereGreenFlux hD hgA hE (hNorm.mono_ambient hChart)
    hExact hInv hO hF hy (he y hy) hu).symm.trans (hValues y hy η φ hφ)

end CalderonN
