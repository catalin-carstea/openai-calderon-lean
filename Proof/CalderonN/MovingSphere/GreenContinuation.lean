module

public import Proof.CalderonN.MovingSphere.Propagation
public import Proof.CalderonN.MovingSphere.RadiusSeed
public import Proof.CalderonN.MovingSphere.CylinderRadiusSeed

import Proof.CalderonN.MovingSphere.SeparatedEndpoints
import Proof.CalderonN.FixedTube.GreenInitialization
import Proof.CalderonN.LowerCrossGreen
import Proof.CalderonN.DilatedGreenBounds
import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.GreenCross
import Proof.CalderonN.MetricPair
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN.MovingSphere

variable {dim : ℕ} [NeZero dim] {normal : I dim}

open FixedTube

set_option maxHeartbeats 2000000 in
/-- The literal shrinking normal spheres have a common open Green-kernel
continuation for every positive lower parameter at which the tensor is
small. The lower punctured tube retains the actual Green germs. -/
theorem exists_conformalCylinder_greenContinuation_with_high_seed
    (hn : 3 ≤ dim) {Ω W : Set (X dim)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁₀ : g₁ 0 = 1) (hg₂₀ : g₂ 0 = 1)
    {G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {Z : Set (X dim)} (hZ : IsCompact Z) (hCZ : (coordinateCylinder normal) ⊆ interior Z)
    (hZB : Z ⊆ ball (0 : (X dim)) 3)
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {ρ R ε tb : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε) (htb : 0 < tb)
    {p : ℕ} (hp : 0 < p)
    (hDepth : ∀ y, conformalDepth normal 4 y ≤ 3*tb → parabolicHeight normal y < 1/4)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Z (ball (0 : (X dim)) 3)
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ a ∈ Ioc (0 : ℝ) 1, ∀ y ∈ (coordinateCylinder normal),
      shrinkingRadius R p (conformalDepth normal 4) a y ≤ ρ/2)
    {frames : ℝ → Frame dim}
    (hOrtho : ∀ lam ∈ Icc (-1 : ℝ) 1, ∀ y i j,
      metricPair (conformalReference (depthScale normal 4) g₁ lam) y
        (frames lam y i) (frames lam y j) = if i = j then 1 else 0)
    (hFrames : ∀ lam ∈ Icc (-1 : ℝ) 1, ∀ i,
      ContDiffOn ℝ ∞ (fun y => frames lam y i) (interior Z))
    (hTests : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      let γ := conformalReference (depthScale normal 4) g₁ lam
      let N := normalPairDomain (interior Z) γ ρ (E lam)
      IsOpen N ∧ N ⊆ ball (0 : (X dim)) 3 ×ˢ interior Z ∧
      ∃ V : (X dim) × (X dim) → (X dim), ContDiffOn ℝ ∞ V N ∧
        (∀ z ∈ normalVelocityDomain (interior Z) γ ρ, V (E lam z,z.1) = z.2) ∧
        (∀ q ∈ N, (q.2,V q) ∈ normalVelocityDomain (interior Z) γ ρ ∧ E lam (q.2,V q) = q.1) ∧
        ∀ a ∈ Ioc (0 : ℝ) 1,
          let r := shrinkingRadius R p (conformalDepth normal 4) a
          ∀ q ∈ N, normalPhase γ V r q = 0 → smallJet γ (dilatedMetric g₂ lam) q.2 ≤ ε*r q.2 →
            ProductStrictHessianAt (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (normalPhase γ V r) q) :
    ∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      let γ := conformalReference (depthScale normal 4) g₁ lam
      let N := normalPairDomain (interior Z) γ ρ (E lam)
      let e (y : (X dim)) := frames lam y
      let r := shrinkingRadius R p (conformalDepth normal 4)
      ∃ (O₀ : Set ((X dim) × (X dim))) (F : (X dim) × (X dim) → ℝ),
      IsOpen O₀ ∧ fixedSeparationSet 4 (d/2) ⊆ O₀ ∧
      ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O₀ F ∧
      (∀ q ∈ fixedSeparationSet 4 (d/2), |F q| ≤ C) ∧
      ∀ δ ∈ Ioc (0 : ℝ) 1, Small (interior (coordinateCylinder normal)) γ (dilatedMetric g₂ lam) (r δ) ε →
        ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ), IsOpen O ∧
          lowerNormalSeed normal N ∪ normalSpherePoint (E lam) e r ''
            (((coordinateCylinder normal) ×ˢ (univ : Set ↥(standardSphere dim))) ×ˢ Icc δ 1) ⊆ O ∧
          ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O G ∧
          EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N) ∧
          (∀ y ∈ (coordinateCylinder normal), tb < conformalDepth normal 4 y → ∀ w : ↥(standardSphere dim),
            let q := normalSpherePoint (E lam) e r ((y,w),δ)
            q ∈ fixedSeparationSet 3 d ∧ G =ᶠ[𝓝 q] F) ∧
          (∀ y ∈ (coordinateCylinder normal), y normal < -(1/4 : ℝ) → ∀ w : ↥(standardSphere dim),
            let q := normalSpherePoint (E lam) e r ((y,w),δ)
            ‖q.1‖ ≤ 3 ∧ ‖q.2‖ ≤ 3 ∧ G =ᶠ[𝓝 q] dilatedGreen G₁ lam) := by
  letI : Nontrivial (Fin dim) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let γ := conformalReference (depthScale normal 4) g₁
  let r := shrinkingRadius R p (conformalDepth normal 4)
  let A := Icc (-1 : ℝ) 1
  have hγ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j) := by
    apply contDiffOn_univ.mp
    simpa only [mem_univ,ofPred_true] using
      contDiffOn_conformalReference_family_entry hg₁ (contDiff_depthScale (normal := normal) 4) i j
  have hPos (lam : ℝ) (y : (X dim)) : (γ lam y).PosDef :=
    (hg₁.2 _ (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)
  obtain ⟨upper,r₀,hupper,hr₀,hCap,hTop,hSide,hHigh⟩ := exists_cylinder_radius_seed_with_high hR hρ htb p hDepth hRadius
  obtain ⟨d,hd,hSep⟩ := exists_uniform_normal_endpoint_separation
    (A := A) isCompact_Icc hZ hγ (fun lam _ y _ => hPos lam y) hE hr₀ hNormal
  obtain ⟨C,hC,hFixed⟩ := exists_bounded_fixedSeparation_initialGreen hn hΩ hW hside hg₁ hg₂ hg₁₀ hg₂₀
    hG₁ hG₂ hmetric hgreen (B := 4) (η := 1/4) (by norm_num) (half_pos hd) (by norm_num)
  refine ⟨d,C,hd,hC,?_⟩
  have hLower := eventually_lowerCross_greenSolution hn hΩ hW hside
    (smoothMetric_restrict hg₁ (subset_univ Ω)) (smoothMetric_restrict hg₂ (subset_univ Ω))
    hG₁ hG₂ hmetric hgreen 4 (by norm_num : (0 : ℝ) < 1/4)
  have hA : A ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hSideW := eventually_dilated_mem_side_of_negative_coordinate hside 3 (by norm_num : (0 : ℝ) < 1/4)
  filter_upwards [hA,hTests,hFixed,hLower,hSideW] with lam hlam hTest hFixed hLower hSideW hpos
  obtain ⟨hN,hNsub,V,hV,hExact,hInverse,hStrict⟩ := hTest hpos
  obtain ⟨O₀,F,hO₀,hFixedSub,hF,hFknown,hFbound⟩ := hFixed hpos
  let gA := dilatedMetric g₁ lam
  let gB := dilatedMetric g₂ lam
  let F₀ := dilatedInitialGreen W G₁ G₂ lam
  let N := normalPairDomain (interior Z) (γ lam) ρ (E lam)
  let e (y : (X dim)) := frames lam y
  let S := separatedNormalSeed N (γ lam) V r₀ ∪ lowerNormalSeed normal N
  have eOrtho (y : (X dim)) (i j : (I dim)) : metricPair (γ lam) y (e y i) (e y j) = if i = j then 1 else 0 :=
    hOrtho lam hlam y i j
  have hγAll : SmoothMetric univ (γ lam) :=
    ⟨fun i j => ((hγ i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,
      fun y _ => hPos lam y⟩
  have hE' : ContDiff ℝ ∞ (E lam) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hN4 : N ⊆ ball (0 : (X dim)) 4 ×ˢ ball (0 : (X dim)) 4 :=
    hNsub.trans (Set.prod_mono (ball_subset_ball (by norm_num))
      (interior_subset.trans (hZB.trans (ball_subset_ball (by norm_num)))))
  have hSep' (q : (X dim) × (X dim)) (hq : q ∈ N)
      (hrad : r₀^2 ≤ metricPair (γ lam) q.2 (V q) (V q)) : d ≤ ‖q.1-q.2‖ := by
    obtain ⟨hVel,hEnd⟩ := hInverse q hq
    have hdisk : V q ∈ disk (γ lam) q.2 ρ := hVel.2.le
    simpa only [hEnd] using hSep lam hlam q.2 (interior_subset hVel.1) (V q) hrad hdisk
  have hFixedMono : fixedSeparationSet (dim := dim) 4 d ⊆ fixedSeparationSet 4 (d/2) :=
    fun q hq => ⟨hq.1,hq.2.1,(half_lt_self hd).le.trans hq.2.2⟩
  obtain ⟨H,hH,hHfar,hHknown⟩ := exists_normalRadius_seed hN hN4 hγAll hV.continuousOn hSep'
    (hFixedMono.trans hFixedSub) hF (hLower hpos)
    (hFknown.mono (inter_subset_inter_left _ hFixedMono))
  have hS : IsOpen S := (isOpen_separatedNormalSeed hN hγAll hV.continuousOn _).union (isOpen_lowerNormalSeed hN)
  have hFrame (i : (I dim)) : ContDiffOn ℝ ∞ (fun y => e y i) (interior Z) :=
    hFrames lam hlam i
  have hIn (z : (NormalSphereBase dim)) (hz : z.1 ∈ (coordinateCylinder normal)) (a : ℝ) (ha : a ∈ Ioo 0 upper) :
      (z.1,r a z.1 • frameVector e z.1 (z.2 : (X dim))) ∈ normalVelocityDomain (interior Z) (γ lam) ρ ∧
      normalSpherePoint (E lam) e r (z,a) ∈ N := by
    have hr : 0 < r a z.1 := mul_pos hR (pow_pos (softplus_pos ha.1 _) _)
    have hw := frameVector_mem_sphere (γ lam) e z.1 (eOrtho z.1) z.2
    have hv : (z.1,r a z.1 • frameVector e z.1 (z.2 : (X dim))) ∈
        normalVelocityDomain (interior Z) (γ lam) ρ := by
      refine ⟨hCZ hz,?_⟩
      change metricPair (γ lam) z.1 (r a z.1 • frameVector e z.1 (z.2 : (X dim)))
        (r a z.1 • frameVector e z.1 (z.2 : (X dim))) < ρ^2
      rw [metricPair_smul_same,show metricPair (γ lam) z.1 (frameVector e z.1 (z.2 : (X dim)))
        (frameVector e z.1 (z.2 : (X dim))) = 1 from hw,mul_one]
      exact pow_lt_pow_left₀ (hCap a ha _ hz) hr.le (by decide)
    exact ⟨hv,⟨_,hv,rfl⟩⟩
  have hRad (z : (NormalSphereBase dim)) (hz : z.1 ∈ (coordinateCylinder normal)) (a : ℝ) (ha : a ∈ Ioo 0 upper) :
      metricPair (γ lam) z.1 (V (normalSpherePoint (E lam) e r (z,a)))
        (V (normalSpherePoint (E lam) e r (z,a))) = (r a z.1)^2 := by
    have hv := (hIn z hz a ha).1
    have hv' := hExact _ hv
    change V (normalSpherePoint (E lam) e r (z,a)) = _ at hv'
    rw [hv',metricPair_smul_same,show metricPair (γ lam) z.1 (frameVector e z.1 (z.2 : (X dim)))
      (frameVector e z.1 (z.2 : (X dim))) = 1 from frameVector_mem_sphere (γ lam) e z.1 (eOrtho z.1) z.2,mul_one]
  have hFar (z : (NormalSphereBase dim)) (hz : z.1 ∈ (coordinateCylinder normal)) (a : ℝ) (ha : a ∈ Ioo 0 upper)
      (hr : r₀ < r a z.1) : normalSpherePoint (E lam) e r (z,a) ∈ separatedNormalSeed N (γ lam) V r₀ := by
    refine ⟨(hIn z hz a ha).2,?_⟩
    change r₀^2 < metricPair (γ lam) z.1 (V (normalSpherePoint (E lam) e r (z,a)))
      (V (normalSpherePoint (E lam) e r (z,a)))
    rw [hRad z hz a ha]
    exact pow_lt_pow_left₀ hr hr₀.le (by decide)
  have hLo (z : (NormalSphereBase dim)) (hz : z.1 ∈ (coordinateCylinder normal)) (a : ℝ) (ha : a ∈ Ioo 0 upper)
      (hy : z.1 normal < -(1/4 : ℝ)) : normalSpherePoint (E lam) e r (z,a) ∈ lowerNormalSeed normal N := by
    refine ⟨⟨(hIn z hz a ha).2,hy⟩,?_⟩
    intro he
    have hzero : (z.1,(0 : (X dim))) ∈ normalVelocityDomain (interior Z) (γ lam) ρ := by
      exact ⟨hCZ hz,by simp [metricPair,pow_pos hρ]⟩
    have hLoc := (hNormal lam hlam).2 z.1 (interior_subset (hCZ hz))
    have h0disk : (0 : (X dim)) ∈ disk (γ lam) z.1 ρ := by simp [disk,metricPair,sq_nonneg]
    have hOrigin : E lam (z.1,0) = z.1 := by
      simpa only [zero_smul] using (hLoc.2.2 (0 : (X dim)) h0disk).2.2.1
    have hVz : V (z.1,z.1) = 0 := by simpa only [hOrigin] using hExact _ hzero
    have hpnt : normalSpherePoint (E lam) e r (z,a) = (z.1,z.1) := Prod.ext he rfl
    have hVal := hRad z hz a ha
    rw [hpnt,hVz] at hVal
    have hr : 0 < r a z.1 := mul_pos hR (pow_pos (softplus_pos ha.1 _) _)
    simp [metricPair] at hVal
    exact (pow_pos hr 2).ne' hVal.symm
  have hMono (z : (X dim)) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) : r s z ≤ r t z :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (softplus_pos hs _).le
      ((strictMonoOn_softplus_scale (conformalDepth normal 4 z)).monotoneOn hs ht hst) p) hR.le
  dsimp only
  refine ⟨O₀,F,hO₀,hFixedSub,hF,hFbound,?_⟩
  intro δ hδ hsmall
  have hAbove : normalSpherePoint (E lam) e r ''
      (((coordinateCylinder normal) ×ˢ (univ : Set ↥(standardSphere dim))) ×ˢ Ioo 1 upper) ⊆ S := by
    rintro q ⟨⟨z,a⟩,⟨hz,ha⟩,rfl⟩
    exact Or.inl (hFar z hz.1 a ⟨zero_lt_one.trans ha.1,ha.2⟩ (hTop a ha _ hz.1))
  have hSideSeed : let B := (coordinateCylinder normal) ×ˢ (univ : Set ↥(standardSphere dim))
      normalSpherePoint (E lam) e r '' ((B \ interior B) ×ˢ Icc δ 1) ⊆ S := by
    dsimp only
    rintro q ⟨⟨z,a⟩,⟨hz,ha⟩,rfl⟩
    have hz' : z.1 ∈ (coordinateCylinder normal) \ interior (coordinateCylinder normal) := by
      refine ⟨hz.1.1,?_⟩
      intro hi
      exact hz.2 (by simpa only [interior_prod_eq,interior_univ] using
        (show z ∈ interior (coordinateCylinder normal) ×ˢ (univ : Set ↥(standardSphere dim)) from ⟨hi,mem_univ _⟩))
    have ha' : a ∈ Ioo (0 : ℝ) upper := ⟨hδ.1.trans_le ha.1,ha.2.trans_lt hupper⟩
    by_cases hlo : z.1 normal < -(1/4 : ℝ)
    · exact Or.inr (hLo z hz'.1 a ha' hlo)
    · exact Or.inl (hFar z hz'.1 a ha' (hSide a ha'.1 _ hz' (le_of_not_gt hlo)))
  have hUp : ∀ z : (NormalSphereBase dim), z.1 ∈ (coordinateCylinder normal) → ∀ s t : ℝ,
      s ∈ Ioo 0 upper → t ∈ Ioo 0 upper → s ≤ t →
      normalSpherePoint (E lam) e r (z,s) ∈ S → normalSpherePoint (E lam) e r (z,t) ∈ S := by
    intro z hz s t hs ht hst hS'
    rcases hS' with hfar | hlo
    · have h := hfar.2
      change r₀^2 < metricPair (γ lam) z.1 (V (normalSpherePoint (E lam) e r (z,s)))
        (V (normalSpherePoint (E lam) e r (z,s))) at h
      rw [hRad z hz s hs] at h
      have hrpos : 0 < r s z.1 := mul_pos hR (pow_pos (softplus_pos hs.1 _) _)
      exact Or.inl (hFar z hz t ht (((sq_lt_sq₀ hr₀.le hrpos.le).mp h).trans_le (hMono _ s t hs.1 ht.1 hst)))
    · exact Or.inr (hLo z hz t ht hlo.1.2)
  have hStrictSeed : ∀ a ∈ Icc δ 1, ∀ q ∈ N, q.2 ∈ interior (coordinateCylinder normal) →
      normalPhase (γ lam) V (r a) q = 0 → q ∉ S →
      ProductStrictHessianAt gA gB (normalPhase (γ lam) V (r a)) q := by
    intro a ha q hq hY hPhase _
    have ha' : a ∈ Ioc (0 : ℝ) 1 := ⟨hδ.1.trans_le ha.1,ha.2⟩
    exact hStrict a ha' q hq hPhase ((hsmall q.2 hY).1.trans
      (mul_le_mul_of_nonneg_left (hMono q.2 δ a hδ.1 ha'.1 ha.1) hε))
  obtain ⟨O,hO,hOS,G,hG,hAgree⟩ := exists_productSolution_across_normalSphere_cylinder
    (isOpen_interior : IsOpen (interior Z)) (smoothMetric_restrict hγAll (subset_univ _)) hρ hE'
    hN hV hExact hInverse hFrame (fun y _ => eOrtho y) (contDiff_conformalDepth (normal := normal) 4).contDiffOn hR hp
    (isCompact_coordinateCylinder (normal := normal)) hCZ (lo := 0) (amin := δ) (amax := 1) (upper := upper)
    le_rfl hδ.1 hδ.2 hupper hCap (smoothMetric_dilatedMetric hg₁ lam) (smoothMetric_dilatedMetric hg₂ lam)
    hS H hH hAbove hSideSeed hUp hStrictSeed
  have hKnown : EqOn G F₀ (lowerNormalSeed normal N) :=
    fun q hq => (hAgree (Or.inr hq : q ∈ S)).trans (hHknown hq)
  refine ⟨O,G,hO,(Set.union_subset_union_left _ subset_union_right).trans hOS,hG,hKnown,?_,?_⟩
  · intro y hy hDepth w
    let q := normalSpherePoint (E lam) e r ((y,w),δ)
    have hδ' : δ ∈ Ioo 0 upper := ⟨hδ.1,hδ.2.trans_lt hupper⟩
    have hq : q ∈ separatedNormalSeed N (γ lam) V r₀ :=
      hFar (y,w) hy δ hδ' (hHigh δ hδ.1 y hDepth.le)
    have hqN := hNsub hq.1
    have hv : r₀^2 ≤ metricPair (γ lam) q.2 (V q) (V q) := hq.2.le
    refine ⟨⟨(mem_ball_zero_iff.mp hqN.1).le,
      (mem_ball_zero_iff.mp (hZB (interior_subset hqN.2))).le,hSep' q hq.1 hv⟩,?_⟩
    have hopen := isOpen_separatedNormalSeed hN hγAll hV.continuousOn r₀
    filter_upwards [hopen.mem_nhds hq] with z hz
    exact (hAgree (Or.inl hz : z ∈ S)).trans (hHfar hz)
  · intro y hy hyLo w
    let q := normalSpherePoint (E lam) e r ((y,w),δ)
    have hδ' : δ ∈ Ioo 0 upper := ⟨hδ.1,hδ.2.trans_lt hupper⟩
    have hq : q ∈ lowerNormalSeed normal N := hLo (y,w) hy δ hδ' hyLo
    have hN' := hNsub hq.1.1
    have hX : ‖q.1‖ ≤ 3 := (mem_ball_zero_iff.mp hN'.1).le
    have hY : ‖q.2‖ ≤ 3 := (mem_ball_zero_iff.mp (hZB (interior_subset hN'.2))).le
    have hWq : lam • q.2 ∈ W := hSideW hpos q.2 (mem_closedBall_zero_iff.mpr hY) hyLo.le
    refine ⟨hX,hY,?_⟩
    have hOpen := (isOpen_lowerNormalSeed (normal := normal) hN).inter
      (hW.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous.comp continuous_snd))
    filter_upwards [hOpen.mem_nhds (show q ∈ lowerNormalSeed normal N ∩ {q | lam • q.2 ∈ W} from
      ⟨hq,hWq⟩)] with z hz
    exact (hKnown hz.1).trans (dilatedInitialGreen_eq_left G₁ G₂ hz.2)

/-- The literal shrinking normal spheres have a common open Green-kernel
continuation for every positive lower parameter at which the tensor is
small. The lower punctured tube retains the actual Green germs. -/
theorem exists_conformalCylinder_greenContinuation
    (hn : 3 ≤ dim) {Ω W : Set (X dim)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁₀ : g₁ 0 = 1) (hg₂₀ : g₂ 0 = 1)
    {G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {Z : Set (X dim)} (hZ : IsCompact Z) (hCZ : (coordinateCylinder normal) ⊆ interior Z)
    (hZB : Z ⊆ ball (0 : (X dim)) 3)
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {ρ R ε tb : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε) (htb : 0 < tb)
    {p : ℕ} (hp : 0 < p)
    (hDepth : ∀ y, conformalDepth normal 4 y ≤ 3*tb → parabolicHeight normal y < 1/4)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Z (ball (0 : (X dim)) 3)
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ a ∈ Ioc (0 : ℝ) 1, ∀ y ∈ (coordinateCylinder normal),
      shrinkingRadius R p (conformalDepth normal 4) a y ≤ ρ/2)
    {frames : ℝ → Frame dim}
    (hOrtho : ∀ lam ∈ Icc (-1 : ℝ) 1, ∀ y i j,
      metricPair (conformalReference (depthScale normal 4) g₁ lam) y
        (frames lam y i) (frames lam y j) = if i = j then 1 else 0)
    (hFrames : ∀ lam ∈ Icc (-1 : ℝ) 1, ∀ i,
      ContDiffOn ℝ ∞ (fun y => frames lam y i) (interior Z))
    (hTests : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      let γ := conformalReference (depthScale normal 4) g₁ lam
      let N := normalPairDomain (interior Z) γ ρ (E lam)
      IsOpen N ∧ N ⊆ ball (0 : (X dim)) 3 ×ˢ interior Z ∧
      ∃ V : (X dim) × (X dim) → (X dim), ContDiffOn ℝ ∞ V N ∧
        (∀ z ∈ normalVelocityDomain (interior Z) γ ρ, V (E lam z,z.1) = z.2) ∧
        (∀ q ∈ N, (q.2,V q) ∈ normalVelocityDomain (interior Z) γ ρ ∧ E lam (q.2,V q) = q.1) ∧
        ∀ a ∈ Ioc (0 : ℝ) 1,
          let r := shrinkingRadius R p (conformalDepth normal 4) a
          ∀ q ∈ N, normalPhase γ V r q = 0 → smallJet γ (dilatedMetric g₂ lam) q.2 ≤ ε*r q.2 →
            ProductStrictHessianAt (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (normalPhase γ V r) q) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      let γ := conformalReference (depthScale normal 4) g₁ lam
      let N := normalPairDomain (interior Z) γ ρ (E lam)
      let e (y : (X dim)) := frames lam y
      let r := shrinkingRadius R p (conformalDepth normal 4)
      ∀ δ ∈ Ioc (0 : ℝ) 1, Small (interior (coordinateCylinder normal)) γ (dilatedMetric g₂ lam) (r δ) ε →
        ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ), IsOpen O ∧
          lowerNormalSeed normal N ∪ normalSpherePoint (E lam) e r ''
            (((coordinateCylinder normal) ×ˢ (univ : Set ↥(standardSphere dim))) ×ˢ Icc δ 1) ⊆ O ∧
          ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O G ∧
          EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N) := by
  obtain ⟨_,_,_,_,h⟩ := exists_conformalCylinder_greenContinuation_with_high_seed
    hn hΩ hW hside hg₁ hg₂ hg₁₀ hg₂₀ hG₁ hG₂ hmetric hgreen hZ hCZ hZB hE
    hρ hR hε htb hp hDepth hNormal hRadius hOrtho hFrames hTests
  filter_upwards [h] with lam h hpδ
  obtain ⟨_,_,_,_,_,_,h⟩ := h hpδ
  dsimp only
  intro δ hδ hSmall
  obtain ⟨O,G,hO,hS,hG,hEq,_⟩ := h δ hδ hSmall
  exact ⟨O,G,hO,hS,hG,hEq⟩

end CalderonN.MovingSphere
