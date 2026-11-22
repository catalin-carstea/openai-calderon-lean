module

public import Proof.CalderonN.NormalSphereCoordinates
public import Proof.CalderonN.ProductPhaseSweep

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN.MovingSphere

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option maxHeartbeats 1200000 in
/-- With a compatible upward seed,
the compact propagation theorem applies to the literal shrinking spheres.
The propagated solution uses the same normal map as the strict test. -/
theorem exists_productSolution_across_normalSphere_cylinder
    {Y : Set (X dim)} (hY : IsOpen Y) {γ : (MetricField dim)} (hγ : SmoothMetric Y γ)
    {ρ : ℝ} (hρ : 0 < ρ) {E V : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : IsOpen (normalPairDomain Y γ ρ E))
    (hV : ContDiffOn ℝ ∞ V (normalPairDomain Y γ ρ E))
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {e : (Frame dim)} (he : ∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {depth : (X dim) → ℝ} (hd : ContDiffOn ℝ ∞ depth Y)
    {R : ℝ} (hR : 0 < R) {p : ℕ} (hp : 0 < p)
    {K : Set (X dim)} (hK : IsCompact K) (hKY : K ⊆ Y)
    {lo amin amax upper : ℝ} (hlo₀ : 0 ≤ lo) (hlo : lo < amin)
    (hab : amin ≤ amax) (hhi : amax < upper)
    (hcap : ∀ a ∈ Ioo lo upper, ∀ y ∈ K, shrinkingRadius R p depth a y < ρ)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {S : Set ((X dim) × (X dim))} (hS : IsOpen S) (Fseed : (X dim) × (X dim) → ℝ) (hseed : ProductSolutionOn g₁ g₂ S Fseed)
    (hAbove : normalSpherePoint E e (shrinkingRadius R p depth) ''
      ((K ×ˢ (univ : Set ↥(standardSphere dim))) ×ˢ Ioo amax upper) ⊆ S)
    (hSide : let B := K ×ˢ (univ : Set ↥(standardSphere dim))
      normalSpherePoint E e (shrinkingRadius R p depth) ''
        ((B \ interior B) ×ˢ Icc amin amax) ⊆ S)
    (hUp : ∀ z : (NormalSphereBase dim), z.1 ∈ K → ∀ s t : ℝ,
      s ∈ Ioo lo upper → t ∈ Ioo lo upper → s ≤ t →
      normalSpherePoint E e (shrinkingRadius R p depth) (z,s) ∈ S →
      normalSpherePoint E e (shrinkingRadius R p depth) (z,t) ∈ S)
    (hStrict : ∀ a ∈ Icc amin amax, ∀ q ∈ normalPairDomain Y γ ρ E,
      q.2 ∈ interior K → normalPhase γ V (shrinkingRadius R p depth a) q = 0 → q ∉ S →
      ProductStrictHessianAt g₁ g₂ (normalPhase γ V (shrinkingRadius R p depth a)) q) :
    ∃ O : Set ((X dim) × (X dim)), IsOpen O ∧ S ∪ normalSpherePoint E e (shrinkingRadius R p depth) ''
      ((K ×ˢ (univ : Set ↥(standardSphere dim))) ×ˢ Icc amin amax) ⊆ O ∧
      ∃ G, ProductSolutionOn g₁ g₂ O G ∧ EqOn G Fseed S := by
  let r := shrinkingRadius R p depth
  let B := K ×ˢ (univ : Set ↥(standardSphere dim))
  let D := normalPairDomain Y γ ρ E
  let P := normalSpherePoint E e r
  obtain ⟨c,hSource,hTarget,hPoint⟩ :=
    exists_normalSphereCoordinates hY hγ hρ hE hN hV hExact hInv he hframe hd hR hp
  have hP : (c.symm : (NormalSphereBase dim) × ℝ → (X dim) × (X dim)) = P := funext hPoint
  have : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
  have hB : IsCompact B := hK.prod isCompact_univ
  have hT : B ×ˢ Ioo lo upper ⊆ c.target := by
    intro z hz
    rw [hTarget]
    exact ⟨hKY hz.1.1,hlo₀.trans_lt hz.2.1,hcap z.2 hz.2 _ hz.1.1⟩
  have hLevel (a : ℝ) (ha : a ∈ Icc amin amax) : a ∈ Ioo lo upper :=
    ⟨hlo.trans_le ha.1,ha.2.trans_lt hhi⟩
  have hRad (a : ℝ) (ha : 0 < a) (y : (X dim)) : 0 < r a y :=
    mul_pos hR (pow_pos (softplus_pos ha _) _)
  have hSm (a : ℝ) (ha : a ∈ Icc amin amax) :
      ContDiffOn ℝ ∞ (normalPhase γ V (r a)) D := by
    have hr : ContDiffOn ℝ ∞ (r a) Y :=
      (contDiffOn_shrinkingRadius_parameter hd R p).comp
        (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun y hy => ⟨hlo₀.trans_lt (hLevel a ha).1,hy⟩)
    exact contDiffOn_normalPhase hγ (fun q hq => (hInv q hq).1.1) hV hr
  have hIn (z : (NormalSphereBase dim)) (hz : z ∈ B) (a : ℝ) (ha : a ∈ Ioo lo upper) :
      c.symm (z,a) ∈ D := hSource (c.map_target (hT ⟨hz,ha⟩))
  have hSphere (z : (NormalSphereBase dim)) (hz : z ∈ B) :
      frameVector e z.1 z.2 ∈ sphereAt γ z.1 :=
    frameVector_mem_sphere γ e z.1 (hframe z.1 (hKY hz.1)) z.2
  have hRadRoom (z : (NormalSphereBase dim)) (hz : z ∈ B) (t : ℝ) (ht : t ∈ Ioo lo upper) :
      r t z.1 ∈ Ioo (0 : ℝ) ρ := ⟨hRad t (hlo₀.trans_lt ht.1) _,hcap t ht _ hz.1⟩
  have hZero (a : ℝ) (ha : a ∈ Icc amin amax) (z : (NormalSphereBase dim)) (hz : z ∈ interior B) :
      normalPhase γ V (r a) (c.symm (z,a)) = 0 := by
    rw [hPoint]
    exact (normalPhase_radial hExact (hKY (interior_subset hz).1) (hSphere z (interior_subset hz))
      (hRadRoom z (interior_subset hz) a (hLevel a ha)) (r a)).trans (by ring)
  have hSign (a : ℝ) (ha : a ∈ Icc amin amax) (z : (NormalSphereBase dim)) (hz : z ∈ interior B)
      (t : ℝ) (ht : t ∈ Ioo lo upper) :
      0 < normalPhase γ V (r a) (c.symm (z,t)) ↔ a < t := by
    have hm : StrictMonoOn (fun b => r b z.1) (Ioi (0 : ℝ)) := by
      intro b hb d hd hbd
      exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀
        (strictMonoOn_softplus_scale (depth z.1) hb hd hbd) (softplus_pos hb _).le hp.ne') hR
    have hab' : a ∈ Ioi (0 : ℝ) := hlo₀.trans_lt (hLevel a ha).1
    have ht' : t ∈ Ioi (0 : ℝ) := hlo₀.trans_lt ht.1
    rw [hPoint]
    exact (normalPhase_pos_iff_radial hExact (hKY (interior_subset hz).1)
      (hSphere z (interior_subset hz)) (hRadRoom z (interior_subset hz) t ht)
      (r a) (hRad a hab' _).le).trans (hm.lt_iff_lt hab' ht')
  change ∃ O : Set ((X dim) × (X dim)), IsOpen O ∧ S ∪ P '' (B ×ˢ Icc amin amax) ⊆ O ∧
    ∃ G, ProductSolutionOn g₁ g₂ O G ∧ EqOn G Fseed S
  rw [← hP]
  refine exists_productSolution_across_compact_phase_cylinder c hB hS hlo hab hhi hT
    (by simpa only [hP] using hAbove) (by simpa only [hP] using hSide) ?_
    hg₁ hg₂ Fseed hseed (fun a => normalPhase γ V (r a)) ?_ hZero hSign ?_
  · intro z hz s t hs ht hst hSeed
    simpa only [hPoint] using hUp z hz.1 s t hs ht hst (by simpa only [hPoint] using hSeed)
  · intro a ha
    refine (hSm a ha).mono ?_
    rintro q ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    exact hIn z (interior_subset hz) t ht
  · intro a ha z hz hn
    have hcenter : (c.symm (z,a)).2 ∈ interior K := by
      rw [hPoint]
      rw [show interior B = interior K ×ˢ (univ : Set ↥(standardSphere dim)) by
        simp only [B,interior_prod_eq,interior_univ]] at hz
      exact hz.1
    exact hStrict a ha _ (hIn z (interior_subset hz) a (hLevel a ha)) hcenter (hZero a ha z hz) hn

end CalderonN.MovingSphere
