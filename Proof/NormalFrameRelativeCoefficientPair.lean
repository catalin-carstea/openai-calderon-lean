import Proof.NormalFrameRelativeFirstRegularity
import Proof.UniformRadialCoefficientDomains
import Proof.GeneralLocalCommonSupportFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- One common-support pair represents the genuine normalized coefficient and
    its scalar first model in center/frame/relative-radius parameters. The
    residual identity is a joint germ, so every finite mixed jet is retained. -/
theorem uniform_normalFrameRelative_coefficient_pair_family {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η : ℝ,0 < η ∧ η ≤ 1 ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ r0 : ℝ,|r0| ≤ d.radius y →
      ∃ a a1 : NormalFrameRelativeParameter × X → Mat,
        ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ a1 ∧
        ∃ S : Set X,IsCompact S ∧ (∀ p z,z ∉ S → a (p,z) = 0) ∧ (∀ p z,z ∉ S → a1 (p,z) = 0) ∧
        ∃ V : Set NormalFrameRelativeParameter,IsOpen V ∧ ((y,L),0) ∈ V ∧
          V ⊆ normalFrameRelativePositiveDomain Ω ∧ (∀ p ∈ V,p.1.1 ∈ Y) ∧
          ContDiffOn ℝ ∞ (normalFrameRelativeFirstCovector d.γ d.g₁) V ∧
          (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) Z,
            a =ᶠ[𝓝 (p,z)] normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r0) ∧
          (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) Z,
            a1 =ᶠ[𝓝 (p,z)] normalFrameRelativeFirstModel d.γ d.g₁) ∧
          (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) Z,
            a1 (p,z) = normalFrameRelativeFirstCovector d.γ d.g₁ p z • (1:Mat)) ∧
          ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) Z,
            (fun q => a q-(1:Mat)-r0 • a1 q) =ᶠ[𝓝 (p,z)]
              (fun q => normalFrameRadialRemainder d.γ d.g₁ d.expMap ((q.1.1,q.2),(1+q.1.2)*r0)) := by
  obtain ⟨η,hη,hη1,hDomains⟩ := uniform_orthonormal_coefficient_smooth_domains (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ Z hZ
  refine ⟨η,hη,hη1,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he r0 hr0
  let p0 : NormalFrameRelativeParameter := ((y,L),0)
  let B0 : NormalFrameRelativeParameter × X → Mat × Mat := fun q =>
    (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r0 q,normalFrameRelativeFirstModel d.γ d.g₁ q)
  let DP := normalFrameRelativePositiveDomain Ω
  let D : Set (NormalFrameRelativeParameter × X) := DP ×ˢ (Set.univ:Set X)
  have hDP : IsOpen DP := isOpen_normalFrameRelativePositiveDomain hΩ
  have hD : IsOpen D := hDP.prod isOpen_univ
  have hpDP : p0 ∈ DP := normalFramePositiveDomain_mem_of_orthonormal d.γ
    (y,(0,L)) (hd.2.1.center_mem hy) he
  have hFirst : ContDiffOn ℝ ∞ (normalFrameRelativeFirstModel d.γ d.g₁) D :=
    hd.1.contDiffOn_normalFrameRelativeFirstModel hΩ (zero_lt_one.trans_le hK)
  have hLocal (z : X) (hz : z ∈ Metric.closedBall (0:X) Z) :
      ∃ U : Set (NormalFrameRelativeParameter × X),IsOpen U ∧ (p0,z) ∈ U ∧ ContDiffOn ℝ ∞ B0 U := by
    have hzN : ‖z‖ ≤ Z := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    obtain ⟨W,hW,hHere,hCoeff⟩ := hDomains floor hf ε hε hSmall d hd y hy L he z hzN r0 hr0
    let U := normalFrameRelativeInput r0 ⁻¹' W ∩ D
    have hU : IsOpen U := (hW.preimage (contDiff_normalFrameRelativeInput r0).continuous).inter hD
    have hInput : normalFrameRelativeInput r0 (p0,z) ∈ W := by
      simpa only [normalFrameRelativeInput,p0,add_zero,one_mul] using hHere
    have hP : ContDiffOn ℝ ∞ (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r0)
        (normalFrameRelativeInput r0 ⁻¹' W) :=
      hCoeff.comp (contDiff_normalFrameRelativeInput r0).contDiffOn (fun q hq => hq)
    exact ⟨U,hU,⟨hInput,⟨hpDP,mem_univ z⟩⟩,
      (hP.mono inter_subset_left).prodMk (hFirst.mono inter_subset_right)⟩
  choose W hW hHere hBW using hLocal
  let U := ⋃ z,⋃ hz : z ∈ Metric.closedBall (0:X) Z,W z hz
  have hU : IsOpen U := isOpen_iUnion (fun z => isOpen_iUnion (fun hz => hW z hz))
  have hSmooth : ContDiffOn ℝ ∞ B0 U := by
    intro q hq
    simp only [U,mem_iUnion] at hq
    obtain ⟨z,hz,hq⟩ := hq
    exact ((hBW z hz).contDiffAt ((hW z hz).mem_nhds hq)).contDiffWithinAt
  let YP := DP ∩ (fun p : NormalFrameRelativeParameter => p.1.1) ⁻¹' Y
  have hYP : IsOpen YP := hDP.inter (hY.preimage continuous_fst.fst)
  have hpYP : p0 ∈ YP := ⟨hpDP,hy⟩
  have hSub : {p0} ×ˢ Metric.closedBall (0:X) Z ⊆ U := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    have hpp : p=p0 := hp
    subst p
    exact mem_iUnion_of_mem z (mem_iUnion_of_mem hz (hHere z hz))
  obtain ⟨B,hB,S,hS,hSupport,V,hV,hpV,hVY,hRep⟩ :=
    exists_local_commonSupport_family_on_open hYP B0 Z U hU hSmooth hpYP hSub
  let a : NormalFrameRelativeParameter × X → Mat := fun q => (B q).1
  let a1 : NormalFrameRelativeParameter × X → Mat := fun q => (B q).2
  have ha : ContDiff ℝ ∞ a := hB.fst
  have ha1 : ContDiff ℝ ∞ a1 := hB.snd
  have hzA : ∀ p z,z ∉ S → a (p,z) = 0 := by
    intro p z hz
    change (B (p,z)).1 = 0
    rw [hSupport p z hz]
    rfl
  have hzA1 : ∀ p z,z ∉ S → a1 (p,z) = 0 := by
    intro p z hz
    change (B (p,z)).2 = 0
    rw [hSupport p z hz]
    rfl
  have hRepA (p : NormalFrameRelativeParameter) (hp : p ∈ V) (z : X) (hz : z ∈ Metric.closedBall (0:X) Z) :
      a =ᶠ[𝓝 (p,z)] normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r0 := by
    filter_upwards [hRep p hp z hz] with q hq
    exact congrArg (fun M : Mat × Mat => M.1) hq
  have hRepA1 (p : NormalFrameRelativeParameter) (hp : p ∈ V) (z : X) (hz : z ∈ Metric.closedBall (0:X) Z) :
      a1 =ᶠ[𝓝 (p,z)] normalFrameRelativeFirstModel d.γ d.g₁ := by
    filter_upwards [hRep p hp z hz] with q hq
    exact congrArg (fun M : Mat × Mat => M.2) hq
  have hEll : ContDiffOn ℝ ∞ (normalFrameRelativeFirstCovector d.γ d.g₁) V :=
    (hd.1.contDiffOn_normalFrameRelativeFirstCovector hΩ (zero_lt_one.trans_le hK)).mono (fun p hp => (hVY hp).1)
  refine ⟨a,a1,ha,ha1,S,hS,hzA,hzA1,V,hV,hpV,(fun p hp => (hVY hp).1),
    (fun p hp => (hVY hp).2),hEll,hRepA,hRepA1,?_,?_⟩
  · intro p hp z hz
    exact (hRepA1 p hp z hz).eq_of_nhds.trans (normalFrameRelativeFirstModel_scalar d.γ d.g₁ (p,z))
  · intro p hp z hz
    filter_upwards [hRepA p hp z hz,hRepA1 p hp z hz] with q hq hq1
    rw [hq,hq1]
    exact normalFrameRelativeCoefficient_affine_residual d.γ d.g₁ d.expMap r0 q

/-- At a true orthonormal frame the relative geometric coefficient is the
    original raw coefficient, so native unit-ball congruence preserves the
    original actual response witnesses. -/
lemma normalFrameRelativeCoefficient_orthonormal (g g₁ : MetricField) (E : X × X → X) (r0 : ℝ)
    (q : NormalFrameRelativeParameter × X)
    (he : ∀ i j,metricPair g q.1.1.1 (q.1.1.2 (axis i)) (q.1.1.2 (axis j)) = if i=j then 1 else 0) :
    normalFrameRelativeCoefficient g g₁ E r0 q =
      normalFrameNormalizedCoefficient g g₁ E (normalFrameRelativeInput r0 q) := by
  change orthonormalNormalFrameCoefficient g g₁ E (normalFrameRelativeInput r0 q) = _
  rw [orthonormalNormalFrameCoefficient_eq_comp,Function.comp_apply,
    normalFrameOrthonormalLift_eq_self g (normalFrameRelativeInput r0 q) he]

end ShrinkingSpheres
