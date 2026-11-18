import Proof.NormalFrameGaussScalar
import Proof.StrictNormalDiskTube
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

theorem uniform_relative_radial_gauss_domain {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ V : Set NormalFrameRelativeParameter,IsOpen V ∧ ((y,frameVectorLinear d.frame y),0) ∈ V ∧
        V ⊆ normalFrameRelativePositiveDomain Ω ∧
        ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,∃ chi : ℝ,0 < chi ∧ ∀ j : I,
          ∑ i : I,z i*normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,z) i j=chi*z j := by
  obtain ⟨η,hη,hη1,hGeo⟩ := uniform_normalFrame_signed_radius_control (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let DP := normalFrameRelativePositiveDomain Ω
  let D := (DP ∩ (fun p : NormalFrameRelativeParameter => p.1.1) ⁻¹' Y) ∩
    (fun p : NormalFrameRelativeParameter => p.2) ⁻¹' Ioo (-(1/2:ℝ)) (1/2:ℝ)
  have hDP : IsOpen DP := isOpen_normalFrameRelativePositiveDomain hΩ
  have hD : IsOpen D := (hDP.inter (hY.preimage continuous_fst.fst)).inter (isOpen_Ioo.preimage continuous_snd)
  have hKpos := zero_lt_one.trans_le hK
  have he (i j : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hpDP : p0 ∈ DP := normalFramePositiveDomain_mem_of_orthonormal d.γ
    (normalFrameRelativeZeroL p0) (hd.2.1.center_mem hy) he
  have hpD : p0 ∈ D := ⟨⟨hpDP,hy⟩,by change (0:ℝ) ∈ Ioo (-(1/2:ℝ)) (1/2:ℝ);constructor <;> norm_num⟩
  let G := normalFrameRelativeGeometricInput d.γ (d.radius y)
  let W := strictNormalDiskTube Y d.γ (fun x => max ρ (d.radius x))
  have hW : IsOpen W := isOpen_strictNormalDiskTube hY (fun x hx => hd.2.1.center_mem hx) hd.1.1 _
    (fun x hx => (hd.normal_radius_continuousAt hY hx).continuousWithinAt)
  have hG : ContinuousOn G (D ×ˢ (univ:Set X)) :=
    (hd.1.1.contDiffOn_relative_geometric_input hΩ hKpos (d.radius y)).continuousOn.mono
      (fun q hq => ⟨hq.1.1.1,hq.2⟩)
  let O := (D ×ˢ (univ:Set X)) ∩ G ⁻¹' W
  have hO : IsOpen O := hG.isOpen_inter_preimage (hD.prod isOpen_univ) hW
  have hSub : ({p0}:Set NormalFrameRelativeParameter) ×ˢ Metric.closedBall (0:X) 2 ⊆ O := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    have hpEq : p=p0 := mem_singleton_iff.mp hp
    subst p
    have hzN : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hPoint := hGeo floor hf ε hε hSmall d hd y hy (frameVectorLinear d.frame y) he (d.radius y)
      (by rw [abs_of_pos (hd.2.2.2.2.1.2 y hy).1]) z hzN
    have hG0 : G (p0,z)=(y,d.radius y • frameVectorLinear d.frame y z) := by
      change normalFrameInput (normalFrameRelativeInput (d.radius y) (normalFrameRelativeNormalization d.γ p0,z))= _
      rw [normalFrameRelativeNormalization_eq_self d.γ p0 he]
      simp only [normalFrameRelativeInput,normalFrameInput,p0,add_zero,one_mul]
    refine ⟨⟨hpD,mem_univ z⟩,?_⟩
    change G (p0,z) ∈ W
    rw [hG0]
    exact ⟨hy,hPoint.1.1⟩
  obtain ⟨V,B,hV,hB,hpV,hZB,hVB⟩ := generalized_tube_lemma isCompact_singleton
    (isCompact_closedBall (0:X) 2) hO hSub
  refine ⟨V ∩ D,hV.inter hD,⟨hpV (mem_singleton p0),hpD⟩,(fun p hp => hp.2.1.1),?_⟩
  intro p hp z hz
  have hMem : (p,z) ∈ O := @hVB (p,z) ⟨hp.1,hZB hz⟩
  let L := (normalFrameRelativeNormalization d.γ p).1.2
  let r := (1+p.2)*d.radius y
  have hr : r ≠ 0 := mul_ne_zero (by have hh := hp.2.2.1;dsimp only [mem_preimage] at hh;linarith)
    (hd.2.2.2.2.1.2 y hy).1.ne'
  have hv : r • L z ∈ interior (disk d.γ p.1.1 (max ρ (d.radius p.1.1))) :=
    mem_interior_disk_of_metricPair_lt d.γ p.1.1 _ _ hMem.2.2
  have hNorm := hd.1.1.normalFrameRelativeNormalization_orthonormal hKpos p hp.2.1.1
  have hRow := hd.1.normalFrameNormalizedCoefficient_radial_row hΩ hKpos hd.2.1 hMem.2.1 L r hr z hNorm hv
  rw [normalFrameRelativeCoefficient_eq_raw_normalized]
  exact hRow
end ShrinkingSpheres
