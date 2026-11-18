import Proof.NormalFrameRelativeCenterErrorWeightJets
import Proof.FixedSpatialMultiplierCutoff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- One common-support smooth representative of each actual Jacobi weight,
    with gained jets in the completed multiplier coefficient space. The fixed
    spatial cutoff is chosen uniformly before the admitted data. -/
theorem uniform_relative_center_error_closed_multiplier_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+7 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,∀ j : I,
      ∃ A : NormalFrameRelativeParameter × X → ℝ,∃ hA : ContDiff ℝ ∞ A,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ p z,z ∉ S → A (p,z)=0,
      ∃ V : Set NormalFrameRelativeParameter,IsOpen V ∧ ((y,frameVectorLinear d.frame y),0) ∈ V ∧
        (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (p,z)]
          normalFrameRelativeCenterErrorWeight d.γ d.expMap (d.radius y) a j) ∧
        ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (commonSupportClosedCoefficientFamily 3 A hA S hS hz)
          ((y,frameVectorLinear d.frame y),0)‖ ≤ C*‖a‖*(d.radius y)^2 := by
  obtain ⟨η,CW,hη,hη1,hCW,hWeight⟩ := uniform_normalFrameRelative_center_error_weight_jets hY hΩ
    (N+3) (by omega) K ρ c₀ M Cj hK hρ 4 (by norm_num)
  obtain ⟨C0,hC0,hCutoff⟩ := exists_uniform_commonSupport_closed_multiplier_family
    (P:=NormalFrameRelativeParameter) N
  let C := C0*CW
  have hC : 1 ≤ C := by
    calc
      1 = (1:ℝ)*1 := by ring
      _ ≤ C0*CW := mul_le_mul hC0 hCW zero_le_one (zero_le_one.trans hC0)
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy a j
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let f := normalFrameRelativeCenterErrorWeight d.γ d.expMap (d.radius y) a j
  let U := smoothOpenLocus f
  have he (i k : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis k)) = if i=k then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using
      hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i k
  have hAt (z : X) (hz4 : z ∈ Metric.closedBall (0:X) 4) :=
    hWeight floor hf ε hε hSmall d hd y hy (frameVectorLinear d.frame y) he a j z
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz4)
  have hSub : {p0} ×ˢ Metric.closedBall (0:X) 4 ⊆ U := by
    intro q hq
    have hq0 : q.1=p0 := mem_singleton_iff.mp hq.1
    obtain ⟨W,hW,hMem,hF⟩ := (hAt q.2 hq.2).1
    refine ⟨W,hW,?_,hF⟩
    change (p0,q.2) ∈ W at hMem
    have hPoint : (p0,q.2)=q := Prod.ext hq0.symm rfl
    rwa [hPoint] at hMem
  obtain ⟨A,hA,S,hS,hz,V,hV,hMemV,hRep,hJets⟩ := hCutoff f U p0 (isOpen_smoothOpenLocus f)
    (contDiffOn_smoothOpenLocus f) hSub (CW*‖a‖*(d.radius y)^2) (by positivity)
    (fun n hn z hz4 => (hAt z hz4).2 n hn)
  refine ⟨A,hA,S,hS,hz,V,hV,hMemV,hRep,?_⟩
  intro n hn
  exact (hJets n hn).trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres
