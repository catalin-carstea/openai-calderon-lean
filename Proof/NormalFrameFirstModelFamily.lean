import Proof.NormalFrameFirstCovectorRegularity
import Proof.GeneralLocalCommonSupportFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

def normalFrameFirstModelCoefficient (g g₁ : MetricField) (q : NormalFrameParameter × X) : Mat :=
  normalFrameFirstCovector g g₁ q.1 q.2 • (1:Mat)

lemma Background.contDiffOn_normalFrameFirstModelCoefficient {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (V : Set NormalFrameParameter) (hCenter : ∀ p ∈ V,p.1 ∈ Ω) :
    ContDiffOn ℝ ∞ (normalFrameFirstModelCoefficient d.γ d.g₁) (V ×ˢ (Set.univ:Set X)) := by
  have hEll := h.contDiffOn_normalFrameFirstCovector hΩ hK V hCenter
  have hBase : ContDiffOn ℝ ∞ (fun q : NormalFrameParameter × X => normalFrameFirstCovector d.γ d.g₁ q.1)
      (V ×ˢ (Set.univ:Set X)) := hEll.comp contDiffOn_fst (fun _ hq => hq.1)
  exact (hBase.clm_apply contDiffOn_snd).smul contDiffOn_const

/-- One compact smooth first-model family represents the genuine first
covector on an open independent center/radius/frame domain. It is chosen
locally without any bound on derivatives of the admitted frame. -/
theorem Background.exists_normalFrame_first_model_family {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (V : Set NormalFrameParameter) (hV : IsOpen V) (hCenter : ∀ p ∈ V,p.1 ∈ Ω)
    (p0 : NormalFrameParameter) (hp0 : p0 ∈ V) :
    ∃ A1 : NormalFrameParameter × X → Mat,∃ hA1 : ContDiff ℝ ∞ A1,
    ∃ S1 : Set X,∃ hS1 : IsCompact S1,∃ hz1 : ∀ p z,z ∉ S1 → A1 (p,z) = 0,
    ∃ U : Set NormalFrameParameter,IsOpen U ∧ p0 ∈ U ∧ U ⊆ V ∧
      ∀ p ∈ U,∀ z ∈ Metric.closedBall (0:X) 2,
        A1 =ᶠ[𝓝 (p,z)] normalFrameFirstModelCoefficient d.γ d.g₁ := by
  let W := V ×ˢ (Set.univ:Set X)
  have hW : IsOpen W := hV.prod isOpen_univ
  have hSmooth : ContDiffOn ℝ ∞ (normalFrameFirstModelCoefficient d.γ d.g₁) W :=
    h.contDiffOn_normalFrameFirstModelCoefficient hΩ hK V hCenter
  have hSub : {p0} ×ˢ Metric.closedBall (0:X) 2 ⊆ W := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    exact ⟨(show p=p0 from hp) ▸ hp0,mem_univ z⟩
  obtain ⟨A1,hA1,S1,hS1,hz1,U,hU,hpU,hUV,hRep⟩ := exists_local_commonSupport_matrix_family_on_open hV
    (normalFrameFirstModelCoefficient d.γ d.g₁) 2 W hW hSmooth hp0 hSub
  exact ⟨A1,hA1,S1,hS1,hz1,U,hU,hpU,hUV,hRep⟩

def normalFrameScaledFirstModelCoefficient (g g₁ : MetricField) (r0 : ℝ)
    (q : NormalFrameParameter × X) : Mat :=
  (q.1.2.1/r0) • normalFrameFirstModelCoefficient g g₁ q

/-- The scalar factor s/r0 keeps the Taylor radius fixed at the chosen r0
while the independent physical radius s varies. Along the three geometric
curves this is exactly their already checked first model. -/
theorem Background.exists_normalFrame_scaled_first_model_family {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (V : Set NormalFrameParameter) (hV : IsOpen V) (hCenter : ∀ p ∈ V,p.1 ∈ Ω)
    (p0 : NormalFrameParameter) (hp0 : p0 ∈ V) (r0 : ℝ) :
    ∃ A1 : NormalFrameParameter × X → Mat,∃ hA1 : ContDiff ℝ ∞ A1,
    ∃ S1 : Set X,∃ hS1 : IsCompact S1,∃ hz1 : ∀ p z,z ∉ S1 → A1 (p,z) = 0,
    ∃ U : Set NormalFrameParameter,IsOpen U ∧ p0 ∈ U ∧ U ⊆ V ∧
      ∀ p ∈ U,∀ z ∈ Metric.closedBall (0:X) 2,
        A1 =ᶠ[𝓝 (p,z)] normalFrameScaledFirstModelCoefficient d.γ d.g₁ r0 := by
  obtain ⟨A1,hA1,S1,hS1,hz1,U,hU,hpU,hUV,hRep⟩ :=
    h.exists_normalFrame_first_model_family hΩ hK V hV hCenter p0 hp0
  let B : NormalFrameParameter × X → Mat := fun q => (q.1.2.1/r0) • A1 q
  have hB : ContDiff ℝ ∞ B := (contDiff_fst.snd.fst.div_const r0).smul hA1
  have hzB (p : NormalFrameParameter) (z : X) (hzS : z ∉ S1) : B (p,z) = 0 := by
    dsimp only [B]
    rw [hz1 p z hzS,smul_zero]
  refine ⟨B,hB,S1,hS1,hzB,U,hU,hpU,hUV,?_⟩
  intro p hp z hzZ
  filter_upwards [hRep p hp z hzZ] with q hq
  exact congrArg (fun M : Mat => (q.1.2.1/r0) • M) hq

end ShrinkingSpheres
