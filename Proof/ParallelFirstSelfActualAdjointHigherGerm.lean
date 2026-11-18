import Proof.ParallelFirstSelfErrorEndpointPacket
import Proof.ParallelFirstSelfNativeAdjointThreeJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

/-- ANY selected actual HIGH adjoint family has the germ of the SAME
retained native three-jet family, by genuine inclusion uniqueness. -/
lemma FirstSelfActualErrorEndpointPacket.adjoint_higher_native_germ
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε C0 C1 : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {y a : X} (hy : y ∈ Y) (p : FirstSelfActualErrorEndpointPacket Y d a)
    (q : FirstSelfNativeAdjointThreeJetPacket Y Ω d y a K C0 C1)
    (AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hAH : ∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH x)=
      (p.low x).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    AH =ᶠ[𝓝 y] q.native.firstErrorTrueAdjointHigherFamily q.coefficients q.domain q.elliptic q.positive ∘
      normalFrameRelativeActualParameter d (d.radius y) := by
  let Ψ := normalFrameRelativeActualParameter d (d.radius y)
  have hr := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hΨ := (contDiffOn_normalFrameRelativeActualParameter d (d.radius y) hd.2.2.2.2.1.1
    (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub)).contDiffAt (hY.mem_nhds hy)
  have hStay : ∀ᶠ x in 𝓝 y,Ψ x ∈ q.native.centerDegreeDomain q.domain :=
    hΨ.continuousAt.eventually ((q.native.centerDegreeDomain_open q.domain).mem_nhds (by
      rw [normalFrameRelativeActualParameter_point d y hr]
      exact q.native.centerDegreeDomain_pointMem q.domain))
  have hCoarse := q.native.actual_first_adjoint_error_germ q.domain hY hΩ hSub hd.1 q.positive
    hy hr hd.2.2.2.2.1.1 q.coefficients p.radial p.adjoint p.center
    p.radial_actual p.adjoint_actual p.center_actual
  filter_upwards [hY.mem_nhds hy,hStay,hCoarse] with x hx hxD hxC
  have hNativeLow : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d a p.adjoint p.center x)=
      (q.native.firstAdjointHalfErrorFamily q.coefficients (Ψ x)).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    rw [hxC]
    exact q.native.firstAdjointHalfErrorFamily_coarse_compatible q.coefficients q.domain q.flat (Ψ x) hxD.1
  have hSame := half_endpoint_unique_of_coarse (actualFirstAdjointErrorFamily d a p.adjoint p.center x)
    (p.low x) (q.native.firstAdjointHalfErrorFamily q.coefficients (Ψ x)) (p.low_graph x hx) hNativeLow
  have hActual := hAH x hx
  rw [hSame] at hActual
  have hNative := q.graph (Ψ x) hxD
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  exact DFunLike.congr_fun (hActual.trans hNative.symm) u

lemma FirstSelfActualErrorEndpointPacket.adjoint_higher_contDiffAt
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε C0 C1 : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {y a : X} (hy : y ∈ Y) (p : FirstSelfActualErrorEndpointPacket Y d a)
    (q : FirstSelfNativeAdjointThreeJetPacket Y Ω d y a K C0 C1)
    (AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hAH : ∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH x)=
      (p.low x).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    ContDiffAt ℝ ∞ AH y := by
  have hr := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hΨ := (contDiffOn_normalFrameRelativeActualParameter d (d.radius y) hd.2.2.2.2.1.1
    (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub)).contDiffAt (hY.mem_nhds hy)
  have hp : normalFrameRelativeActualParameter d (d.radius y) y ∈ q.native.centerDegreeDomain q.domain := by
    rw [normalFrameRelativeActualParameter_point d y hr]
    exact q.native.centerDegreeDomain_pointMem q.domain
  have hNative := (q.native.contDiffOn_firstErrorTrueAdjointHigherFamily q.coefficients q.domain hY hΩ
    q.elliptic q.positive hd.2.2.2.2.1).contDiffAt ((q.native.centerDegreeDomain_open q.domain).mem_nhds hp)
  exact (hNative.comp y hΨ).congr_of_eventuallyEq
    (p.adjoint_higher_native_germ hY hΩ hSub hd hy q AH hAH)

/-- Global actual HIGH smoothness follows for every compatible selected
family, with the SAME original native three-jet witnesses available locally. -/
theorem uniform_actual_error_adjoint_higher_smooth
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ η ≤ 1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ a : X,
      ∀ p : FirstSelfActualErrorEndpointPacket Y d a,
      ∀ AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH x)=
        (p.low x).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) →
      ContDiffOn ℝ ∞ AH Y := by
  obtain ⟨η,C0,C1,hη,hη1,hC0,hC1,hPacket⟩ :=
    uniform_first_self_native_adjoint_three_jet_packet hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,hη1,?_⟩
  intro floor hf ε hε hSmall d hd a p AH hAH y hy
  obtain ⟨q⟩ := hPacket floor hf ε hε hSmall d hd y hy a
  exact (p.adjoint_higher_contDiffAt hY hΩ hSub hd hy q AH hAH).contDiffWithinAt

end ShrinkingSpheres.ParallelEnergy
