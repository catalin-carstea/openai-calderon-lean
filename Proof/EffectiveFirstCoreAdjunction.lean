import Proof.EffectiveFirstCoreOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The complete SAME effective first operator and its constructed actual
formal adjoint are physically adjoint on the common supported domain.
Each of the two scalar products is integrable separately. -/
theorem PhysicalPrincipalData.firstCoreOperators_green
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (Ψ : X → SphereSobolev 2)
    (hU : ContDiff ℝ ∞ U) (hΨ : ContDiff ℝ ∞ Ψ)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0Ψ : ∀ x ∉ S,Ψ x=0)
    (hw : ∀ b,ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    IntegrableOn (fun y => metricDensity d.γ y*
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),P.firstCovariantCoreSection Ψ y⟫_ℝ) Y ∧
    IntegrableOn (fun y => metricDensity d.γ y*
      ⟪sphereSobolevInclusionL 2 0 (by norm_num) (Ψ y),P.firstFormalAdjointCore WF WQ U y⟫_ℝ) Y ∧
    (∫ y in Y,metricDensity d.γ y*
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),P.firstCovariantCoreSection Ψ y⟫_ℝ)=
      (∫ y in Y,metricDensity d.γ y*
        ⟪sphereSobolevInclusionL 2 0 (by norm_num) (Ψ y),P.firstFormalAdjointCore WF WQ U y⟫_ℝ) := by
  let U0 := fun y => sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y)
  let Ψ0 := fun y => sphereSobolevInclusionL 2 0 (by norm_num) (Ψ y)
  let F := fun b y => metricDensity d.γ y*⟪U0 y,P.firstCovariantCoreRow Ψ b y⟫_ℝ
  let A := fun b y => metricDensity d.γ y*⟪Ψ0 y,P.firstFormalAdjointCoreRow WF WQ U b y⟫_ℝ
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hUlp : MemLp U 2 (volume.restrict Y) :=
    hU.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS h0U)
  have hΨlp : MemLp Ψ 2 (volume.restrict Y) :=
    hΨ.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS h0Ψ)
  have hU0lp : MemLp U0 2 (volume.restrict Y) :=
    (sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num)).comp_memLp' hUlp
  have hΨ0lp : MemLp Ψ0 2 (volume.restrict Y) :=
    (sphereSobolevInclusionL 2 0 (by norm_num)).comp_memLp' hΨlp
  have hF (b : I) : IntegrableOn (F b) Y :=
    integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY U0 _ hU0lp
      (P.firstCovariantCoreRow_memLp hY hΩ hSub hd hK Ψ hΨ S hS hSY h0Ψ b (hw b) 2)
      (fun y _ hs => by simp only [U0,h0U y hs,map_zero]) _ (hg.contDiffOn_density hK).continuousOn
  have hA (b : I) : IntegrableOn (A b) Y :=
    integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY Ψ0 _ hΨ0lp
      (P.firstFormalAdjointCoreRow_memLp hY hΩ hSub hd hK WF WQ hCG hCK U hU S hS hSY h0U b (hw b) 2)
      (fun y _ hs => by simp only [Ψ0,h0Ψ y hs,map_zero]) _ (hg.contDiffOn_density hK).continuousOn
  have hFsum : (fun y => metricDensity d.γ y*
      ⟪U0 y,P.firstCovariantCoreSection Ψ y⟫_ℝ)=fun y => ∑ b : I,F b y := by
    funext y
    simp only [PhysicalPrincipalData.firstCovariantCoreSection,F,inner_sum,Finset.mul_sum]
  have hAsum : (fun y => metricDensity d.γ y*
      ⟪Ψ0 y,P.firstFormalAdjointCore WF WQ U y⟫_ℝ)=fun y => ∑ b : I,A b y := by
    funext y
    simp only [PhysicalPrincipalData.firstFormalAdjointCore,A,inner_sum,Finset.mul_sum]
  change IntegrableOn _ Y ∧ IntegrableOn _ Y ∧ _
  rw [hFsum,hAsum]
  refine ⟨integrable_finsetSum Finset.univ (fun b _ => hF b),
    integrable_finsetSum Finset.univ (fun b _ => hA b),?_⟩
  rw [integral_finsetSum Finset.univ (fun b _ => hF b),
    integral_finsetSum Finset.univ (fun b _ => hA b)]
  exact Finset.sum_congr rfl (fun b _ => P.firstFormalAdjointCoreRow_green hY hΩ hSub hd hK WF WQ
    U Ψ hU hΨ S hS hSY h0U h0Ψ b (hw b))

end ShrinkingSpheres
