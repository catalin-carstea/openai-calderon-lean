import Proof.ParallelFirstPotentialDensitySplit
import Proof.ParallelNormAssemblyReservedAdjointWeakGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OperatorForms

variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

lemma firstPotential_bounded_output_supported
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (R : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (hR : ContDiffOn ℝ ∞ R Y)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) (b : I) :
    ContDiff ℝ ∞ (fun x => sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (R x (firstSelfSourceDerivative d U x (axis b)))) ∧
      ∀ x ∉ S,sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (R x (firstSelfSourceDerivative d U x (axis b)))=0 := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hD := contDiff_supported_gradedSphereSectionCovariantDerivative hY (5/2:ℝ) d hg hK he U hU S hS hSY h0 (axis b)
  have hApp := contDiff_supported_operator_apply _ R S hS hD.1 hD.2
    (fun x hx => hR.contDiffAt (hY.mem_nhds (hSY hx)))
  refine ⟨(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).contDiff.comp hApp,?_⟩
  intro x hx
  simp only [firstSelfSourceDerivative,hD.2 x hx,map_zero]

lemma firstPotential_bounded_pair_integrable
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (R : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (hR : ContDiffOn ℝ ∞ R Y)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) (b : I)
    (Q : X → SphereSobolev 0) (hQ : MemLp Q 2 (volume.restrict Y)) :
    IntegrableOn (fun x => metricDensity d.γ x*⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (R x (firstSelfSourceDerivative d U x (axis b))),Q x⟫_ℝ) Y := by
  have hOut := firstPotential_bounded_output_supported hY hSub hd hK R hR U hU S hS.isClosed hSY h0 b
  have hMem : MemLp (fun x => sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (R x (firstSelfSourceDerivative d U x (axis b)))) 2 (volume.restrict Y) :=
    hOut.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hOut.2)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  exact integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ hMem hQ
    (fun x _ hx => hOut.2 x hx) (metricDensity d.γ) (hg.contDiffOn_density hK).continuousOn

/-- Both bounded physical cross terms are individually integrable before
any finite sum or Green decomposition is distributed. -/
theorem firstPotentialBoundedDensity_integrable
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (hF : ∀ b,ContDiffOn ℝ ∞ (effectiveFirstBoundedRemainderAtL (1/2:ℝ) d b) Y)
    (hA : ∀ b,ContDiffOn ℝ ∞ (effectiveFirstBoundedAdjointHalfL d b) Y)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (firstPotentialBoundedDensity P W U) Y := by
  have hQF := P.potentialQuadraticCoreSection_memLp hY hSub hd hK W hCK U hU S hS hSY h0 2
  have hQA := P.potentialQuadraticAdjointCoreSection_memLp hY hSub hd hK W hCG hCK U hU S hS hSY h0 2
  have hEach (b : I) : IntegrableOn (fun y => metricDensity d.γ y*
      (⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (firstPotentialBoundedForwardHigherL d b y (firstSelfSourceDerivative d U y (axis b))),
         P.potentialQuadraticCoreSection W U y⟫_ℝ+
       ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (effectiveFirstBoundedAdjointHigherL d b y (firstSelfSourceDerivative d U y (axis b))),
         P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ)) Y := by
    have hRF : ContDiffOn ℝ ∞ (firstPotentialBoundedForwardHigherL d b) Y :=
      (hF b).clm_comp contDiffOn_const
    have hRA : ContDiffOn ℝ ∞ (effectiveFirstBoundedAdjointHigherL d b) Y :=
      (hA b).clm_comp contDiffOn_const
    have hIF := firstPotential_bounded_pair_integrable hY hSub hd hK _ hRF U hU S hS hSY h0 b _ hQF
    have hIA := firstPotential_bounded_pair_integrable hY hSub hd hK _ hRA U hU S hS hSY h0 b _ hQA
    apply (hIF.add hIA).congr
    exact Filter.Eventually.of_forall (fun x => (mul_add (metricDensity d.γ x) _ _).symm)
  have hSum := (integrable_finset_sum Finset.univ (fun b _ => hEach b)).const_mul 2
  change Integrable (firstPotentialBoundedDensity P W U) (volume.restrict Y)
  unfold firstPotentialBoundedDensity
  simpa only [Finset.mul_sum,mul_assoc] using hSum

end ShrinkingSpheres.ParallelEnergy
