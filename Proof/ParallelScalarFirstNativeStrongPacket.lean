import Proof.ParallelScalarFirstUniformNativeHalfSecond
import Proof.UniformActualStrongHalfCovariantDerivative
import Proof.UniformActualFirstErrorSmoothCovariant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- One smooth strong half first-jet family for the actual native error,
with compatible genuine coarse second graphs and uniform second half norms. -/
theorem uniform_actual_first_error_strong_half_two_jets
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C1 C2 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C1 ∧ 0 ≤ C2 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ a : X,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∃ S : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∀ i : I,ContDiffOn ℝ ∞ (S i) Y ∧ ContDiffOn ℝ ∞ (L i) Y ∧ ∀ y ∈ Y,
        CoarseCovariantRotationGraph d y (axis i) (actualFirstAdjointErrorFamily d a A G) (S i y) ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S i y)=
          (L i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖L i y‖ ≤ C1*‖a‖*d.radius y*beta d.γ d.radius y ∧
        ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
          CoarseCovariantRotationGraph d y (axis j) (S i) T ∧
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
            N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
          ‖N‖ ≤ C2*‖a‖*d.radius y*(beta d.γ d.radius y)^2 := by
  classical
  obtain ⟨ηS,CS,hηS,hηS1,hCS,hSmooth⟩ :=
    uniform_actual_first_error_smooth_covariant hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηH,C0,C1,hηH,hηH1,hC0,hC1,hHalf⟩ :=
    uniform_actual_first_error_covariant_half_graph hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨η2,C2,hη2,hη21,hC2,hSecond⟩ :=
    uniform_actual_first_error_second_strong_half_graph hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηS (min ηH η2),C1,C2,lt_min hηS (lt_min hηH hη2),
    (min_le_left _ _).trans hηS1,hC1,hC2,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG
  obtain ⟨S0,hS0S,hS0⟩ := hSmooth floor hf ε hε (hSmall.trans (min_le_left _ _))
    d hd R A hAS hR hA a G hGS hG
  let S := fun (i : I) (x : X) => S0 x (axis i)
  have hSG (i : I) (x : X) (hx : x ∈ Y) :
      CoarseCovariantRotationGraph d x (axis i) (actualFirstAdjointErrorFamily d a A G) (S i x) :=
    (hS0 x hx).1 (axis i)
  have hExists (i : I) (x : X) :
      ∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),x ∈ Y →
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S i x)=
          L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖L‖ ≤ C1*‖a‖*d.radius x*beta d.γ d.radius x := by
    by_cases hx : x ∈ Y
    · obtain ⟨L0,L1,T,hBase,hT,hCompat,hL0,hL1,hLε⟩ :=
        hHalf floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
          d hd R A hAS hR hA a G hGS hG x hx (axis i) (by simp only [norm_axis];rfl)
      have hSame : S i x=T := coarseCovariantRotationGraph_unique (hSG i x hx) hT
      exact ⟨L1,fun _ => ⟨by rw [hSame];exact hCompat,hL1⟩⟩
    · exact ⟨0,fun hxy => (hx hxy).elim⟩
  choose L hL using hExists
  refine ⟨S,L,?_⟩
  intro i
  have hSL (x : X) (hx : x ∈ Y) := (hL i x hx).1
  have hSecondI := hSecond floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
    d hd R A hR hA a G hG (axis i) (by simp only [norm_axis];rfl) (S i) (L i) (hSG i) hSL
  refine ⟨hS0S.clm_apply contDiffOn_const,hSecondI.1,?_⟩
  intro y hy
  refine ⟨hSG i y hy,hSL y hy,(hL i y hy).2,?_⟩
  intro j
  exact hSecondI.2 y hy (axis j) (by simp only [norm_axis];rfl)

end ShrinkingSpheres.ParallelEnergy
