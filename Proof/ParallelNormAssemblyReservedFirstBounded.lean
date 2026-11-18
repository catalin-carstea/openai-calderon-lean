import Proof.ParallelNormAssemblyReservedFirstWords
import Proof.PrincipalFirstErrorCoordinateSharpWeights
import Proof.UniformScalarPrincipalConnectionTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Genuine order-zero realization at each Sobolev grade of the bounded
geometric part of the complete effective first coefficient. -/
def effectiveFirstBoundedRemainderAtL (s : ℝ) (d : Data) (b : I) (y : X) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  (∑ a : I,principalFirstErrorCoordinateWeight d a b y • physicalFirstCorrectionAtL s d y (axis a))-
    scalarPrincipalConnectionWeight d b y • ContinuousLinearMap.id ℝ (SphereSobolev s)

lemma effective_first_bounded_inclusion (s t : ℝ) (hst : t ≤ s) (d : Data) (b : I) (y : X)
    (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hst (effectiveFirstBoundedRemainderAtL s d b y u)=
      effectiveFirstBoundedRemainderAtL t d b y (sphereSobolevInclusionL s t hst u) := by
  simp only [effectiveFirstBoundedRemainderAtL,_root_.sub_apply,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.id_apply,map_sub,map_sum,map_smul,physicalFirstCorrectionAtL_inclusion]

/-- The order-zero realization agrees with the literal half remainder
through the genuine inclusion, after the complete frame contraction. -/
lemma effective_first_bounded_half_actual (d : Data) (b : I) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (effectiveFirstBoundedRemainderAtL (1/2:ℝ) d b y)=effectiveFirstBoundedRemainderHalfL d b y := by
  rw [effectiveFirstBoundedRemainderHalfL,principalFirstCorrectionCoordinateHalfL_eq d y he b]
  apply ContinuousLinearMap.ext
  intro u
  simp only [effectiveFirstBoundedRemainderAtL,ContinuousLinearMap.comp_apply,_root_.sub_apply,_root_.sum_apply,
    _root_.smul_apply,ContinuousLinearMap.id_apply,map_sub,map_sum,map_smul,physicalFirstCorrectionHalfL,
    ContinuousLinearMap.comp_apply,physicalFirstCorrectionAtL_inclusion]

/-- The geometric first-coefficient remainder has the sharper order-zero
ε/β² norm on EVERY fixed genuine Sobolev grade. It is built only from
already available original correction and scalar connection estimates. -/
theorem uniform_effective_first_bounded_remainder {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (s : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b : I,
      ContDiffOn ℝ ∞ (effectiveFirstBoundedRemainderAtL s d b) Y ∧ ∀ y ∈ Y,
        ‖effectiveFirstBoundedRemainderAtL s d b y‖ ≤ C*ε/(beta d.γ d.radius y)^2 := by
  obtain ⟨CW,hCW,hDrift⟩ := uniform_scalar_principal_connection_two_jets hY hΩ hm K ρ c₀ M Cj hK
  let B := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let Q := 3*K*firstCorrectionGradeBound s K (M ⟨1,by omega⟩)
  let C := 3*B*Q+CW
  have hK0 := zero_le_one.trans hK
  have hB : 0 ≤ B := principalFirstErrorCoordinateTwoJetBudget_nonneg _ _ _ _ hK0 (abs_nonneg _) (abs_nonneg _)
  have hQ : 0 ≤ Q := by
    have hh := firstCorrectionGradeBound_nonneg s K (M ⟨1,by omega⟩)
    dsimp only [Q]
    positivity
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hε1 d hd b
  have hw (a : I) := hd.contDiffOn_principalFirstErrorCoordinateWeight (zero_lt_one.trans_le hK) a b
  have hF (a : I) := hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ (zero_lt_one.trans_le hK) s (axis a)
  have hW := hDrift floor hf ε hε hε1 d hd b
  refine ⟨(ContDiffOn.sum (fun a _ => (hw a).smul (hF a))).sub (hW.1.smul contDiffOn_const),?_⟩
  intro y hy
  let β := beta d.γ d.radius y
  have hWeight (a : I) : |principalFirstErrorCoordinateWeight d a b y| ≤ B*ε/β^2 :=
    (hd.principalFirstErrorCoordinateWeight_small_two_jet_bounds hY (by omega) hK hf hε hε1 hy a b 0 0).1
  have hFC (a : I) : ‖physicalFirstCorrectionAtL s d y (axis a)‖ ≤ Q :=
    hd.norm_physicalFirstCorrectionAtL_axis_le hΩ (by omega) hK hf hε hε1 s hy a
  have hSum : ‖∑ a : I,principalFirstErrorCoordinateWeight d a b y • physicalFirstCorrectionAtL s d y (axis a)‖ ≤
      (3*B*Q)*ε/β^2 := by
    have hTerm (a : I) : ‖principalFirstErrorCoordinateWeight d a b y • physicalFirstCorrectionAtL s d y (axis a)‖ ≤
        (B*ε/β^2)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hWeight a) (hFC a) (norm_nonneg _) (by positivity)
    exact ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => hTerm a))).trans_eq
      (by simp only [Fin.sum_univ_three];ring)
  have hDriftN : ‖scalarPrincipalConnectionWeight d b y • ContinuousLinearMap.id ℝ (SphereSobolev s)‖ ≤ CW*ε/β^2 := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hW.2 y hy 0 0).1 (ContinuousLinearMap.norm_id_le) (norm_nonneg _)
      (by positivity)).trans_eq (mul_one _)
  exact ((norm_sub_le _ _).trans (add_le_add hSum hDriftN)).trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres.ParallelEnergy
