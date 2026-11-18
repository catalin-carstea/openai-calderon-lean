import Proof.ClosedCoefficientDirectionalDerivative
import Proof.SmoothFiniteJetBounds
import Proof.ClosedHigherScalarMultiplier
import Proof.ClosedScalarCommutativity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

def smoothCoefficientProduct (r : ℕ) (Q P : SmoothCoefficientJets r) : SmoothCoefficientJets r :=
  compactCoefficient r (coefficientValue r Q*coefficientValue r P)
    ((contDiff_coefficientValue r Q).mul (contDiff_coefficientValue r P))
    ((hasCompactSupport_coefficientValue r Q).mul_right)

lemma coefficientValue_smoothCoefficientProduct (r : ℕ) (Q P : SmoothCoefficientJets r) :
    coefficientValue r (smoothCoefficientProduct r Q P)=coefficientValue r Q*coefficientValue r P :=
  coefficientValue_compactCoefficient _ _ _ _

lemma norm_smoothCoefficientProduct_le (r : ℕ) (Q P : SmoothCoefficientJets r) :
    ‖smoothCoefficientProduct r Q P‖ ≤ 2^r*‖Q‖*‖P‖ := by
  apply norm_compactCoefficient_le_of_jets r _ _ _ _ (by positivity)
  intro n hn x
  have hQ : SmoothFiniteJetBound (coefficientValue r Q) x r ‖Q‖ :=
    ⟨norm_nonneg _,(contDiff_coefficientValue r Q).contDiffAt,
      fun k hk => norm_iteratedFDeriv_coefficientValue_le r Q k hk x⟩
  have hP : SmoothFiniteJetBound (coefficientValue r P) x r ‖P‖ :=
    ⟨norm_nonneg _,(contDiff_coefficientValue r P).contDiffAt,
      fun k hk => norm_iteratedFDeriv_coefficientValue_le r P k hk x⟩
  exact (hQ.scalar hP).bound n hn

def smoothCoefficientProductLeftL (r : ℕ) (Q : SmoothCoefficientJets r) :
    SmoothCoefficientJets r →L[ℝ] SmoothCoefficientJets r :=
  (realLinearMapOfSubSmul (smoothCoefficientProduct r Q) (by
    intro P T c
    apply smoothCoefficientJets_ext_of_value r
    simp only [coefficientValue_smoothCoefficientProduct,coefficientValue_sub_local,coefficientValue_smul]
    ext x
    simp only [Pi.mul_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring)).mkContinuous (2^r*‖Q‖) (fun P => norm_smoothCoefficientProduct_le r Q P)

def closedCoefficientFixedProductL (r : ℕ) (Q : SmoothCoefficientJets r) :
    ClosedCoefficientJets r →L[ℝ] ClosedCoefficientJets r :=
  ((smoothCoefficientClosureInclusionL r).comp (smoothCoefficientProductLeftL r Q)).extend
    (smoothCoefficientClosureInclusionL r)

lemma closedCoefficientFixedProductL_on_smooth (r : ℕ) (Q P : SmoothCoefficientJets r) :
    closedCoefficientFixedProductL r Q (smoothCoefficientClosureInclusionL r P)=
      smoothCoefficientClosureInclusionL r (smoothCoefficientProduct r Q P) :=
  ((smoothCoefficientClosureInclusionL r).comp (smoothCoefficientProductLeftL r Q)).extend_eq
    (denseRange_smoothCoefficientClosureInclusionL r)
    (show Isometry (smoothCoefficientClosureInclusionL r) from fun _ _ => rfl).isUniformInducing P

lemma norm_closedCoefficientFixedProductL_apply_le (r : ℕ) (Q : SmoothCoefficientJets r)
    (P : ClosedCoefficientJets r) : ‖closedCoefficientFixedProductL r Q P‖ ≤ 2^r*‖Q‖*‖P‖ := by
  have hDense : ∀ P ∈ range (smoothCoefficientClosureInclusionL r),
      ‖closedCoefficientFixedProductL r Q P‖ ≤ 2^r*‖Q‖*‖P‖ := by
    rintro _ ⟨P,rfl⟩
    rw [closedCoefficientFixedProductL_on_smooth,norm_smoothCoefficientClosureInclusionL,
      norm_smoothCoefficientClosureInclusionL]
    exact norm_smoothCoefficientProduct_le r Q P
  exact (denseRange_smoothCoefficientClosureInclusionL r).induction hDense
    (isClosed_le (by fun_prop) (by fun_prop)) P

lemma closedThreeJetCoarseScalarMultiplier_fixed_product (Q : SmoothCoefficientJets 3)
    (P : ClosedCoefficientJets 3) :
    closedThreeJetCoarseScalarMultiplierL (closedCoefficientFixedProductL 3 Q P)=
      (closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q)).comp
        (closedThreeJetCoarseScalarMultiplierL P) := by
  have hDense : ∀ P ∈ range (smoothCoefficientClosureInclusionL 3),
      closedThreeJetCoarseScalarMultiplierL (closedCoefficientFixedProductL 3 Q P)=
        (closedThreeJetCoarseScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q)).comp
          (closedThreeJetCoarseScalarMultiplierL P) := by
    rintro _ ⟨P,rfl⟩
    rw [closedCoefficientFixedProductL_on_smooth,closedThreeJetCoarseScalarMultiplierL_on_smooth,
      closedThreeJetCoarseScalarMultiplierL_on_smooth,closedThreeJetCoarseScalarMultiplierL_on_smooth]
    have hV : smoothSphereValue (coefficientSmoothData
        (smoothMultiplierLowerJets (smoothCoefficientProduct 3 Q P)))=
      smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets Q))*
      smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets P)) := by
      ext w
      change coefficientValue 2 (smoothMultiplierLowerJets (smoothCoefficientProduct 3 Q P)) w.val=
        coefficientValue 2 (smoothMultiplierLowerJets Q) w.val*coefficientValue 2 (smoothMultiplierLowerJets P) w.val
      simp only [coefficientValue_smoothMultiplierLowerJets,coefficientValue_smoothCoefficientProduct,Pi.mul_apply]
    rw [hV]
    exact ContinuousLinearMap.ext (fun u => coarseSphereScalarMulL_mul_apply _ _ u)
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) P

lemma closedThreeJetHalfScalarMultiplier_fixed_product (Q : SmoothCoefficientJets 3)
    (P : ClosedCoefficientJets 3) :
    closedThreeJetHalfBoundaryScalarMultiplierL (closedCoefficientFixedProductL 3 Q P)=
      (closedThreeJetHalfBoundaryScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q)).comp
        (closedThreeJetHalfBoundaryScalarMultiplierL P) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  simp only [ContinuousLinearMap.comp_apply,closedThreeJet_half_scalar_multiplier_coarse]
  exact DFunLike.congr_fun (closedThreeJetCoarseScalarMultiplier_fixed_product Q P)
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u)

lemma closedThreeJetHigherScalarMultiplier_fixed_product (Q : SmoothCoefficientJets 3)
    (P : ClosedCoefficientJets 3) :
    closedThreeJetHigherScalarMultiplierL (closedCoefficientFixedProductL 3 Q P)=
      (closedThreeJetHigherScalarMultiplierL (smoothCoefficientClosureInclusionL 3 Q)).comp
        (closedThreeJetHigherScalarMultiplierL P) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2:ℝ) 0 (by norm_num)
  simp only [ContinuousLinearMap.comp_apply,closedThreeJet_higher_scalar_multiplier_coarse]
  exact DFunLike.congr_fun (closedThreeJetCoarseScalarMultiplier_fixed_product Q P)
    (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u)
end ShrinkingSpheres
