import Proof.ParallelNormAssemblyReservedWordPair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma linear_commutator_two_step {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F) (L : E →L[ℝ] F) (x y : E) : A-L y=(A-L x)+L (x-y) := by
  rw [map_sub]
  abel

/-- The order-dropped actual commutator of one true adjoint generator
with the complete quadratic word matrix. -/
def cubicWordCommutatorValue {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ)) : SphereSobolev (-(1/2:ℝ)) :=
  ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,p c e •
    (W.commLow a c (P.potentialGeneratorHigh y e u)+
      P.potentialGeneratorLow y c (W.commHigh a e u))

/-- The single-word/two-word commutator identity is on the SAME genuine
core lifts. It uses both compatible halves of W, before norms. -/
lemma cubic_word_commutator_core_identity {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ))
    (V : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (v : SphereSobolev (3/2:ℝ))
    (hV : ∀ e,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V e)=P.potentialGeneratorHigh y e u)
    (hv : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v=W.adjointHigh a u) :
    (P.potentialGeneratorLow y a).adjoint (quadraticWordForwardCoreValue P y p V)-
      (∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
        p c e • P.potentialGeneratorLow y c (P.potentialGeneratorHigh y e v))=
      cubicWordCommutatorValue P W a p u := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Inc := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hA (x : SphereSobolev (3/2:ℝ)) :
      Inc (W.adjointHigh a x)=(P.potentialGeneratorLow y a).adjoint (J x) :=
    DFunLike.congr_fun (W.adjoint_compatible a) x
  have hH (e : PhysicalPotentialGeneratorIndex) (x : SphereSobolev (3/2:ℝ)) :
      Inc (P.potentialGeneratorHigh y e x)=P.potentialGeneratorLow y e (J x) :=
    DFunLike.congr_fun (P.potential_generator_balanced hy e) x
  have hFirst (e : PhysicalPotentialGeneratorIndex) :
      W.adjointHigh a (V e)-P.potentialGeneratorHigh y e v=W.commHigh a e u := by
    apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    change Inc (W.adjointHigh a (V e)-P.potentialGeneratorHigh y e v)=_
    rw [map_sub,hA,hH,hV e,hv]
    exact DFunLike.congr_fun (W.commutator_compatible a e) u
  have hTerm (c e : PhysicalPotentialGeneratorIndex) :
      (P.potentialGeneratorLow y a).adjoint (P.potentialGeneratorHigh y c (V e))-
        P.potentialGeneratorLow y c (P.potentialGeneratorHigh y e v)=
      W.commLow a c (P.potentialGeneratorHigh y e u)+
        P.potentialGeneratorLow y c (W.commHigh a e u) := by
    have hG := DFunLike.congr_fun ((W.commutator_compatible a c).trans (W.commutator_balanced a c)) (V e)
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply] at hG
    calc
      _ = ((P.potentialGeneratorLow y a).adjoint (P.potentialGeneratorHigh y c (V e))-
          P.potentialGeneratorLow y c (W.adjointHigh a (V e)))+
          P.potentialGeneratorLow y c (W.adjointHigh a (V e)-P.potentialGeneratorHigh y e v) := by
        exact linear_commutator_two_step _ _ _ _
      _ = _ := congrArg₂ (fun x z : SphereSobolev (-(1/2:ℝ)) => x+z)
        (hG.trans (congrArg (W.commLow a c) (hV e)))
        (congrArg (P.potentialGeneratorLow y c) (hFirst e))
  simp only [quadraticWordForwardCoreValue,cubicWordCommutatorValue,map_sum,map_smul,
    ←Finset.sum_sub_distrib,←smul_sub,hTerm]

/-- The actual cubic commutator gains one angular order with exactly the
weights of the selected potential generators and the SAME W. -/
theorem cubic_word_commutator_norm_bound {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (hr : 0 ≤ d.radius y) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ)) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    ‖cubicWordCommutatorValue P W a p u‖ ≤
      (2*G*CK*potentialGeneratorWeight (d.radius y) a)*
        quadraticWordCoefficientMass p (potentialGeneratorWeight (d.radius y))*‖u‖ := by
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let w := potentialGeneratorWeight (d.radius y)
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hw := potentialGeneratorWeight_nonneg hr
  have hL (c : PhysicalPotentialGeneratorIndex) : ‖P.potentialGeneratorLow y c‖ ≤ G*w c :=
    ((P.potential_generator_norm_bounds hy hr c).1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hw c))
  have hH (e : PhysicalPotentialGeneratorIndex) : ‖P.potentialGeneratorHigh y e‖ ≤ G*w e :=
    ((P.potential_generator_norm_bounds hy hr e).2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hw e))
  have hTerm (c e : PhysicalPotentialGeneratorIndex) :
      ‖W.commLow a c (P.potentialGeneratorHigh y e u)+
        P.potentialGeneratorLow y c (W.commHigh a e u)‖ ≤
        (2*G*CK*w a)*(w c*w e)*‖u‖ := by
    have h1 : ‖W.commLow a c (P.potentialGeneratorHigh y e u)‖ ≤
        (CK*w a*w c)*(G*w e*‖u‖) := by
      exact ((W.commLow a c).le_opNorm _).trans
        (mul_le_mul (W.commLow_bound a c) (((P.potentialGeneratorHigh y e).le_opNorm u).trans
          (mul_le_mul_of_nonneg_right (hH e) (norm_nonneg u))) (norm_nonneg _) (mul_nonneg (mul_nonneg hCK (hw a)) (hw c)))
    have h2 : ‖P.potentialGeneratorLow y c (W.commHigh a e u)‖ ≤
        (G*w c)*(CK*w a*w e*‖u‖) := by
      exact ((P.potentialGeneratorLow y c).le_opNorm _).trans
        (mul_le_mul (hL c) (((W.commHigh a e).le_opNorm u).trans
          (mul_le_mul_of_nonneg_right (W.commHigh_bound a e) (norm_nonneg u))) (norm_nonneg _) (mul_nonneg hG (hw c)))
    exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)
  calc
    _ ≤ ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
        ‖p c e • (W.commLow a c (P.potentialGeneratorHigh y e u)+
          P.potentialGeneratorLow y c (W.commHigh a e u))‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => norm_sum_le _ _))
    _ ≤ ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
        |p c e| *((2*G*CK*w a)*(w c*w e)*‖u‖) := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro e _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hTerm c e) (abs_nonneg _)
    _ = (2*G*CK*w a)*quadraticWordCoefficientMass p w*‖u‖ := by
      simp only [quadraticWordCoefficientMass,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro e _
      ring

end ShrinkingSpheres.ParallelEnergy
