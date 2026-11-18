import Proof.GradedGeneratorWordCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
variable {Hi Mid Lo κ : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo] [Fintype κ]

def rightMultiplierCombinationCommutatorL
    (G : κ → Mid →L[ℝ] Lo) (K : κ → κ → Mid →L[ℝ] Lo)
    (M N : κ → Mid →L[ℝ] Mid) (CM CN : κ → κ → Mid →L[ℝ] Mid) : Mid →L[ℝ] Lo :=
  ∑ a,∑ b,rightMultiplierWordCommutatorL (G a) (G b) (K a b) (M a) (N b) (CM b a) (CN a b)

lemma graded_finite_right_multiplier_commutator
    (I : Hi →L[ℝ] Mid) (G : κ → Mid →L[ℝ] Lo) (Gh : κ → Hi →L[ℝ] Mid)
    (K : κ → κ → Mid →L[ℝ] Lo) (M N : κ → Mid →L[ℝ] Mid)
    (Mh Nh : κ → Hi →L[ℝ] Hi) (CM CN : κ → κ → Mid →L[ℝ] Mid)
    (hG : ∀ a b,(G a).comp (Gh b)-(G b).comp (Gh a)=(K a b).comp I)
    (hCM : ∀ b a,(Gh b).comp (Mh a)-(M a).comp (Gh b)=(CM b a).comp I)
    (hCN : ∀ a b,(Gh a).comp (Nh b)-(N b).comp (Gh a)=(CN a b).comp I)
    (hM : ∀ a,I.comp (Mh a)=(M a).comp I) (hN : ∀ b,I.comp (Nh b)=(N b).comp I)
    (hComm : ∀ a b,(Mh a).comp (Nh b)=(Nh b).comp (Mh a)) :
    (∑ a,(G a).comp (M a)).comp (∑ b,(Gh b).comp (Nh b))-
      (∑ b,(G b).comp (N b)).comp (∑ a,(Gh a).comp (Mh a))=
      (rightMultiplierCombinationCommutatorL G K M N CM CN).comp I := by
  have hForward : (∑ a,(G a).comp (M a)).comp (∑ b,(Gh b).comp (Nh b))=
      ∑ a,∑ b,((G a).comp (M a)).comp ((Gh b).comp (Nh b)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
    exact Finset.sum_comm
  have hReverse : (∑ b,(G b).comp (N b)).comp (∑ a,(Gh a).comp (Mh a))=
      ∑ a,∑ b,((G b).comp (N b)).comp ((Gh a).comp (Mh a)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
  rw [hForward,hReverse]
  calc
    _ = ∑ a,∑ b,(((G a).comp (M a)).comp ((Gh b).comp (Nh b))-
      ((G b).comp (N b)).comp ((Gh a).comp (Mh a))) := by
        simp only [Finset.sum_sub_distrib]
    _ = ∑ a,∑ b,(rightMultiplierWordCommutatorL (G a) (G b) (K a b) (M a) (N b) (CM b a) (CN a b)).comp I := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact graded_right_multiplier_word_commutator I (G a) (G b) (K a b) (Gh a) (Gh b)
        (M a) (N b) (CM b a) (CN a b) (Mh a) (Nh b)
        (hG a b) (hCM b a) (hCN a b) (hM a) (hN b) (hComm a b)
    _ = _ := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [rightMultiplierCombinationCommutatorL,ContinuousLinearMap.comp_apply,_root_.sum_apply]

lemma norm_rightMultiplierCombinationCommutatorL_le
    (G : κ → Mid →L[ℝ] Lo) (K : κ → κ → Mid →L[ℝ] Lo)
    (M N : κ → Mid →L[ℝ] Mid) (CM CN : κ → κ → Mid →L[ℝ] Mid) :
    ‖rightMultiplierCombinationCommutatorL G K M N CM CN‖ ≤
      ∑ a,∑ b,(‖K a b‖*‖M a‖*‖N b‖+‖G a‖*‖CM b a‖*‖N b‖+‖G b‖*‖CN a b‖*‖M a‖) := by
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b _ =>
      norm_rightMultiplierWordCommutatorL_le (G a) (G b) (K a b) (M a) (N b) (CM b a) (CN a b)))))
/-- Product weights expose the small generator/multiplier combinations;
this is the quantitative caller used for the first-error self commutator. -/
lemma norm_rightMultiplierCombinationCommutatorL_of_weights
    (G : κ → Mid →L[ℝ] Lo) (K : κ → κ → Mid →L[ℝ] Lo)
    (M N : κ → Mid →L[ℝ] Mid) (CM CN : κ → κ → Mid →L[ℝ] Mid)
    (C : ℝ) (w m n : κ → ℝ) (hC : 0 ≤ C) (hw : ∀ a,0 ≤ w a)
    (hm : ∀ a,0 ≤ m a) (hn : ∀ b,0 ≤ n b)
    (hG : ∀ a,‖G a‖ ≤ C*w a) (hK : ∀ a b,‖K a b‖ ≤ C*(w a*w b))
    (hM : ∀ a,‖M a‖ ≤ C*m a) (hN : ∀ b,‖N b‖ ≤ C*n b)
    (hCM : ∀ b a,‖CM b a‖ ≤ C*(w b*m a))
    (hCN : ∀ a b,‖CN a b‖ ≤ C*(w a*n b)) :
    ‖rightMultiplierCombinationCommutatorL G K M N CM CN‖ ≤
      3*C^3*(∑ a,w a*m a)*(∑ b,w b*n b) := by
  have bound3 (A B D x y z : ℝ) (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
      (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : A ≤ C*x) (hB : B ≤ C*y) (hD : D ≤ C*z) :
      A*B*D ≤ C^3*(x*y*z) := by
    have hAB := mul_le_mul hA hB hB0 (mul_nonneg hC hx)
    exact (mul_le_mul hAB hD hD0 (mul_nonneg (mul_nonneg hC hx) (mul_nonneg hC hy))).trans_eq (by ring)
  have hTerm (a b : κ) :
      ‖K a b‖*‖M a‖*‖N b‖+‖G a‖*‖CM b a‖*‖N b‖+‖G b‖*‖CN a b‖*‖M a‖ ≤
      3*C^3*(w a*m a)*(w b*n b) := by
    have hOne := bound3 ‖K a b‖ ‖M a‖ ‖N b‖ (w a*w b) (m a) (n b)
      (norm_nonneg _) (norm_nonneg _) (mul_nonneg (hw a) (hw b)) (hm a) (hK a b) (hM a) (hN b)
    have hTwo := bound3 ‖G a‖ ‖CM b a‖ ‖N b‖ (w a) (w b*m a) (n b)
      (norm_nonneg _) (norm_nonneg _) (hw a) (mul_nonneg (hw b) (hm a)) (hG a) (hCM b a) (hN b)
    have hThree := bound3 ‖G b‖ ‖CN a b‖ ‖M a‖ (w b) (w a*n b) (m a)
      (norm_nonneg _) (norm_nonneg _) (hw b) (mul_nonneg (hw a) (hn b)) (hG b) (hCN a b) (hM a)
    exact (add_le_add (add_le_add hOne hTwo) hThree).trans_eq (by ring)
  calc
    _ ≤ ∑ a,∑ b,(‖K a b‖*‖M a‖*‖N b‖+‖G a‖*‖CM b a‖*‖N b‖+‖G b‖*‖CN a b‖*‖M a‖) :=
      norm_rightMultiplierCombinationCommutatorL_le G K M N CM CN
    _ ≤ ∑ a,∑ b,3*C^3*(w a*m a)*(w b*n b) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hTerm a b))
    _ = _ := by
      simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
      exact Finset.sum_comm
end ShrinkingSpheres
