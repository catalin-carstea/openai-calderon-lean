import Proof.FlatLoweringCoarseRotation
import Proof.SkewRotationCoefficientContraction
import Proof.ActualCovariantRotationGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Constant canonical lowering components have exactly their tensor-index
    frame connection term as covariant derivative. -/
lemma flatOneLoweringL_covariant_graph (d : Data) (y a : X)
    (hSkew : ∀ p q,frameConnectionCoefficient d.γ d.frame y a p q=
      -frameConnectionCoefficient d.γ d.frame y a q p) (i : I) :
    CoarseCovariantRotationGraph d y a (fun _ => flatOneLoweringL i)
      (∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k • flatOneLoweringL k) := by
  let Γ := frameConnectionCoefficient d.γ d.frame y a
  have hΓ (p q : I) : Γ p q= -Γ q p := hSkew p q
  let c : I → ℝ := fun k => if k=i then 1 else 0
  have hCond (p q : I) (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
      (if p=q then T else 0)=(if q=p then T else 0) := by
    by_cases hpq : p=q
    · rw [ite_eq_left hpq,ite_eq_left hpq.symm]
    · rw [ite_eq_right hpq,ite_eq_right (Ne.symm hpq)]
  have hBasis (p q : I) : flatLoweringRotationCommutatorL p q i=
      c q • flatOneLoweringL p-c p • flatOneLoweringL q := by
    simp only [c,flatLoweringRotationCommutatorL,ite_smul,one_smul,zero_smul]
    exact congrArg₂ (fun v w : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => v-w)
      (hCond i q _) (hCond i p _)
  have hCon := skew_rotation_coefficient_contraction Γ hSkew c flatOneLoweringL
  have hCoeff (p : I) : (∑ q : I,Γ p q*c q)=Γ p i := by
    simp only [c,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hCon' : (∑ p : I,∑ q : I,((1/2:ℝ)*Γ p q) • flatLoweringRotationCommutatorL p q i)=
      ∑ p : I,Γ p i • flatOneLoweringL p := by
    calc
      _ = ∑ p : I,∑ q : I,((1/2:ℝ)*Γ p q) • (c q • flatOneLoweringL p-c p • flatOneLoweringL q) := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        rw [hBasis]
      _ = ∑ p : I,(∑ q : I,Γ p q*c q) • flatOneLoweringL p := hCon
      _ = _ := by simp only [hCoeff]
  have hSwap : (∑ p : I,Γ p i • flatOneLoweringL p)= -(∑ p : I,Γ i p • flatOneLoweringL p) := by
    calc
      _ = ∑ p : I,-(Γ i p • flatOneLoweringL p) := Finset.sum_congr rfl (fun p _ => by rw [hΓ p i,neg_smul])
      _ = _ := by rw [Finset.sum_neg_distrib]
  apply coarseCovariantRotationGraph_of_angular d y a (fun _ => flatOneLoweringL i)
    (fun p q => flatLoweringRotationCommutatorL p q i) _
  · rw [fderiv_const_apply]
    change (0 : SphereSobolev 1 →L[ℝ] SphereSobolev 0)-
      (∑ p : I,∑ q : I,((1/2:ℝ)*Γ p q) • flatLoweringRotationCommutatorL p q i)=
        ∑ k : I,Γ i k • flatOneLoweringL k
    calc
      _ = -(∑ p : I,∑ q : I,((1/2:ℝ)*Γ p q) • flatLoweringRotationCommutatorL p q i) := zero_sub _
      _ = -(∑ p : I,Γ p i • flatOneLoweringL p) :=
        congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => -T) hCon'
      _ = -(-(∑ p : I,Γ i p • flatOneLoweringL p)) :=
        congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => -T) hSwap
      _ = _ := neg_neg _
  · exact fun p q u => flatOneLoweringL_coarse_rotation p q i u
end ShrinkingSpheres
