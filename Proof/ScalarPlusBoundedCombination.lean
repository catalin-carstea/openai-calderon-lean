import Proof.RightScalarCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
variable {κ V Mid Lo : Type*} [Fintype κ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

lemma finite_scalar_plus_bounded_combination (R : V →L[ℝ] (Mid →L[ℝ] Lo))
    (I0 : Mid →L[ℝ] Lo) (Q : κ → V) (L : κ → Mid →L[ℝ] Lo) (Z : κ → Lo →L[ℝ] Lo)
    (hL : ∀ i,L i=R (Q i)+(Z i).comp I0) (c : κ → ℝ) :
    (∑ i,c i • L i)=R (∑ i,c i • Q i)+(∑ i,c i • Z i).comp I0 := by
  calc
    _ = (∑ i,c i • R (Q i))+(∑ i,c i • (Z i).comp I0) := by
      simp only [hL,smul_add,Finset.sum_add_distrib]
    _ = _ := by
      rw [map_sum]
      simp only [map_smul]
      congr 1
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply]

lemma scalar_model_plus_weighted_bounded (R : V →L[ℝ] (Mid →L[ℝ] Lo))
    (I0 : Mid →L[ℝ] Lo) (Q0 : V) (T : Mid →L[ℝ] Lo) (hT : T=R Q0)
    (Q : κ → V) (L : κ → Mid →L[ℝ] Lo) (F Z : κ → Lo →L[ℝ] Lo)
    (hL : ∀ i,L i=R (Q i)+(Z i).comp I0) (c : κ → ℝ) (r : ℝ) :
    T+r • (∑ i,c i • ((F i).comp I0+L i))=
      R (Q0+r • (∑ i,c i • Q i))+(r • (∑ i,c i • (F i+Z i))).comp I0 := by
  have hTerm (i : κ) : (F i).comp I0+L i=R (Q i)+(F i+Z i).comp I0 := by
    rw [hL i,ContinuousLinearMap.add_comp]
    abel
  have hSum := finite_scalar_plus_bounded_combination R I0 Q
    (fun i => (F i).comp I0+L i) (fun i => F i+Z i) hTerm c
  rw [hT,hSum,smul_add,map_add,map_smul,ContinuousLinearMap.smul_comp]
  abel
end ShrinkingSpheres
