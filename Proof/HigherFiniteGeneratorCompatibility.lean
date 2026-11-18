import Proof.GradedFiniteGeneratorCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres
variable {Hi Mid Lo κ : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo] [Fintype κ]

/-- Every term in the same finite commutator word respects the genuine
    graded inclusions, so the higher realization represents the low one. -/
lemma rightMultiplierCombinationCommutatorL_compatible
    (I1 : Hi →L[ℝ] Mid) (I0 : Mid →L[ℝ] Lo)
    (G : κ → Mid →L[ℝ] Lo) (Gh : κ → Hi →L[ℝ] Mid)
    (KG : κ → κ → Mid →L[ℝ] Lo) (KGh : κ → κ → Hi →L[ℝ] Mid)
    (M N : κ → Mid →L[ℝ] Mid) (Mh Nh : κ → Hi →L[ℝ] Hi)
    (CM CN : κ → κ → Mid →L[ℝ] Mid) (CMh CNh : κ → κ → Hi →L[ℝ] Hi)
    (hG : ∀ a,I0.comp (Gh a)=(G a).comp I1)
    (hKG : ∀ a b,I0.comp (KGh a b)=(KG a b).comp I1)
    (hM : ∀ a,I1.comp (Mh a)=(M a).comp I1)
    (hN : ∀ b,I1.comp (Nh b)=(N b).comp I1)
    (hCM : ∀ b a,I1.comp (CMh b a)=(CM b a).comp I1)
    (hCN : ∀ a b,I1.comp (CNh a b)=(CN a b).comp I1) :
    I0.comp (rightMultiplierCombinationCommutatorL Gh KGh Mh Nh CMh CNh)=
      (rightMultiplierCombinationCommutatorL G KG M N CM CN).comp I1 := by
  have hGV (a : κ) (u : Hi) : I0 (Gh a u)=G a (I1 u) := DFunLike.congr_fun (hG a) u
  have hKV (a b : κ) (u : Hi) : I0 (KGh a b u)=KG a b (I1 u) := DFunLike.congr_fun (hKG a b) u
  have hMV (a : κ) (u : Hi) : I1 (Mh a u)=M a (I1 u) := DFunLike.congr_fun (hM a) u
  have hNV (b : κ) (u : Hi) : I1 (Nh b u)=N b (I1 u) := DFunLike.congr_fun (hN b) u
  have hCMV (b a : κ) (u : Hi) : I1 (CMh b a u)=CM b a (I1 u) := DFunLike.congr_fun (hCM b a) u
  have hCNV (a b : κ) (u : Hi) : I1 (CNh a b u)=CN a b (I1 u) := DFunLike.congr_fun (hCN a b) u
  apply ContinuousLinearMap.ext
  intro u
  simp only [rightMultiplierCombinationCommutatorL,rightMultiplierWordCommutatorL,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.add_apply,_root_.sub_apply,
    map_sum,ContinuousLinearMap.map_add,ContinuousLinearMap.map_sub,
    hGV,hKV,hMV,hNV,hCMV,hCNV]
end ShrinkingSpheres
