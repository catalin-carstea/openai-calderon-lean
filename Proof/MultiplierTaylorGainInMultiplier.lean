import Proof.MultiplierTaylorGainKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
open Set
namespace ShrinkingSpheres

section
variable {E H U V W Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Composition by three fixed operators, as a continuous linear map on
the remaining middle slot. -/
def operatorTripleCompositionL (T : W →L[ℝ] Z) (I : V →L[ℝ] W) (P : H →L[ℝ] U) :
    (U →L[ℝ] V) →L[ℝ] (H →L[ℝ] Z) :=
  ((ContinuousLinearMap.compL ℝ H W Z) T).comp
    (((ContinuousLinearMap.compL ℝ H V W) I).comp
      ((ContinuousLinearMap.compL ℝ H U V).flip P))

/-- The full Taylor kernel as a bounded linear map on its multiplier,
using the same three genuine bounded forcing maps. -/
def operatorMultiplierTaylorInMultiplierL
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I I0 : V →L[ℝ] W) (A1 : W →L[ℝ] V)
    (K K0 K1 : E →L[ℝ] (U →L[ℝ] V)) (P P0 P1 : H →L[ℝ] U) (r : ℝ) :
    E →L[ℝ] (H →L[ℝ] Z) :=
  (operatorTripleCompositionL T I P).comp K-(operatorTripleCompositionL T I0 P0).comp K0-
    r • ((operatorTripleCompositionL T I0 P1).comp K0+
      (operatorTripleCompositionL T I0 H0).comp K1+
      (operatorTripleCompositionL T (-(I0.comp (A1.comp I0))) H0).comp K0)

lemma operatorMultiplierTaylorInMultiplierL_apply
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I I0 : V →L[ℝ] W) (A1 : W →L[ℝ] V)
    (K K0 K1 : E →L[ℝ] (U →L[ℝ] V)) (P P0 P1 : H →L[ℝ] U) (r : ℝ) (q : E) :
    operatorMultiplierTaylorInMultiplierL T H0 I I0 A1 K K0 K1 P P0 P1 r q =
      operatorMultiplierTaylorKernel T H0 I I0 A1 (K q) (K0 q) (K1 q) P P0 P1 r := by
  change T.comp (I.comp ((K q).comp P))-T.comp (I0.comp ((K0 q).comp P0))-
    r • (T.comp (I0.comp ((K0 q).comp P1))+T.comp (I0.comp ((K1 q).comp H0))+
      T.comp ((-(I0.comp (A1.comp I0))).comp ((K0 q).comp H0))) = _
  simp only [operatorMultiplierTaylorKernel,ContinuousLinearMap.comp_add]

lemma continuousOn_operatorMultiplierTaylorInMultiplierL
    {Param : Type*} [TopologicalSpace Param] (D : Set Param)
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I0 : V →L[ℝ] W)
    (K0 : E →L[ℝ] (U →L[ℝ] V)) (P0 : H →L[ℝ] U) (r : ℝ)
    (I : Param → V →L[ℝ] W) (A1 : Param → W →L[ℝ] V)
    (K K1 : Param → E →L[ℝ] (U →L[ℝ] V)) (P P1 : Param → H →L[ℝ] U)
    (hI : ContinuousOn I D) (hA1 : ContinuousOn A1 D)
    (hK : ContinuousOn K D) (hK1 : ContinuousOn K1 D)
    (hP : ContinuousOn P D) (hP1 : ContinuousOn P1 D) :
    ContinuousOn (fun p => operatorMultiplierTaylorInMultiplierL T H0 (I p) I0 (A1 p)
      (K p) K0 (K1 p) (P p) P0 (P1 p) r) D := by
  unfold operatorMultiplierTaylorInMultiplierL operatorTripleCompositionL
  fun_prop

end
end ShrinkingSpheres
