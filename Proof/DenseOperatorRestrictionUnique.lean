import Mathlib.Analysis.Calculus.FDeriv.CompCLM
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
variable {A B C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
lemma clm_eq_of_dense_restriction (J : A →L[ℝ] B) (hJ : DenseRange J) (S T : B →L[ℝ] C)
    (hEq : S.comp J=T.comp J) : S=T := by
  have hAll : (fun u => S u) = fun u => T u :=
    hJ.equalizer S.continuous T.continuous (congrArg (fun L : A →L[ℝ] C => fun u => L u) hEq)
  exact ContinuousLinearMap.ext (fun u => congrFun hAll u)
end ShrinkingSpheres
