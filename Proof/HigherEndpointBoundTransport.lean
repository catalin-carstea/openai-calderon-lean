import Mathlib.Analysis.Normed.Operator.Basic
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres

/-- Transport a genuine higher witness and its norm through an equality
    of operators on the SAME lower grade. Both inclusion maps stay explicit. -/
lemma exists_higher_endpoint_bound_congr
    {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
    [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]
    (I0 : Mid →L[ℝ] Lo) (I1 : Hi →L[ℝ] Mid) (L L' : Mid →L[ℝ] Lo) (B : ℝ)
    (hL : L=L') (h : ∃ H : Hi →L[ℝ] Mid,I0.comp H=L.comp I1 ∧ ‖H‖ ≤ B) :
    ∃ H : Hi →L[ℝ] Mid,I0.comp H=L'.comp I1 ∧ ‖H‖ ≤ B := by
  subst L'
  exact h
end ShrinkingSpheres
