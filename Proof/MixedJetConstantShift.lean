import Proof.ParameterSpatialJetBounds
import Proof.PositiveJetCompositionBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SpatialJetFields

variable {P E V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma contDiff_parameter_spatial_jet (f : P × E → V) (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : E) :
    ContDiff ℝ ∞ (fun q => iteratedFDeriv ℝ k (fun z => f (q,z)) x) := by
  have hEq : (fun q => iteratedFDeriv ℝ k (fun z => f (q,z)) x) =
      fun q => spatialJetField k f (q,x) := by
    funext q
    exact (spatialJetField_eq_iteratedFDeriv k f hf q x).symm
  rw [hEq]
  exact (contDiff_spatialJetField k f hf).comp (contDiff_id.prodMk contDiff_const)

/-- A fixed spatial baseline has zero positive parameter jets, at every
    spatial derivative order. The baseline need not have compact support. -/
theorem iteratedFDeriv_parameter_spatial_sub_fixed_pos
    (f : P × E → V) (hf : ContDiff ℝ ∞ f) (b : E → V) (hb : ContDiff ℝ ∞ b)
    (p : P) (x : E) (n k : ℕ) (hn : 1 ≤ n) :
    iteratedFDeriv ℝ n (fun q => iteratedFDeriv ℝ k (fun z => f (q,z)-b z) x) p =
      iteratedFDeriv ℝ n (fun q => iteratedFDeriv ℝ k (fun z => f (q,z)) x) p := by
  have hEq : (fun q => iteratedFDeriv ℝ k (fun z => f (q,z)-b z) x) =
      fun q => iteratedFDeriv ℝ k (fun z => f (q,z)) x-iteratedFDeriv ℝ k b x := by
    funext q
    exact iteratedFDeriv_sub_apply
      (((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le (by simp))
      (hb.contDiffAt.of_le (by simp))
  rw [hEq]
  exact iteratedFDeriv_sub_const_pos _ p (contDiff_parameter_spatial_jet f hf k x).contDiffAt _ n hn

lemma iteratedFDeriv_affine_taylor_family_eq_pos
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A A1 D : P → W) (A00 A0 : W) (r : ℝ) (p : P)
    (hD : ContDiffAt ℝ ∞ D p) (n : ℕ) (hn : 1 ≤ n)
    (hFamily : ∀ q,A q = A00+r • A1 q+D q) :
    iteratedFDeriv ℝ n (fun q => A q-A0-r • A1 q) p = iteratedFDeriv ℝ n D p := by
  have hFun : (fun q => A q-A0-r • A1 q) = fun q => (A00-A0)+D q := by
    funext q
    rw [hFamily]
    module
  rw [hFun]
  change iteratedFDeriv ℝ n ((fun _ : P => A00-A0)+D) p = _
  rw [iteratedFDeriv_add_apply contDiffAt_const (hD.of_le (by simp)),
    iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,zero_add]

end ShrinkingSpheres
