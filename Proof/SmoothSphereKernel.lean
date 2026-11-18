import Proof.TestRepresentative
import Proof.Archive.CompactParameterSmoothness
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.CompactParameterSmoothness

/-- Integration of a continuous complex function on the probability sphere is bounded linear. -/
def sphereIntegralCLM : C(UnitSphere,ℂ) →L[ℝ] ℂ :=
  (L1.integralCLM : Lp ℂ 1 sphereProbability →L[ℝ] ℂ).comp
    (ContinuousMap.toLp 1 sphereProbability ℝ)

lemma sphereIntegralCLM_apply (f : C(UnitSphere,ℂ)) :
    sphereIntegralCLM f = ∫ v : UnitSphere,f v ∂sphereProbability := by
  change L1.integralCLM ((ContinuousMap.toLp 1 sphereProbability ℝ) f) = _
  rw [← L1.integral_eq,L1.integral_eq_integral]
  exact integral_congr_ae (f.coeFn_toLp (p:=1) (𝕜:=ℝ) sphereProbability)

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma contDiff_frameVector_comp (e : Frame) (he : ∀ i,ContDiff ℝ ∞ (fun y => e y i))
    (Y Z : D → X) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) :
    ContDiff ℝ ∞ (fun q => frameVector e (Y q) (Z q)) :=
  ContDiff.sum (fun i _ => (((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp hZ).smul ((he i).comp hY)))

lemma contDiff_metricPair_comp (g : MetricField) (hg : ∀ i j,ContDiff ℝ ∞ (fun y => g y i j))
    (Y W Z : D → X) (hY : ContDiff ℝ ∞ Y) (hW : ContDiff ℝ ∞ W) (hZ : ContDiff ℝ ∞ Z) :
    ContDiff ℝ ∞ (fun q => metricPair g (Y q) (W q) (Z q)) :=
  ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (((hg i j).comp hY).mul ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp hW)).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp hZ)))

lemma contDiff_legendre_comp (k : ℕ) (f : D → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun q => legendre (f q) k) := by
  induction k using Nat.twoStepInduction with
  | zero => simpa only [legendre] using (contDiff_const : ContDiff ℝ ∞ (fun _ : D => (1:ℝ)))
  | one => simpa only [legendre] using hf
  | more k h0 h1 =>
    simpa only [legendre] using (((contDiff_const.mul hf).mul h1).sub (contDiff_const.mul h0)).div_const ((k:ℝ)+2)

/-- A globally smooth sphere kernel integrates to a globally smooth parameter function.
    The compact sphere is fixed, so its measure never depends on the parameter. -/
lemma contDiff_integral_compact_sphere (F : D × X → ℂ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun q => ∫ v : UnitSphere,F (q,v.val) ∂sphereProbability) := by
  let inc : C(UnitSphere,X) := ⟨Subtype.val,continuous_subtype_val⟩
  have hh := sphereIntegralCLM.contDiff.comp (contDiff_infty_compactPullback F hF inc)
  simpa only [Function.comp_def,sphereIntegralCLM_apply,compactPullback_apply,inc,ContinuousMap.coe_mk] using hh

lemma contDiff_integrated_legendre_kernel (g : MetricField) (hg : ∀ i j,ContDiff ℝ ∞ (fun y => g y i j))
    (e : Frame) (he : ∀ i,ContDiff ℝ ∞ (fun y => e y i))
    (G : X × X → ℂ) (hG : ContDiff ℝ ∞ G) (k : ℕ) :
    ContDiff ℝ ∞ (fun p : X × X => ((2*(k:ℝ)+1 : ℝ) : ℂ)*
      ∫ v : UnitSphere,(legendre (metricPair g p.1 p.2 (frameVector e p.1 v.val)) k : ℂ)*G (p.1,v.val) ∂sphereProbability) := by
  have hY : ContDiff ℝ ∞ (fun q : (X × X) × X => q.1.1) := contDiff_fst.comp contDiff_fst
  have hW : ContDiff ℝ ∞ (fun q : (X × X) × X => q.1.2) := contDiff_snd.comp contDiff_fst
  have hZ : ContDiff ℝ ∞ (fun q : (X × X) × X => q.2) := contDiff_snd
  have hV := contDiff_frameVector_comp e he _ _ hY hZ
  have hL := contDiff_legendre_comp k _ (contDiff_metricPair_comp g hg _ _ _ hY hW hV)
  have hGc : ContDiff ℝ ∞ (fun q : (X × X) × X => G (q.1.1,q.2)) := hG.comp (hY.prodMk hZ)
  exact contDiff_const.mul (contDiff_integral_compact_sphere _ ((Complex.ofRealCLM.contDiff.comp hL).mul hGc))

end ShrinkingSpheres
