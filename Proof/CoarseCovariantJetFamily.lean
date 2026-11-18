import Proof.ActualCovariantRotationGraph
import Proof.DenseOperatorRestrictionUnique
import Proof.ActualRadialTaylorEndpoints
import Proof.PolynomialDirectional
import Proof.MetricSmooth
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coarseCovariantRotationGraph_unique {d : Data} {y a : X}
    {F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    {S T : SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (hS : CoarseCovariantRotationGraph d y a F S)
    (hT : CoarseCovariantRotationGraph d y a F T) : S=T := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 2 1 (by norm_num))
    (denseRange_sphereSobolevInclusionL 2 1 (by norm_num))
  apply DFunLike.ext
  intro u
  exact sphereSobolevInclusionL_injective 0 (-1) (by norm_num) ((hS u).trans (hT u).symm)

/-- The actual coarse covariant derivative, linear in its physical direction,
    built from the ordinary derivative and the SAME angular graph generators. -/
def coarseCovariantJetFamily (d : Data)
    (F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (y : X) :
    X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  fderiv ℝ F y-∑ i : I,∑ j : I,((1/2:ℝ) • frameConnectionLinear d.γ d.frame y i j).smulRight (C i j y)

lemma coarseCovariantJetFamily_apply (d : Data)
    (F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (y a : X) :
    coarseCovariantJetFamily d F C y a=fderiv ℝ F y a-
      ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • C i j y := by
  simp only [coarseCovariantJetFamily,_root_.sub_apply,_root_.sum_apply,
    ContinuousLinearMap.smulRight_apply,_root_.smul_apply,frameConnectionLinear_apply,smul_eq_mul]

lemma coarseCovariantJetFamily_graph (d : Data)
    (F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (y a : X)
    (hC : ∀ i j : I,∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (F y (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (C i j y (sphereSobolevInclusionL 2 1 (by norm_num) u)+F y (sphereSobolevRotationL 2 i j u))) :
    CoarseCovariantRotationGraph d y a F (coarseCovariantJetFamily d F C y a) :=
  coarseCovariantRotationGraph_of_angular d y a F (fun i j => C i j y) _
    (coarseCovariantJetFamily_apply d F C y a).symm hC

lemma contDiffOn_coarseCovariantJetFamily {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hSub : Y ⊆ Ω) (d : Data) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Ω)
    (F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hF : ContDiffOn ℝ ∞ F Y) (hC : ∀ i j,ContDiffOn ℝ ∞ (C i j) Y) :
    ContDiffOn ℝ ∞ (coarseCovariantJetFamily d F C) Y := by
  have hΓ (i j : I) : ContDiffOn ℝ ∞ (fun x => frameConnectionLinear d.γ d.frame x i j) Ω := by
    apply contDiffOn_clm_apply.mpr
    intro a
    simpa only [frameConnectionLinear_apply] using
      h.contDiffOn_frameConnection hΩ hK d.frame he (fun _ => a) contDiffOn_const i j
  exact (hF.fderiv_of_isOpen hY (by simp)).sub (ContDiffOn.sum (fun i _ =>
    ContDiffOn.sum (fun j _ => ((hΓ i j).mono hSub |>.const_smul (1/2:ℝ)).smulRight (hC i j))))
end ShrinkingSpheres
