import Proof.ParallelNormAssemblyReservedQuadraticJetWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- First jet of a full scalar-weighted quadratic word matrix, retaining
all three product-rule contributions. -/
def quadraticWordFirstJetL {ι : Type*} [Fintype ι]
    (p dp : ι → ι → ℝ)
    (L DL : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H DH : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ a,∑ b,(dp a b • (L a).comp (H b)+p a b • ((DL a).comp (H b)+(L a).comp (DH b)))

lemma weighted_quadratic_covariant_product_rule (d : Data)
    (p : X → ℝ)
    (L : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (LA H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (y a : X) (hp : ContDiffAt ℝ ∞ p y) (hL : ContDiffAt ℝ ∞ L y) (hH : ContDiffAt ℝ ∞ H y)
    (DL : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (DH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hBalanced : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (LA y)=
      (L y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hDL : halfOperatorCovariantDerivativeL d L LA y a=
      DL.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hDH : higherOperatorCovariantDerivativeL d H y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (DH.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))))
    (u : SphereSobolev (5/2:ℝ)) (v : SphereSobolev (3/2:ℝ))
    (hv : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v=
      H y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) :
    quadraticOperatorCovariantDerivativeL d (fun x => p x • (L x).comp (H x)) y a u=
      sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
        (((fderiv ℝ p y a) • (L y).comp (H y)+p y • (DL.comp (H y)+(L y).comp DH))
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) := by
  rw [quadratic_covariant_smul d p (fun x => (L x).comp (H x)) y a
    (hp.differentiableAt (by simp)) ((hL.clm_comp hH).differentiableAt (by simp))]
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply]
  rw [quadratic_covariant_product_rule d L LA H y a hL hH DL DH hBalanced hDL hDH u v hv]
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,map_add,map_smul]

/-- The entire finite quadratic matrix's covariant first derivative has
its genuine strong two-angular-order extension. All cross words remain. -/
theorem quadratic_matrix_covariant_first_jet {ι : Type*} [Fintype ι]
    (d : Data) (p : ι → ι → X → ℝ)
    (L : ι → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : ι → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (y a : X) (hp : ∀ b c,ContDiffAt ℝ ∞ (p b c) y)
    (hL : ∀ b,ContDiffAt ℝ ∞ (L b) y) (hH : ∀ b,ContDiffAt ℝ ∞ (H b) y)
    (DL : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (DH : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hBalanced : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H b y)=
      (L b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hDL : ∀ b,halfOperatorCovariantDerivativeL d (L b) (H b) y a=
      (DL b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hDH : ∀ b,higherOperatorCovariantDerivativeL d (H b) y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        ((DH b).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))))
    (u : SphereSobolev (5/2:ℝ)) (V : ι → SphereSobolev (3/2:ℝ))
    (hV : ∀ b,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V b)=
      H b y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) :
    quadraticOperatorCovariantDerivativeL d (fun x => ∑ b,∑ c,p b c x • (L b x).comp (H c x)) y a u=
      sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
        (quadraticWordFirstJetL (fun b c => p b c y) (fun b c => fderiv ℝ (p b c) y a)
          (fun b => L b y) DL (fun b => H b y) DH
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) := by
  have hEach (b c : ι) : ContDiffAt ℝ ∞ (fun x => p b c x • (L b x).comp (H c x)) y :=
    (hp b c).smul ((hL b).clm_comp (hH c))
  rw [quadratic_covariant_sum d _ y a (fun b =>
    (ContDiffAt.sum (fun c _ => hEach b c)).differentiableAt (by simp))]
  simp only [quadraticWordFirstJetL,_root_.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [quadratic_covariant_sum d _ y a (fun c => (hEach b c).differentiableAt (by simp))]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  exact weighted_quadratic_covariant_product_rule d (p b c) (L b) (H b) (H c) y a
    (hp b c) (hL b) (hH c) (DL b) (DH c) (hBalanced b) (hDL b) (hDH c) u (V c) (hV c)

end ShrinkingSpheres.ParallelEnergy
