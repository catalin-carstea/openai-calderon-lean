import Proof.ParallelScalarFirstCovariantPair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def halfPair
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (U V : X → SphereSobolev (3/2:ℝ)) (y : X) : ℝ :=
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C y (J (V y)))

def halfPairCoefficientDerivative (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U V : X → SphereSobolev (3/2:ℝ)) (y a : X) : ℝ :=
  sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (U y))
    (halfOperatorCovariantDerivativeL d C Ch y a (V y))

/-- The operator-valued third-base cross term reduces to derivatives of
first-gradient pairings, genuine covariant coefficient jets, and the
actual curvature commutator supplied by its caller. -/
theorem symmetric_half_covariant_second_triple_identity (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (H : X → X → SphereSobolev (3/2:ℝ)) (y a b c : X)
    (hC : ContDiffAt ℝ ∞ C y) (hH : ∀ v,ContDiffAt ℝ ∞ (H v) y)
    (hCh : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch y)=
      (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hSym : (C y).adjoint=C y)
    (R : X → X → SphereSobolev (1/2:ℝ))
    (hR : ∀ v w,halfSectionCovariantDerivativeL d (H w) y v-
      halfSectionCovariantDerivativeL d (H v) y w=R v w) :
    let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    2*sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d (H b) y a)
        (C y (J (H c y)))=
      fderiv ℝ (halfPair C (H b) (H c)) y a+
      fderiv ℝ (halfPair C (H a) (H c)) y b-
      fderiv ℝ (halfPair C (H a) (H b)) y c-
      halfPairCoefficientDerivative d C Ch (H b) (H c) y a-
      halfPairCoefficientDerivative d C Ch (H a) (H c) y b+
      halfPairCoefficientDerivative d C Ch (H a) (H b) y c+
      sphereSobolevDualPairing (1/2:ℝ) (R a b) (C y (J (H c y)))+
      sphereSobolevDualPairing (1/2:ℝ) (R c b) (C y (J (H a y)))-
      sphereSobolevDualPairing (1/2:ℝ) (R a c) (C y (J (H b y))) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let B := fun (u v : SphereSobolev (1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) u (C y v)
  have hB (u v : SphereSobolev (1/2:ℝ)) : B u v=B v u := by
    dsimp only [B,sphereSobolevDualPairing]
    calc
      _ = ⟪(C y).adjoint u,v⟫_ℝ := ((C y).adjoint_inner_left v u).symm
      _ = _ := by rw [hSym,real_inner_comm]
  have hSub (u v w : SphereSobolev (1/2:ℝ)) : B (u-v) w=B u w-B v w :=
    inner_sub_left _ _ _
  have hAlg := symmetric_pair_second_triple_algebra B hB hSub
    (fun v => J (H v y)) (fun v w => halfSectionCovariantDerivativeL d (H w) y v) R hR a b c
  have h1 := half_covariant_pair_fderiv d C Ch (H b) (H c) y a hC (hH b) (hH c) hCh
  have h2 := half_covariant_pair_fderiv d C Ch (H a) (H c) y b hC (hH a) (hH c) hCh
  have h3 := half_covariant_pair_fderiv d C Ch (H a) (H b) y c hC (hH a) (hH b) hCh
  change fderiv ℝ (halfPair C (H b) (H c)) y a=_ at h1
  change fderiv ℝ (halfPair C (H a) (H c)) y b=_ at h2
  change fderiv ℝ (halfPair C (H a) (H b)) y c=_ at h3
  dsimp only [B,J,halfPairCoefficientDerivative] at hAlg h1 h2 h3 ⊢
  linarith only [hAlg,h1,h2,h3]

end ShrinkingSpheres.ParallelEnergy
