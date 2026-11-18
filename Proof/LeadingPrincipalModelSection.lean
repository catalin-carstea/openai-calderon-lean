import Proof.PrincipalLeadingCollection
import Proof.ActualFrameErrorLift
import Proof.FrameTensorMatrix
import Proof.PureAngularPrincipalHalf
import Proof.Normalization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Tensor Hessian of the genuine H2 section, with its covector-index connection. -/
def highSectionCovariantHessian (d : Data) (U : X → SphereSobolev 2) (y : X) (i j : I) :
    SphereSobolev 0 :=
  oneSectionCovariantDerivative d (fun x => highSectionCovariantDerivative d U x (d.frame x j)) y (d.frame y i)-
    ∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
      sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U y (d.frame y k))

/-- The leading part of the actual expanded second trace, including the
inverse-radius derivative and logarithmic Hessian. -/
def leadingSecondTraceSection (d : Data) (U : X → SphereSobolev 2) (y : X) (i j : I) :
    SphereSobolev 0 :=
  let D := fun k => highSectionCovariantDerivative d U y (d.frame y k)
  let f := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  highSectionCovariantHessian d U y i j+
    actualLeadingFrameAdjointL d i y (D j)+actualLeadingFrameAdjointL d j y (D i)+
    actualLeadingFrameAdjointL d i y ((d.radius y)⁻¹ • flatTwoRaisingL j (U y)+
      f j • sphereSobolevShiftedDegreeL 2 (U y))+
    (-(d.radius y)⁻¹*f i) • flatOneRaisingL j (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
    hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j) •
      sphereSobolevDegreeL (sphereSobolevInclusionL 2 1 (by norm_num) (U y))

/-- The complete covariant D-plus Hessian written on successive genuine
Sobolev spaces. Its only second-base coefficient after contraction is rQ. -/
def modelPlusTensorSection (d : Data) (U : X → SphereSobolev 2) (y : X) (i j : I) :
    SphereSobolev 0 :=
  let D := fun k => highSectionCovariantDerivative d U y (d.frame y k)
  let f := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  highSectionCovariantHessian d U y i j+
    f i • sphereSobolevDegreeL (D j)+f j • sphereSobolevDegreeL (D i)+
    hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j) •
      sphereSobolevDegreeL (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
    (f i*f j) • sphereSobolevDegreeL (sphereSobolevShiftedDegreeL 2 (U y))

def highSectionModelPlus (d : Data) (U : X → SphereSobolev 2) (y : X) (j : I) :
    SphereSobolev 1 :=
  highSectionCovariantDerivative d U y (d.frame y j)+
    (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)) • sphereSobolevShiftedDegreeL 2 (U y)

/-- Exact leading physical collection with the actual principal matrix.
This is an identity before any coefficient estimate or integration. -/
theorem leadingPrincipalSection_model_collection (d : Data) (U : X → SphereSobolev 2) (y : X)
    (hr : d.radius y ≠ 0) (hQ : ∀ a b,principal d.γ d.g₂ y a b=principal d.γ d.g₂ y b a) :
    let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
    d.radius y • (∑ i : I,∑ j : I,q i j • leadingSecondTraceSection d U y i j)=
      d.radius y • (∑ i : I,∑ j : I,q i j • modelPlusTensorSection d U y i j)+
      (2:ℝ) • (∑ i : I,∑ j : I,q i j • flatOneRaisingL i (highSectionModelPlus d U y j))+
      (d.radius y)⁻¹ • (∑ i : I,∑ j : I,q i j • flatOneRaisingL i (flatTwoRaisingL j (U y))) := by
  dsimp only
  have h := symmetric_leading_trace_collection (d.radius y) (d.radius y)⁻¹ (mul_inv_cancel₀ hr)
    (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y))
    (frameTensorMatrix_symmetric d.γ d.frame y (principal d.γ d.g₂ y) hQ)
    (fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k))
    (fun i j => hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j))
    (U y) (fun k => highSectionCovariantDerivative d U y (d.frame y k)) (highSectionCovariantHessian d U y)
  have hRaise (j : I) : sphereSobolevInclusionL 1 0 (by norm_num) (flatRaisingSobolevL 2 j (U y))=
      flatRaisingSobolevL 1 j (sphereSobolevInclusionL 2 1 (by norm_num) (U y)) :=
    flatTwoRaisingL_coarse j (U y)
  simpa only [hRaise,leadingSecondTraceSection,modelPlusTensorSection,highSectionModelPlus,
    actualLeadingFrameAdjointL,leadingFrameModelFamily,flatOneRaisingL,flatTwoRaisingL,
    sphereSobolevShiftedDegreeL_one_eq_degree,flatTwoRaisingL_coarse,
    sphereSobolevShiftedDegreeL_two_coarse] using h

lemma Admissible.framePrincipalCoefficient_symmetric {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y : X} (hy : y ∈ Y) (i j : I) :
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j=
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i := by
  apply frameTensorMatrix_symmetric
  intro a b
  have hs := Matrix.isHermitian_iff_isSymm.mp (hd.principal_properties hK (hd.2.1.center_mem hy)).1.isHermitian
  exact congrArg (fun Q : Mat => Q b a) hs

private lemma matrix_sum_delta_split {V : Type} [AddCommGroup V] [Module ℝ V]
    (q : I → I → ℝ) (F : I → I → V) :
    (∑ i : I,∑ j : I,q i j • F i j)=
      (∑ i : I,F i i)+(∑ i : I,∑ j : I,(q i j-(if i=j then 1 else 0)) • F i j) := by
  have hDelta : (∑ i : I,∑ j : I,(if i=j then (1:ℝ) else 0) • F i j)=∑ i : I,F i i := by simp
  simp only [sub_smul,Finset.sum_sub_distrib,hDelta]
  abel

/-- The actual leading contraction is the raising model plus the rQ tensor
square and exactly the two h perturbations. The pure angular term is the
previously identified physical h/r operator. -/
theorem leadingPrincipalSection_model_split (d : Data) (U : X → SphereSobolev 2) (y : X)
    (hr : d.radius y ≠ 0) (hQ : ∀ a b,principal d.γ d.g₂ y a b=principal d.γ d.g₂ y b a)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
    d.radius y • (∑ i : I,∑ j : I,q i j • leadingSecondTraceSection d U y i j)=
      (2:ℝ) • (∑ i : I,flatOneRaisingL i (highSectionModelPlus d U y i))+
      d.radius y • (∑ i : I,∑ j : I,q i j • modelPlusTensorSection d U y i j)+
      (2:ℝ) • (∑ i : I,∑ j : I,(q i j-(if i=j then 1 else 0)) •
        flatOneRaisingL i (highSectionModelPlus d U y j))+
      pureAngularPrincipalPerturbationL d y (U y) := by
  dsimp only
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  have hZero : (∑ i : I,flatOneRaisingL i (flatTwoRaisingL i (U y)))=0 := by
    have h := DFunLike.congr_fun (flatRaisingSobolevL_contracted_double_zero 2) (U y)
    have hOne : flatRaisingSobolevL ((2:ℝ)-1)=flatRaisingSobolevL 1 := by rw [show (2:ℝ)-1=1 by norm_num]
    simpa only [_root_.sum_apply,ContinuousLinearMap.comp_apply,_root_.zero_apply,hOne,flatOneRaisingL,flatTwoRaisingL] using h
  have hPure : (d.radius y)⁻¹ • (∑ i : I,∑ j : I,q i j • flatOneRaisingL i (flatTwoRaisingL j (U y)))=
      pureAngularPrincipalPerturbationL d y (U y) := by
    rw [matrix_sum_delta_split q (fun i j => flatOneRaisingL i (flatTwoRaisingL j (U y))),hZero,zero_add]
    rw [pureAngularPrincipalPerturbationL_frame d y he]
    simp only [_root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [frameTensorMatrix_sub,frameTensorMatrix_inverse_metric d.γ d.frame y he]
    exact congrArg (fun t : ℝ => t • flatOneRaisingL i (flatTwoRaisingL j (U y)))
      (by dsimp only [q];ring)
  have h := leadingPrincipalSection_model_collection d U y hr hQ
  dsimp only at h
  rw [hPure,matrix_sum_delta_split q (fun i j => flatOneRaisingL i (highSectionModelPlus d U y j)),smul_add] at h
  exact h.trans (by abel)
end ShrinkingSpheres
