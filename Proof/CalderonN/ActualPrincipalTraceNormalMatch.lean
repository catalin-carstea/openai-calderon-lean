module

public import Proof.CalderonN.ActualCoordinatePrincipalTrace

import Proof.CalderonN.NormalizeMovingTraceCoefficients
import Mathlib.Tactic

/-! Match the normalized coefficient formulas to the operators that
act on the physical supported traces. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem actual_principalTrace_normalCoefficients_match
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y) (hg₂ : SmoothMetric Y d.g₂)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))
    (V : ActualTraceVelocityFactors hn Y) (hV : ∀ x (hx : x ∈ Y),V.Matches (F x hx)) :
    let P := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let g := supportedReferenceTraceCoeff hY hg hK hr
    let R := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let K₀ := supportedCoordinateModelPotential hY hg hK he hA hEll S hlog
    let K₁ := supportedCoordinateModelPotentialDerivative hY hg hK he hA hEll S hlog
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let G := actualSupportedAffine hY F hF
    (∀ i,(P.firstNormal hY i).forward.action hY = movingTraceFirstBaseCoeff a (a-g) 0 R K₀ E G i) ∧
      (P.zero hY).forward.action hY = movingTraceZeroBaseCoeff a (a-g) 0 R K₀ E G K₁ := by
  dsimp only
  let P := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
  let a := supportedPrincipalTraceCoeff hY hr hQ
  let g := supportedReferenceTraceCoeff hY hg hK hr
  let R := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
  let K₀ := supportedCoordinateModelPotential hY hg hK he hA hEll S hlog
  let K₁ := supportedCoordinateModelPotentialDerivative hY hg hK he hA hEll S hlog
  let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
  let G := actualSupportedAffine hY F hF
  have hFiber (x : X dim) (hx : x ∈ Y) :
      let Bx := smoothSupportedTraceFiberL (Y:=Y) x
      (∀ i u,Bx ((P.firstNormal hY i).forward.action hY u) =
        Bx (movingTraceFirstBaseCoeff a (a-g) 0 R K₀ E G i u)) ∧
      ∀ u,Bx ((P.zero hY).forward.action hY u) = Bx (movingTraceZeroBaseCoeff a (a-g) 0 R K₀ E G K₁ u) := by
    dsimp only
    let Bx := smoothSupportedTraceFiberL (Y:=Y) x
    let r : Module.End ℝ (SmoothSphereTrace dim) := P.radius.forward.1 x
    let s : Module.End ℝ (SmoothSphereTrace dim) := (d.radius x)⁻¹ • 1
    let a₀ (i j : I dim) : Module.End ℝ (SmoothSphereTrace dim) := (P.principal i j).forward.1 x
    let q (i j : I dim) : Module.End ℝ (SmoothSphereTrace dim) := (P.smallDifference i j).forward.1 x
    let U (i : I dim) : Module.End ℝ (SmoothSphereTrace dim) := (P.model.leading hY i).forward.1 x
    let C (i : I dim) : Module.End ℝ (SmoothSphereTrace dim) := (P.model.potential hY i).forward.1 x
    let C' (i j : I dim) : Module.End ℝ (SmoothSphereTrace dim) := (P.model.potentialDerivative hY i j).forward.1 x
    let E₀ (i : I dim) : Module.End ℝ (SmoothSphereTrace dim) := (P.velocity.velocityRemainder hY i).forward.1 x
    let G₀ (i : I dim) : Module.End ℝ (SmoothSphereTrace dim) := (P.velocity.affine hY i).forward.1 x
    let W₀ (i : I dim) : Module.End ℝ (SmoothSphereTrace dim) := (P.velocity.lowerVelocity hY i).forward.1 x
    have hW (i : I dim) : (P.velocity.lowerVelocity hY i).forward.1 x = r*E₀ i+G₀ i := by
      dsimp only [W₀,r,E₀,G₀,P,actualCoordinatePrincipalTraceFactors,ActualTraceVelocityFactors.lowerVelocity,
        PairedTraceFiberFamily.add,PairedTraceFiberFamily.mul,RegularTraceFiberFamily.add,RegularTraceFiberFamily.mul]
      rw [(hV x hx).radius]
      abel
    have hRadius : r = d.radius x • (1 : Module.End ℝ (SmoothSphereTrace dim)) := rfl
    have hInv : r*s = 1 := by
      simp only [hRadius,s,smul_mul_assoc,mul_smul_comm,mul_one,smul_smul,mul_inv_cancel₀ (hr₀ x hx),inv_mul_cancel₀ (hr₀ x hx),one_smul]
    have hInv' : s*r = 1 := by
      simp only [hRadius,s,smul_mul_assoc,mul_smul_comm,mul_one,smul_smul,mul_inv_cancel₀ (hr₀ x hx),inv_mul_cancel₀ (hr₀ x hx),one_smul]
    have hScalar (c : ℝ) (E : Module.End ℝ (SmoothSphereTrace dim)) : E*(c • 1) = (c • 1)*E := by
      simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
    have hNorm := normalize_movingTrace_coefficients a₀ q r s hInv hInv' (hScalar _) (hScalar _) U C E₀ G₀ C'
    have ha (i j : I dim) (u : SmoothSupportedTraceSection Y) :
        Bx (a i j u) = a₀ i j (Bx u) := by
      simp only [a,Bx,a₀,P,actualCoordinatePrincipalTraceFactors,PairedTraceFiberFamily.scalar,
        PairedTraceFiberFamily.symmetric,RegularTraceFiberFamily.scalar,supportedPrincipalTraceCoeff,
        smoothSupportedTraceBaseMul_fiber,LinearMap.smul_apply,Module.End.one_apply]
    have hh (i j : I dim) (u : SmoothSupportedTraceSection Y) :
        Bx ((a-g) i j u) = (r*(r*q i j)) (Bx u) := by
      simp only [Pi.sub_apply,LinearMap.sub_apply,map_sub,ha,g,supportedReferenceTraceCoeff,Bx,
        smoothSupportedTraceBaseMul_fiber]
      change (d.radius x*principal d.γ d.g₂ x i j) • Bx u-(d.radius x*(d.γ x)⁻¹ i j) • Bx u =
        d.radius x • (d.radius x • (tracePrincipalSmallDifference d i j x • Bx u))
      rw [← sub_smul,smul_smul,smul_smul]
      congr 1
      unfold tracePrincipalSmallDifference
      simp only [Matrix.sub_apply]
      field_simp [hr₀ x hx] <;> ring
    have hR (i : I dim) (u : SmoothSupportedTraceSection Y) :
        Bx (R i u) = (s*U i) (Bx u) := by
      simp only [R,s,U,Bx,supportedLeadingTraceVelocity,Module.End.mul_apply,LinearMap.smul_apply,
        Module.End.one_apply,smoothSupportedTraceBaseMul_fiber]
      rw [← actualCoordinateTraceModel_leading (hn:=hn) hY hg hK he hlog hA hEll S i]
      exact congrArg ((d.radius x)⁻¹ • ·) (RegularTraceFiberFamily.action_fiber hY _ u x)
    have hK₀ (i : I dim) (u : SmoothSupportedTraceSection Y) :
        Bx (K₀ i u) = C i (Bx u) := by
      rw [show K₀ i = (P.model.potential hY i).forward.action hY from
        (actualCoordinateTraceModel_potential hY hg hK he hlog hA hEll S i).symm]
      exact RegularTraceFiberFamily.action_fiber hY _ u x
    have hK₁ (i j : I dim) (u : SmoothSupportedTraceSection Y) :
        Bx (K₁ i j u) = C' i j (Bx u) := by
      rw [show K₁ i j = (P.model.potentialDerivative hY i j).forward.action hY from
        (actualCoordinateTraceModel_potentialDerivative hY hg hK he hlog hA hEll S i j).symm]
      exact RegularTraceFiberFamily.action_fiber hY _ u x
    have hE (i : I dim) (u : SmoothSupportedTraceSection Y) :
        Bx (E i u) = (r*E₀ i) (Bx u) := by
      simp only [Bx,E,E₀,r,P,actualCoordinatePrincipalTraceFactors,Module.End.mul_apply,
        LinearMap.smul_apply,Module.End.one_apply,
        actualSupportedGaussRemainder_fiber hY hg he hr hr₀ hlog hA hEll S F hC hF hn hx,
        (hV x hx).velocityRemainder_eq hY (hr₀ x hx) i]
      rfl
    have hG (i : I dim) (u : SmoothSupportedTraceSection Y) :
        Bx (G i u) = G₀ i (Bx u) := by
      simp only [G,G₀,Bx,P,actualCoordinatePrincipalTraceFactors,actualSupportedAffine,
        smoothSupportedTraceFiberAction_fiber,actualGaussAffineFamily,dite_eq_left hx,
        (hV x hx).affine_eq hY i,Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply,
        Module.End.one_apply,map_add,map_smul]
    dsimp only [Bx] at ha hh hR hK₀ hK₁ hE hG
    refine ⟨?_,?_⟩
    · intro i u
      have h := congrArg (fun L : Module.End ℝ (SmoothSphereTrace dim) => L (Bx u)) (hNorm.1 i).symm
      simp only [CoordinatePrincipalTraceFactors.firstNormal,CoordinatePrincipalTraceFactors.firstNormalEntry,
        PairedTraceFiberFamily.add,PairedTraceFiberFamily.finiteSum,PairedTraceFiberFamily.mul,
        RegularTraceFiberFamily.action_fiber,RegularTraceFiberFamily.add,RegularTraceFiberFamily.finiteSum,
        RegularTraceFiberFamily.mul,LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,hW,
        movingTraceFirstBaseCoeff,Pi.add_apply,Pi.zero_apply,LinearMap.zero_apply,map_zero,zero_add,
        map_add,map_sum,ha,hh,hR,hK₀,hE,hG] at h ⊢
      exact h
    · intro u
      have h := congrArg (fun L : Module.End ℝ (SmoothSphereTrace dim) => L (Bx u)) hNorm.2.symm
      simp only [CoordinatePrincipalTraceFactors.zero,CoordinatePrincipalTraceFactors.zeroNormalizedEntry,
        PairedTraceFiberFamily.add,PairedTraceFiberFamily.finiteSum,PairedTraceFiberFamily.mul,
        RegularTraceFiberFamily.action_fiber,RegularTraceFiberFamily.add,RegularTraceFiberFamily.finiteSum,
        RegularTraceFiberFamily.mul,LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,hW,
        movingTraceZeroBaseCoeff,movingTracePerturbation,Pi.add_apply,Pi.zero_apply,zero_mul,
        Finset.sum_const_zero,add_zero,map_add,map_sum,ha,hh,hR,hK₀,hK₁,hE,hG] at h ⊢
      exact h
  constructor
  · intro i
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    exact (hFiber x hx).1 i u
  · ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    exact (hFiber x hx).2 u

end CalderonN
