import Proof.FirstConormalDegreeBound
import Proof.UniformConormalTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] nativeWeakConormalEndpoint weakFirstConormalVariationL

structure ConormalOneData (a : X → Mat)
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (F1 : SmoothCoefficientMatrix 2) (c r : ℝ) (ell : X →L[ℝ] ℝ)
    (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (CN2 : ℝ) : Prop where
  weak_compatible : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp N =
    (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  symmetric : ∀ u v,⟪N u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,N v⟫_ℝ
  remainder_bound : ‖N-c • sphereSobolevDegreeL-r • firstConormalOneL F1 c ell‖ ≤ CN2*r^2

def conormalOneFromRemainderL (F1 : SmoothCoefficientMatrix 2) (c r : ℝ) (ell : X →L[ℝ] ℝ)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  c • sphereSobolevDegreeL+r • firstConormalOneL F1 c ell+R

/-- The compatible symmetric midpoint remainder assembles the actual H1
    conormal map, with its exact weak equation and common quadratic bound. -/
theorem conormalOneData_of_remainder {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (F0 F1 : SmoothCoefficientMatrix 2) (c r CN2 : ℝ) (hc : 0 < c) (ell : X →L[ℝ] ℝ)
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) x = ell x*(1:Mat) i j)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hRN : ‖R‖ ≤ CN2*r^2)
    (hLower : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
      (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner-c • fixedLowRadialL-
        r • weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1).comp
          (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hRS : ∀ u v,⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,R v⟫_ℝ) :
    ConormalOneData a ha F1 c r ell (conormalOneFromRemainderL F1 c r ell R) CN2 := by
  let N := conormalOneFromRemainderL F1 c r ell R
  let Ihalf := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  refine ⟨?_,?_,?_⟩
  · apply ContinuousLinearMap.ext
    intro u
    have hD := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u) fixedLowRadialL_degree_compatible
    have hFirst := weakFirstConormal_degree_realization F0 F1 c hc ell hF0 hF1 ha1 hInv0 u
    have hR := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u) hLower
    have hStart : J (N u) = c • J (sphereSobolevDegreeL u)+r • J (firstConormalOneL F1 c ell u)+J (R u) := by
      change J (c • sphereSobolevDegreeL u+r • firstConormalOneL F1 c ell u+R u) = _
      exact (J.map_add _ _).trans (congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => z+J (R u))
        ((J.map_add _ _).trans (congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => x+y) (J.map_smul c _) (J.map_smul r _))))
    have hPair := congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => c • x+r • y) hD.symm hFirst.symm
    have hAll := congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => x+y) hPair hR
    exact hStart.trans (hAll.trans (by
      simp only [_root_.sub_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply]
      abel))
  · intro u v
    have hD := sphereSobolevDegreeL_symmetric u v
    have hFirst := firstConormalOneL_symmetric F0 F1 c hc ell hF0 hF1 ha1 hInv0 u v
    have hPair := congrArg₂ (fun x y : ℝ => c*x+r*y) hD hFirst
    have hAll := congrArg₂ (fun x y : ℝ => x+y) hPair (hRS u v)
    simpa only [conormalOneFromRemainderL,_root_.add_apply,_root_.smul_apply,
      inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right] using hAll
  · have hEq : N-c • sphereSobolevDegreeL-r • firstConormalOneL F1 c ell = R := by
      dsimp only [N,conormalOneFromRemainderL]
      abel
    exact (congrArg norm hEq).le.trans hRN

end ShrinkingSpheres
