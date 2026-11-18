import Proof.CoarseDegreeCommutator
import Proof.Archive.ClosedScalarCompatibilityQuotient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped InnerProductSpace ENNReal ContDiff
namespace ShrinkingSpheres.CoarseDegreeCompatibility
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ClosedScalarCompatibility
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

abbrev CoarseDegreeData := (SphereSobolev 1 →L[ℝ] SphereSobolev 0) ×
  ((I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0) ×
    (I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0))

def radialProjectionL : CoarseDegreeData →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  ContinuousLinearMap.fst ℝ _ _

def rotationProjectionL (ij : I × I) : CoarseDegreeData →L[ℝ]
    (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  (ContinuousLinearMap.proj ij).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

def adjointProjectionL (ij : I × I) : CoarseDegreeData →L[ℝ]
    (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  (ContinuousLinearMap.proj ij).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

def blockEvaluationL (A : CoarseDegreeData →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0))
    (m n : ℕ) (z : harmonicSphereSubspace n) : CoarseDegreeData →L[ℝ] harmonicSphereSubspace m :=
  (sphereSobolevCoefficientL 0 m).comp
    ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) (sphereSobolevSingleL 1 n z)).comp A)

def rotationConstraintL (ij : I × I) (m n : ℕ)
    (z : harmonicSphereSubspace n) (w : harmonicSphereSubspace m) : CoarseDegreeData →L[ℝ] ℝ :=
  (innerSL ℝ w).comp
    (blockEvaluationL (rotationProjectionL ij) m n z-
      (harmonicSphereRotation m ij.1 ij.2).comp (blockEvaluationL radialProjectionL m n z)+
      blockEvaluationL radialProjectionL m n (harmonicSphereRotation n ij.1 ij.2 z))

lemma rotationConstraintL_apply (ij : I × I) (m n : ℕ)
    (z : harmonicSphereSubspace n) (w : harmonicSphereSubspace m) (x : CoarseDegreeData) :
    rotationConstraintL ij m n z w x =
      ⟪coarsePhysicalHarmonicBlock (x.2.1 ij) m n z-
        harmonicSphereRotation m ij.1 ij.2 (coarsePhysicalHarmonicBlock x.1 m n z)+
          coarsePhysicalHarmonicBlock x.1 m n (harmonicSphereRotation n ij.1 ij.2 z),w⟫_ℝ := by
  change ⟪w,coarsePhysicalHarmonicBlock (x.2.1 ij) m n z-
    harmonicSphereRotation m ij.1 ij.2 (coarsePhysicalHarmonicBlock x.1 m n z)+
    coarsePhysicalHarmonicBlock x.1 m n (harmonicSphereRotation n ij.1 ij.2 z)⟫_ℝ = _
  exact real_inner_comm _ w

def adjointConstraintL (ij : I × I) (u v : SphereSobolev 1) : CoarseDegreeData →L[ℝ] ℝ :=
  (innerSL ℝ (sphereSobolevInclusionL 1 0 (by norm_num) v)).comp
    ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) u).comp (rotationProjectionL ij))-
  (innerSL ℝ (sphereSobolevInclusionL 1 0 (by norm_num) u)).comp
    ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) v).comp (adjointProjectionL ij))

lemma adjointConstraintL_apply (ij : I × I) (u v : SphereSobolev 1) (x : CoarseDegreeData) :
    adjointConstraintL ij u v x =
      ⟪x.2.1 ij u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ-
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,x.2.2 ij v⟫_ℝ := by
  change ⟪sphereSobolevInclusionL 1 0 (by norm_num) v,x.2.1 ij u⟫_ℝ-
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,x.2.2 ij v⟫_ℝ = _
  exact congrArg (fun a : ℝ => a-⟪sphereSobolevInclusionL 1 0 (by norm_num) u,x.2.2 ij v⟫_ℝ)
    (real_inner_comm (x.2.1 ij u) (sphereSobolevInclusionL 1 0 (by norm_num) v))

abbrev ConstraintIndex := (Σ _ij : I × I,Σ m : ℕ,Σ n : ℕ,
  harmonicSphereSubspace n × harmonicSphereSubspace m) ⊕ ((I × I) × SphereSobolev 1 × SphereSobolev 1)

def constraintL : ConstraintIndex → CoarseDegreeData →L[ℝ] ℝ
  | Sum.inl ⟨ij,m,n,z,w⟩ => rotationConstraintL ij m n z w
  | Sum.inr (ij,u,v) => adjointConstraintL ij u v

abbrev compatibleData := simultaneousScalarKernel (E := CoarseDegreeData) constraintL

lemma mem_compatibleData_iff (x : CoarseDegreeData) : x ∈ compatibleData ↔
    (∀ ij : I × I,∀ m n : ℕ,∀ z,
      coarsePhysicalHarmonicBlock (x.2.1 ij) m n z =
        harmonicSphereRotation m ij.1 ij.2 (coarsePhysicalHarmonicBlock x.1 m n z)-
          coarsePhysicalHarmonicBlock x.1 m n (harmonicSphereRotation n ij.1 ij.2 z)) ∧
    (∀ ij,∀ u v : SphereSobolev 1,
      ⟪x.2.1 ij u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,x.2.2 ij v⟫_ℝ) := by
  rw [mem_simultaneousScalarKernel_iff]
  constructor
  · intro hx
    constructor
    · intro ij m n z
      apply sub_eq_zero.mp
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      have hh := hx (Sum.inl ⟨ij,m,n,z,
        coarsePhysicalHarmonicBlock (x.2.1 ij) m n z-
          (harmonicSphereRotation m ij.1 ij.2 (coarsePhysicalHarmonicBlock x.1 m n z)-
            coarsePhysicalHarmonicBlock x.1 m n (harmonicSphereRotation n ij.1 ij.2 z))⟩)
      change rotationConstraintL ij m n z _ x = 0 at hh
      rw [rotationConstraintL_apply] at hh
      have hAlg : coarsePhysicalHarmonicBlock (x.2.1 ij) m n z-
          harmonicSphereRotation m ij.1 ij.2 (coarsePhysicalHarmonicBlock x.1 m n z)+
          coarsePhysicalHarmonicBlock x.1 m n (harmonicSphereRotation n ij.1 ij.2 z) =
        coarsePhysicalHarmonicBlock (x.2.1 ij) m n z-
          (harmonicSphereRotation m ij.1 ij.2 (coarsePhysicalHarmonicBlock x.1 m n z)-
            coarsePhysicalHarmonicBlock x.1 m n (harmonicSphereRotation n ij.1 ij.2 z)) := by abel
      rw [hAlg] at hh
      exact hh
    · intro ij u v
      have hh := hx (Sum.inr (ij,u,v))
      change adjointConstraintL ij u v x = 0 at hh
      rw [adjointConstraintL_apply] at hh
      exact sub_eq_zero.mp hh
  · rintro ⟨hGraph,hDual⟩ (_|_)
    · rename_i z
      rcases z with ⟨ij,m,n,z,w⟩
      change rotationConstraintL ij m n z w x = 0
      rw [rotationConstraintL_apply]
      have hZero : coarsePhysicalHarmonicBlock (x.2.1 ij) m n z-
          harmonicSphereRotation m ij.1 ij.2 (coarsePhysicalHarmonicBlock x.1 m n z)+
          coarsePhysicalHarmonicBlock x.1 m n (harmonicSphereRotation n ij.1 ij.2 z) = 0 := by
        rw [hGraph]
        abel
      rw [hZero,inner_zero_left]
    · rename_i z
      rcases z with ⟨ij,u,v⟩
      change adjointConstraintL ij u v x = 0
      rw [adjointConstraintL_apply,hDual,sub_self]

end ShrinkingSpheres.CoarseDegreeCompatibility
