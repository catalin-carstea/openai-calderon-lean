module

public import Proof.CalderonN.FinitePhysicalDegreeForm
public import Proof.CalderonN.FiniteFlatRadialOperator

import Mathlib.Tactic

/-! The spectral comparison on finite packets gives the degree
commutator of the same symmetric operator on the actual sphere. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace DirectSum Classical
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim]

def finiteHarmonicSphereL (hn : 3 ≤ dim) : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim :=
  (smoothBoundaryLiftL hn).comp harmonicFiniteSmoothL

theorem finiteHarmonicSphereL_apply (hn : 3 ≤ dim) (f : HarmonicFiniteCoefficients dim) :
    finiteHarmonicSphereL hn f = smoothSphereLift (harmonicFiniteSmooth f).1 (harmonicFiniteSmooth f).2 := by
  rw [finiteHarmonicSphereL,LinearMap.comp_apply,smoothBoundaryLiftL_apply]
  exact smoothSphereLift_eq_of_eqOn ⟨(harmonicFiniteSmoothL f).1,smoothBallData_contDiff (harmonicFiniteSmoothL f)⟩ (harmonicFiniteSmooth f)
    (fun z _ => congrFun (harmonicFiniteSmoothL_val f) z)

theorem finiteHarmonicSphereL_eq_sobolev (hn : 3 ≤ dim) (f : HarmonicFiniteCoefficients dim) :
    finiteHarmonicSphereL hn f =
      (sphereSobolevZeroEquiv (dim:=dim)).symm (harmonicBoundaryFiniteL 0 f) := by
  rw [finiteHarmonicSphereL_apply,← smoothBoundarySobolev_harmonicFiniteSmooth hn 0 (by norm_num),
    smoothBoundarySobolev_zero_eq,LinearIsometryEquiv.symm_apply_apply]

theorem finiteHarmonicSphereL_rotation_apply (hn : 3 ≤ dim) (i j : Fin dim)
    (f : HarmonicFiniteCoefficients dim) :
    finiteHarmonicSphereL hn (finiteHarmonicRotationL i j f) =
      smoothSphereLift (sphereRotationDerivative i j (harmonicFiniteSmooth f).1)
        (contDiff_sphereRotationDerivative i j _ (harmonicFiniteSmooth f).2) := by
  rw [finiteHarmonicSphereL_apply]
  exact smoothSphereLift_eq_of_eqOn (harmonicFiniteSmooth _) ⟨_,contDiff_sphereRotationDerivative
    i j _ (harmonicFiniteSmooth f).2⟩ (fun z _ => congrFun (harmonicFiniteSmooth_rotation i j f) z)

private theorem finiteHarmonicPacket_of_support_subset (f : HarmonicFiniteCoefficients dim)
    (s : Finset ℕ) (hs : f.support ⊆ s) : finiteHarmonicPacket s f = f := by
  conv_rhs => rw [← finiteHarmonicPacket_support f]
  simp only [finiteHarmonicPacket]
  symm
  apply Finset.sum_subset hs
  intro k _ hk
  rw [show f k = 0 from DFinsupp.notMem_support_iff.mp hk,map_zero]

/-- Adjointness and the block identities are derived from the genuine
smooth rotation and the symmetric finite harmonic pairing. -/
theorem abs_finite_smooth_degree_pair_le (hn : 3 ≤ dim)
    (T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim) (τ : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hτ : ∀ f,T f = smoothSphereLift (τ f).1 (τ f).2)
    (hSym : ∀ f g, ⟪T f,finiteHarmonicSphereL hn g⟫_ℝ =
      ⟪finiteHarmonicSphereL hn f,T g⟫_ℝ)
    (P : Fin dim × Fin dim → HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim)
    (hRot : ∀ ij f, P ij f =
      smoothSphereLift (sphereRotationDerivative ij.1 ij.2 (τ f).1)
        (contDiff_sphereRotationDerivative ij.1 ij.2 _ (τ f).2)-T (finiteHarmonicRotationL ij.1 ij.2 f))
    (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ ij f, ‖P ij f‖ ≤ B*‖harmonicBoundaryFiniteL 1 f‖)
    (f g : HarmonicFiniteCoefficients dim) :
    |⟪T f,finiteHarmonicSphereL hn (finiteHarmonicDegreeL g)⟫_ℝ-
      ⟪T (finiteHarmonicDegreeL f),finiteHarmonicSphereL hn g⟫_ℝ| ≤
      (dim:ℝ)^4*(B+B)*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖ := by
  have hDual (ij : Fin dim × Fin dim) (x y : HarmonicFiniteCoefficients dim) :
      ⟪P ij x,finiteHarmonicSphereL hn y⟫_ℝ = ⟪finiteHarmonicSphereL hn x,P ij y⟫_ℝ := by
    rw [hRot,hRot,inner_sub_left,inner_sub_right]
    have h₁ := inner_sphereRotationDerivative_skew ij.1 ij.2 (τ x).1 (harmonicFiniteSmooth y).1
      (τ x).2 (harmonicFiniteSmooth y).2
    have h₂ := inner_sphereRotationDerivative_skew ij.1 ij.2 (harmonicFiniteSmooth x).1 (τ y).1
      (harmonicFiniteSmooth x).2 (τ y).2
    rw [← finiteHarmonicSphereL_apply hn y,← hτ x,← finiteHarmonicSphereL_rotation_apply hn] at h₁
    rw [← finiteHarmonicSphereL_apply hn x,← hτ y,← finiteHarmonicSphereL_rotation_apply hn] at h₂
    rw [h₁, hSym x, hSym (finiteHarmonicRotationL ij.1 ij.2 x)]
    linarith only [h₂]
  have hGraph (ij : Fin dim × Fin dim) (m n : ℕ) (z : harmonicSphereSubspace dim n) :
      physicalHarmonicBlock (P ij) m n z =
        harmonicSphereRotation m ij.1 ij.2 (physicalHarmonicBlock T m n z)-
        physicalHarmonicBlock T m n (harmonicSphereRotation n ij.1 ij.2 z) := by
    simp only [physicalHarmonicBlock,LinearMap.comp_apply,ContinuousLinearMap.coe_coe]
    let a := DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace dim k)) n z
    rw [hRot,map_sub,harmonicProjection_sphereRotationDerivative m ij.1 ij.2 (τ a).1 (τ a).2,
      ← hτ,finiteHarmonicRotationL_lof]
  let s := f.support ∪ g.support
  have hf := finiteHarmonicPacket_of_support_subset f s Finset.subset_union_left
  have hg := finiteHarmonicPacket_of_support_subset g s Finset.subset_union_right
  have hCmp := abs_finite_physical_degree_form_le hn T P P B B hB hB hP hP
    (fun ij x y => by simpa only [finiteHarmonicSphereL_eq_sobolev] using hDual ij x y) hGraph s f g
  rw [hf,hg] at hCmp
  refine (le_of_eq ?_).trans hCmp
  congr 1
  have hDegree (x y : HarmonicFiniteCoefficients dim) :
      ⟪T (finiteHarmonicPacket s x), finiteHarmonicSphereL hn (finiteHarmonicDegreeL (finiteHarmonicPacket s y))⟫_ℝ =
        ∑ m ∈ s,∑ n ∈ s,(m:ℝ)*⟪physicalHarmonicBlock T m n (x n),y m⟫_ℝ := by
    rw [finiteHarmonicDegreeL_packet,finiteHarmonicSphereL_eq_sobolev,sphereSobolevZeroEquiv_symm_packet,
      ← physicalHarmonicBlock_pairing]
    simp only [real_inner_smul_right]
  have hDegree' (x y : HarmonicFiniteCoefficients dim) :
      ⟪T (finiteHarmonicDegreeL (finiteHarmonicPacket s x)), finiteHarmonicSphereL hn (finiteHarmonicPacket s y)⟫_ℝ =
        ∑ m ∈ s,∑ n ∈ s,(n:ℝ)*⟪physicalHarmonicBlock T m n (x n),y m⟫_ℝ := by
    rw [finiteHarmonicDegreeL_packet,finiteHarmonicSphereL_eq_sobolev,sphereSobolevZeroEquiv_symm_packet,
      ← physicalHarmonicBlock_pairing]
    simp only [map_smul,real_inner_smul_left]
  have he := congrArg₂ (fun x y => ⟪T x,finiteHarmonicSphereL hn (finiteHarmonicDegreeL y)⟫_ℝ -
    ⟪T (finiteHarmonicDegreeL x),finiteHarmonicSphereL hn y⟫_ℝ) hf hg
  rw [← he,hDegree,hDegree',← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

end CalderonN
