module

public import Proof.CalderonN.FiniteConormalModelRotation
public import Proof.CalderonN.FiniteConormalTaylorSymmetry

import Mathlib.Tactic

/-! One common family of smooth Dirichlet solutions realizes the
conormal Taylor remainder and its actual rotation commutators. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_finiteConormalTaylorOperators (hn : 3 ≤ dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) {lo hi : ℝ}
    (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    (hSym : ∀ z ∈ ball (0 : X dim) 1, (A z).IsSymm)
    (b : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hbT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hbH : ∀ f, EqOn (negativeBallDivergence A (b f).1) 0 (ball (0 : X dim) 1))
    (W : SmoothData dim)
    (hW : ∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim))
    (ell : X dim →L[ℝ] ℝ) (r : ℝ) :
    ∃ (T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim)
      (P : Fin dim × Fin dim → HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim)
      (τ : HarmonicFiniteCoefficients dim → SmoothData dim),
      (∀ f,T f = smoothSphereLift (τ f).1 (τ f).2) ∧
      (∀ f g, ⟪T f,finiteHarmonicSphereL hn g⟫_ℝ = ⟪finiteHarmonicSphereL hn f,T g⟫_ℝ) ∧
      (∀ ij f, P ij f =
        smoothSphereLift (sphereRotationDerivative ij.1 ij.2 (τ f).1)
          (contDiff_sphereRotationDerivative ij.1 ij.2 _ (τ f).2)-T (finiteHarmonicRotationL ij.1 ij.2 f)) ∧
      (∀ f, EqOn (τ f).1 (fun z => smoothBallConormal A (b f).1 z -
        (flatRadialDataL f).1 z-r*(firstConormalDataL ell f).1 z) (standardSphere dim)) ∧
      ∀ ij f (Δ : SmoothData dim),
        EqOn Δ.1 (fun z => sphereRotationDerivative ij.1 ij.2 (smoothBallConormal A (b f).1) z -
          smoothBallConormal A (b (finiteHarmonicRotationL ij.1 ij.2 f)).1 z -
          r*(firstConormalDataL (ell.comp (ballRotationGeneratorL ij.1 ij.2)) f).1 z) (standardSphere dim) →
        P ij f = smoothSphereLift Δ.1 Δ.2 := by
  let S := smoothBoundaryLiftL (dim:=dim) hn
  let CW := smoothBallDataMulL W
  let R := flatRadialDataL (dim:=dim)+r • firstConormalDataL ell
  let Sol f := smoothBallRadialDataL (⟨(b f).1,(b f).2⟩ : smoothBallDataSubmodule dim)
  let U f := CW (Sol f)-R f
  let τ f : SmoothData dim := ⟨(U f).1,smoothBallData_contDiff (U f)⟩
  let L (B : smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim)
      (hB : ∀ u v, EqOn u.1 v.1 (standardSphere dim) → EqOn (B u).1 (B v).1 (standardSphere dim)) :=
    finiteSphereMappedRadialResponseL hn B hB hA hEll b hbT hbH
  have hCW := smoothBallDataMulL_congr W
  let T := L CW hCW-S.comp R
  let K (ij : Fin dim × Fin dim) := smoothBallAngularDataL ij.1 ij.2
  let Rθ (ij : Fin dim × Fin dim) := finiteHarmonicRotationL ij.1 ij.2
  have hK (ij : Fin dim × Fin dim) := smoothBallAngularDataL_congr (dim:=dim) ij.1 ij.2
  let P (ij : Fin dim × Fin dim) :=
    L ((K ij).comp CW) (fun u v h => hK ij _ _ (hCW u v h))-
      (S.comp (K ij)).comp R-T.comp (Rθ ij)
  have hTτ (f : HarmonicFiniteCoefficients dim) : T f = S (U f) := by
    simp only [T,L,LinearMap.sub_apply,LinearMap.comp_apply,finiteSphereMappedRadialResponseL_apply,
      U,map_sub,S,Sol]
  have hτ (f : HarmonicFiniteCoefficients dim) :
      T f = smoothSphereLift (τ f).1 (τ f).2 := by rw [hTτ,show S = smoothBoundaryLiftL hn from rfl,smoothBoundaryLiftL_apply]
  have hP' (ij : Fin dim × Fin dim) (f : HarmonicFiniteCoefficients dim) :
      P ij f = S (K ij (U f)-U (Rθ ij f)) := by
    simp only [P,L,LinearMap.sub_apply,LinearMap.comp_apply,finiteSphereMappedRadialResponseL_apply,
      U,map_sub,S,Sol,hTτ]
  have hP0 (ij : Fin dim × Fin dim) (f : HarmonicFiniteCoefficients dim) :
      P ij f = S (K ij (U f))-T (Rθ ij f) := by rw [hP',map_sub,hTτ]
  have hP (ij : Fin dim × Fin dim) (f : HarmonicFiniteCoefficients dim) :
      P ij f = smoothSphereLift (sphereRotationDerivative ij.1 ij.2 (τ f).1)
        (contDiff_sphereRotationDerivative ij.1 ij.2 _ (τ f).2)-T (Rθ ij f) := by
    rw [hP0,show S = smoothBoundaryLiftL hn from rfl,smoothBoundaryLiftL_apply]
    rfl
  let C f : SmoothData dim := ⟨smoothBallConormal A (b f).1,contDiff_smoothBallConormal hA (b f)⟩
  have hB (f : HarmonicFiniteCoefficients dim) :
      EqOn (CW (Sol f)).1 (C f).1 (standardSphere dim) := by
    intro z hz
    exact (congrFun (smoothBallDataMulL_apply W (Sol f)) z).trans (hW (b f) hz).symm
  have hE (f : HarmonicFiniteCoefficients dim) :
      EqOn (τ f).1 (fun z => smoothBallConormal A (b f).1 z -
        (flatRadialDataL f).1 z-r*(firstConormalDataL ell f).1 z) (standardSphere dim) := by
    intro z hz
    change (CW (Sol f)).1 z-((flatRadialDataL f).1 z+r*(firstConormalDataL ell f).1 z) = _
    rw [hB f hz]
    change _ = (C f).1 z-(flatRadialDataL f).1 z-r*(firstConormalDataL ell f).1 z
    ring
  refine ⟨T,P,τ,hτ,?_,hP,hE,?_⟩
  · intro f g
    rw [hτ,hτ,finiteHarmonicSphereL_apply,finiteHarmonicSphereL_apply,
      smoothSphereLift_inner,smoothSphereLift_inner]
    have hf := hE f
    have hg := hE g
    rw [flatRadialDataL_apply,firstConormalDataL_apply] at hf hg
    exact integral_finiteConormalTaylor_symm hA hSym ell r f g (b f) (b g) (τ f) (τ g)
      (hbH f) (hbH g) (hbT f) (hbT g) hf hg
  intro ij f Δ hΔ
  let J := finiteHarmonicRotationL ij.1 ij.2
  let G : SmoothData dim := ⟨(K ij (U f)-U (J f)).1,smoothBallData_contDiff (K ij (U f)-U (J f))⟩
  rw [hP',show S = smoothBoundaryLiftL hn from rfl,smoothBoundaryLiftL_apply]
  apply smoothSphereLift_eq_of_eqOn G Δ
  intro z hz
  have hKf := hK ij _ _ (hB f) hz
  change sphereRotationDerivative ij.1 ij.2 (CW (Sol f)).1 z =
    sphereRotationDerivative ij.1 ij.2 (C f).1 z at hKf
  have hFlat := congrArg (fun a : smoothBallDataSubmodule dim => a.1 z)
    (flatRadialDataL_commutes_rotation ij.1 ij.2 f)
  have hModel := firstConormalDataL_components_rotation ij.1 ij.2 ell f hz
  have hU : G.1 z =
      (K ij (CW (Sol f))).1 z-((K ij (flatRadialDataL f)).1 z+
        r*(K ij (firstConormalDataL ell f)).1 z) -
      ((CW (Sol (J f))).1 z-((flatRadialDataL (J f)).1 z+r*(firstConormalDataL ell (J f)).1 z)) := by
    dsimp only [G,U,R,LinearMap.add_apply,LinearMap.smul_apply]
    simp only [map_sub,map_add,map_smul]
    rfl
  rw [hU,show (K ij (CW (Sol f))).1 z = _ from hKf,hB (J f) hz,hFlat,hΔ hz]
  change (K ij (firstConormalDataL ell f)).1 z-(firstConormalDataL ell (J f)).1 z =
    (firstConormalDataL (ell.comp (ballRotationGeneratorL ij.1 ij.2)) f).1 z at hModel
  change (sphereRotationDerivative ij.1 ij.2 (C f).1 z -
    ((flatRadialDataL (J f)).1 z+r*(K ij (firstConormalDataL ell f)).1 z)) -
    ((C (J f)).1 z-((flatRadialDataL (J f)).1 z+r*(firstConormalDataL ell (J f)).1 z)) =
    sphereRotationDerivative ij.1 ij.2 (C f).1 z-(C (J f)).1 z -
      r*(firstConormalDataL (ell.comp (ballRotationGeneratorL ij.1 ij.2)) f).1 z
  rw [← hModel]
  ring

end CalderonN
