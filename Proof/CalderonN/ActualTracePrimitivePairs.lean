module

public import Proof.CalderonN.PairedTraceFiberFamilyBounds
public import Proof.CalderonN.UniformActualTraceAngularAtoms
public import Proof.CalderonN.SupportedSphereMultiplierGerms

import Mathlib.Tactic

/-! Regular paired actions of the primitive angular operators and
their value and base derivative bounds. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}
variable {B R : Module.End ℝ (SmoothSphereTrace dim)} {J C : ℝ}

namespace PairedTraceFiberFamily

@[expose] def multiplier (m : ∀ x ∈ Y,SmoothData dim)
    (hM : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m)) :
    PairedTraceFiberFamily hn Y :=
  symmetric ⟨supportedSphereMultiplierFamily m,hM⟩ (fun x hx =>
    supportedSphereMultiplierFamily_selfAdjoint hn m x hx)

@[expose] def coordinate (i : I dim) : PairedTraceFiberFamily hn Y :=
  symmetric ⟨fun _ => smoothSphereTraceMul (smoothCoordinateData i),
    smoothSupportedTraceFiberRegular_constMultiplier _⟩ (fun _ _ => smoothSphereTraceMul_symmetric hn _)

@[expose] def degree {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    PairedTraceFiberFamily hn Y :=
  symmetric ⟨fun _ => smoothTraceFlatDegree hA hEll S,smoothSupportedTraceFiberRegular_flatDegree hA hEll S Y⟩
    (fun _ _ => smoothTraceFlatDegree_symmetric hn hA hEll S)

@[expose] def rotation (i j : I dim) : PairedTraceFiberFamily hn Y :=
  let F : RegularTraceFiberFamily Y := ⟨fun _ => smoothSphereTraceRotation i j,smoothSupportedTraceFiberRegular_rotation i j⟩
  ⟨F,F.neg,fun _ _ => smoothTraceRotation_skew hn i j⟩

theorem rotation_bounds (H : ActualTraceAngularBasis hn B R J C)
    (hY : IsOpen Y) (x : X dim) (hx : x ∈ Y) (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) (i j : I dim) :
    PairedTraceFiberFamilyBounds H.atoms hY x β N 1 C (rotation i j) := by
  have h := H.rotation i j
  refine ⟨SmoothSupportedFiberJetBound.constFamily _ hx hβ h.nonneg h.angular,h,?_⟩
  have hr := h.const_smul (-1:ℝ)
  have he : (-1:ℝ) • smoothSphereTraceRotation i j = -smoothSphereTraceRotation i j :=
    by ext u : 1; simp only [LinearMap.smul_apply,LinearMap.neg_apply,neg_one_smul]
  rw [he,abs_neg,abs_one,one_mul] at hr
  exact hr

theorem coordinate_bounds (H : ActualTraceAngularBasis hn B R J C) (hJ : 1 ≤ J)
    (hY : IsOpen Y) (x : X dim) (hx : x ∈ Y) (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) (i : I dim) :
    PairedTraceFiberFamilyBounds H.atoms hY x β N 0 C (coordinate i) := by
  have h := H.multiplier (smoothCoordinateData i) (coordinateData_hasJets i J hJ)
  exact ⟨SmoothSupportedFiberJetBound.constFamily _ hx hβ h.nonneg h.angular,h,h⟩

theorem degree_bounds {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (H : ActualTraceAngularBasis hn (smoothTraceFlatDegree hA hEll S) R J C)
    (hY : IsOpen Y) (x : X dim) (hx : x ∈ Y) (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) :
    PairedTraceFiberFamilyBounds H.atoms hY x β N 1 C (degree hA hEll S) :=
  ⟨SmoothSupportedFiberJetBound.constFamily _ hx hβ H.degree.nonneg H.degree.angular,H.degree,H.degree⟩

theorem multiplier_bounds (H : ActualTraceAngularBasis hn B R J C)
    (hY : IsOpen Y) (x : X dim) (hx : x ∈ Y) (β : ℝ) (hβ : 0 < β)
    {A : ℝ} (hA : 0 ≤ A) (hAJ : 6*A ≤ J) (m : ∀ x ∈ Y,SmoothData dim)
    (hM : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m))
    (hG : SupportedSphereMultiplierGerm m x β A) :
    PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (C+smoothTraceMultiplierJetConstant dim (2*A))
      (multiplier m hM) := by
  obtain ⟨f,hf,hJets⟩ := hG.angularRepresentative
  have h := H.multiplier f (fun z hz => (hJets z hz).enlarge hAJ)
  have hF : SmoothTraceSymbolBounds H.atoms 0 C (supportedSphereMultiplierFamily m x) := by rwa [hf]
  have hV := smoothTraceMultiplierJetConstant_nonneg (dim:=dim) (2*A) (by positivity)
  have hJet := hG.angularBaseJets hY hβ hA hM hn
  exact ⟨hJet.enlarge hβ.le (le_add_of_nonneg_left h.nonneg),
    hF.enlarge (le_add_of_nonneg_right hV),hF.enlarge (le_add_of_nonneg_right hV)⟩

end PairedTraceFiberFamily

end CalderonN
