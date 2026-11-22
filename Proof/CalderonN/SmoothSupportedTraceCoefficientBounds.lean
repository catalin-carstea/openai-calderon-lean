module

public import Proof.CalderonN.SmoothTraceCommutatorBounds
public import Proof.CalderonN.SmoothSupportedFiberDerivativeCalculus
public import Proof.CalderonN.SupportedSphereMultiplierDerivative
public import Proof.CalderonN.ActualSupportedAffineRegular

import Mathlib.Tactic

/-! The first base jet of a fiber coefficient costs one factor of beta.
Angular rotation and degree commutators preserve its angular order. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}
variable {hY : IsOpen Y} {x : X dim} {β : ℝ}

structure SmoothSupportedTraceCoefficientBounds (hn : 3 ≤ dim)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hY : IsOpen Y) (x : X dim) (β : ℝ)
    (k : ℕ) (C : ℝ) (F : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hF : SmoothSupportedTraceFiberRegular Y F) : Prop where
  angular : SmoothTraceCommutatorBounds hn B k C (F x)
  first : ∀ a : X dim, ‖a‖ ≤ 1 →
    SmoothTraceAngularBound hn k (C*β) (smoothSupportedTraceFiberDerivative hY F hF a x)

namespace SmoothSupportedTraceCoefficientBounds

variable {hn : 3 ≤ dim} {B : Module.End ℝ (SmoothSphereTrace dim)}
variable {F G : X dim → Module.End ℝ (SmoothSphereTrace dim)}
variable {hF : SmoothSupportedTraceFiberRegular Y F} {hG : SmoothSupportedTraceFiberRegular Y G}
variable {k l : ℕ} {C D : ℝ}

theorem enlarge (h : SmoothSupportedTraceCoefficientBounds hn B hY x β k C F hF)
    (hβ : 0 ≤ β) (hCD : C ≤ D) :
    SmoothSupportedTraceCoefficientBounds hn B hY x β k D F hF :=
  ⟨h.angular.enlarge hCD,fun a ha => (h.first a ha).enlarge (mul_le_mul_of_nonneg_right hCD hβ)⟩

theorem weaken (h : SmoothSupportedTraceCoefficientBounds hn B hY x β k C F hF)
    (hβ : 0 ≤ β) (hkl : k ≤ l) :
    SmoothSupportedTraceCoefficientBounds hn B hY x β l C F hF :=
  ⟨h.angular.weaken hkl,fun a ha => (h.first a ha).weaken (mul_nonneg h.angular.nonneg hβ) hkl⟩

theorem congr (h : SmoothSupportedTraceCoefficientBounds hn B hY x β k C F hF)
    (hx : x ∈ Y) (he : F =ᶠ[𝓝 x] G) :
    SmoothSupportedTraceCoefficientBounds hn B hY x β k C G hG := by
  refine ⟨he.eq_of_nhds ▸ h.angular,?_⟩
  intro a ha
  rw [← smoothSupportedTraceFiberDerivative_eq_of_eventuallyEq hY hF hG a hx he]
  exact h.first a ha

theorem add (h : SmoothSupportedTraceCoefficientBounds hn B hY x β k C F hF)
    (g : SmoothSupportedTraceCoefficientBounds hn B hY x β k D G hG) (hx : x ∈ Y) :
    SmoothSupportedTraceCoefficientBounds hn B hY x β k (C+D) (fun y => F y+G y) (hF.add hG) := by
  refine ⟨h.angular.add g.angular,?_⟩
  intro a ha
  rw [smoothSupportedTraceFiberDerivative_add hY F G hF hG a hx,add_mul]
  exact (h.first a ha).add (g.first a ha)

theorem sub (h : SmoothSupportedTraceCoefficientBounds hn B hY x β k C F hF)
    (g : SmoothSupportedTraceCoefficientBounds hn B hY x β k D G hG) (hx : x ∈ Y) :
    SmoothSupportedTraceCoefficientBounds hn B hY x β k (C+D) (fun y => F y-G y) (hF.sub hG) := by
  refine ⟨h.angular.sub g.angular,?_⟩
  intro a ha
  rw [smoothSupportedTraceFiberDerivative_sub hY F G hF hG a hx,add_mul]
  exact (h.first a ha).sub (g.first a ha)

theorem mul (h : SmoothSupportedTraceCoefficientBounds hn B hY x β k C F hF)
    (g : SmoothSupportedTraceCoefficientBounds hn B hY x β l D G hG)
    (hx : x ∈ Y) (hβ : 0 ≤ β) :
    SmoothSupportedTraceCoefficientBounds hn B hY x β (k+l) (C*D+C*D)
      (fun y => F y*G y) (hF.mul hY hG) := by
  refine ⟨h.angular.mul g.angular,?_⟩
  intro a ha
  rw [smoothSupportedTraceFiberDerivative_mul hY F G hF hG a hx]
  have hA := (h.first a ha).mul g.angular.bound (mul_nonneg h.angular.nonneg hβ)
  have hB := h.angular.bound.mul (g.first a ha) h.angular.nonneg
  convert hA.add hB using 1
  ring

theorem const {T : Module.End ℝ (SmoothSphereTrace dim)}
    {hT : SmoothSupportedTraceFiberRegular Y (fun _ => T)}
    (h : SmoothTraceCommutatorBounds hn B k C T) (hx : x ∈ Y) (hβ : 0 ≤ β) :
    SmoothSupportedTraceCoefficientBounds hn B hY x β k C (fun _ => T) hT := by
  refine ⟨h,?_⟩
  intro a _ i j _ u
  rw [smoothSupportedTraceFiberDerivative_const hY T hT a hx,LinearMap.zero_apply]
  simp only [traceOrderNorm,map_zero,norm_zero]
  positivity [h.nonneg]

theorem base_smul (h : SmoothSupportedTraceCoefficientBounds hn B hY x β k C F hF)
    (hx : x ∈ Y) (hβ : 0 ≤ β) (c : X dim → ℝ) (hc : ContDiffOn ℝ ∞ c Y)
    (hD : 0 ≤ D) (hC₀ : |c x| ≤ D) (hC₁ : ∀ a : X dim, ‖a‖ ≤ 1 → |fderiv ℝ c x a| ≤ D*β) :
    SmoothSupportedTraceCoefficientBounds hn B hY x β k (D*C+D*C) (fun y => c y • F y)
      (hF.base_smul hY hc) := by
  have hAng := (h.angular.const_smul (c x)).enlarge
    ((mul_le_mul_of_nonneg_right hC₀ h.angular.nonneg).trans (le_add_of_nonneg_right (mul_nonneg hD h.angular.nonneg)))
  refine ⟨hAng,?_⟩
  intro a ha
  let P (y : X dim) := c y • (1 : Module.End ℝ (SmoothSphereTrace dim))
  let hP := smoothSupportedTraceFiberRegular_smul hY hc
  have he : (fun y => c y • F y) = (fun y => P y * F y) := by
    funext y
    simp only [P,smul_mul_assoc,one_mul]
  rw [smoothSupportedTraceFiberDerivative_eq_of_eventuallyEq hY (hF.base_smul hY hc)
    (hP.mul hY hF) a hx (he ▸ EventuallyEq.rfl)]
  rw [smoothSupportedTraceFiberDerivative_mul hY P F hP hF a hx,
    smoothSupportedTraceFiberDerivative_scalar hY c hc a hx]
  simp only [P,smul_mul_assoc,one_mul]
  have h₁ := (h.angular.bound.const_smul (fderiv ℝ c x a)).enlarge
    (mul_le_mul_of_nonneg_right (hC₁ a ha) h.angular.nonneg)
  have h₂ := ((h.first a ha).const_smul (c x)).enlarge
    (mul_le_mul_of_nonneg_right hC₀ (mul_nonneg h.angular.nonneg hβ))
  convert h₁.add h₂ using 1
  ring

end SmoothSupportedTraceCoefficientBounds

end CalderonN
