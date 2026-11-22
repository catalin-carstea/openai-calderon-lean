module

public import Proof.CalderonN.SmoothSupportedFiberHigherDerivatives
public import Proof.CalderonN.SupportedSphereMultiplierBounds

import Proof.CalderonN.ProductHarmonicDerivatives
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! Joint normalized scalar jets control the angular norm of the
ordinary base derivatives of a multiplier. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

@[expose] def parametricScalarBaseDerivative (f : X dim × X dim → ℝ) :
    (n : ℕ) → (Fin n → X dim) → X dim × X dim → ℝ
  | 0, _ => f
  | n+1,a => fun p => fderiv ℝ (parametricScalarBaseDerivative f n (Fin.tail a)) p (a 0,0)

theorem contDiff_parametricScalarBaseDerivative (f : X dim × X dim → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (a : Fin n → X dim) :
    ContDiff ℝ ∞ (parametricScalarBaseDerivative f n a) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact ((ih (Fin.tail a)).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

theorem LocalSmoothJetBudget.base_derivatives
    {f : X dim × X dim → ℝ} {p : X dim × X dim} {k : ℕ} {C : ℝ}
    (n : ℕ) (a : Fin n → X dim) (ha : ∀ i,‖a i‖ ≤ 1) (h : LocalSmoothJetBudget f p (k+n) C) :
    LocalSmoothJetBudget (parametricScalarBaseDerivative f n a) p k C := by
  induction n generalizing k with
  | zero => exact h
  | succ n ih =>
    have h₀ : LocalSmoothJetBudget f p ((k+1)+n) C := by
      rw [show (k+1)+n = k+(n+1) by omega]
      exact h
    have h₁ := ih (Fin.tail a) (fun i => ha i.succ) h₀
    exact h₁.base_axis (a 0) (ha 0)

theorem parametricScalarBaseDerivative_normalized
    (f : X dim × X dim → ℝ) (hf : ContDiff ℝ ∞ f) (x z : X dim) (β : ℝ)
    (n : ℕ) (a : Fin n → X dim) :
    let g (p : X dim × X dim) := (x+β⁻¹ • p.1,z+p.2)
    parametricScalarBaseDerivative (f ∘ g) n a =
      fun p => (β⁻¹)^n • (parametricScalarBaseDerivative f n a (g p)) := by
  dsimp only
  induction n with
  | zero =>
    funext p
    simp only [parametricScalarBaseDerivative,Function.comp_apply,pow_zero,one_smul]
  | succ n ih =>
    let g (p : X dim × X dim) := (x+β⁻¹ • p.1,z+p.2)
    let F := parametricScalarBaseDerivative f n (Fin.tail a)
    have hF := contDiff_parametricScalarBaseDerivative f hf n (Fin.tail a)
    have hFg : ContDiff ℝ ∞ (F ∘ g) := hF.comp
      ((contDiff_const.add (contDiff_fst.const_smul _)).prodMk (contDiff_const.add contDiff_snd))
    funext p
    change fderiv ℝ (parametricScalarBaseDerivative (f ∘ g) n (Fin.tail a)) p (a 0,0) =
      (β⁻¹)^(n+1) • fderiv ℝ F (g p) (a 0,0)
    rw [ih (Fin.tail a)]
    change fderiv ℝ ((β⁻¹)^n • (F ∘ g)) p (a 0,0) = _
    have hsmul : fderiv ℝ ((β⁻¹)^n • (F ∘ g)) p = (β⁻¹)^n • fderiv ℝ (F ∘ g) p :=
      fderiv_const_smul (hFg.differentiable (by simp) p) _
    rw [hsmul,smul_apply]
    have hF' := congrFun (normalized_multiplier_baseAxis F hF x z β (a 0)) p
    change fderiv ℝ (F ∘ g) p (a 0,0) = β⁻¹ • fderiv ℝ F (g p) (a 0,0) at hF'
    rw [hF',smul_smul,pow_succ]

theorem localSmoothJetBudget_parametric_baseDerivative_slice
    (f : X dim × X dim → ℝ) (hf : ContDiff ℝ ∞ f) (x z : X dim) (β : ℝ) (hβ : 0 < β)
    (k n : ℕ) (a : Fin n → X dim) (ha : ∀ i,‖a i‖ ≤ 1) {C : ℝ}
    (h : LocalSmoothJetBudget (fun p : X dim × X dim => f (x+β⁻¹ • p.1,z+p.2)) 0 (k+n) C) :
    LocalSmoothJetBudget (fun w => parametricScalarBaseDerivative f n a (x,w)) z k
      (((k.factorial:ℝ)*C)*β^n) := by
  let g (p : X dim × X dim) := (x+β⁻¹ • p.1,z+p.2)
  let F := parametricScalarBaseDerivative f n a
  have h₀ := h.base_derivatives n a ha
  change LocalSmoothJetBudget (parametricScalarBaseDerivative (f ∘ g) n a) 0 k C at h₀
  rw [parametricScalarBaseDerivative_normalized f hf x z β n a] at h₀
  have h₁ := h₀.const_smul (β^n) (pow_nonneg hβ.le n)
  have he : (fun p : X dim × X dim => β^n • ((β⁻¹)^n • F (g p))) = F ∘ g := by
    funext p
    rw [smul_smul,inv_pow,mul_inv_cancel₀ (pow_ne_zero _ hβ.ne'),one_smul]
    rfl
  change LocalSmoothJetBudget (fun p : X dim × X dim => β^n • ((β⁻¹)^n • F (g p))) 0 k _ at h₁
  rw [he] at h₁
  have h₂ := localSmoothJetBudget_angular_slice (F ∘ g) (0 : X dim) (0 : X dim) z h₁
  have hslice : (fun w : X dim => (F ∘ g) (0,0+(w-z))) = fun w => F (x,w) := by
    funext w
    simp [Function.comp_apply,g,sub_eq_add_neg,add_left_comm,add_assoc]
  rw [hslice] at h₂
  exact h₂.enlarge (by ring_nf; rfl)

@[expose] def smoothParametricScalarSlice (f : X dim × X dim → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : X dim) : SmoothData dim :=
  ⟨fun z => f (x,z),hf.comp (contDiff_const.prodMk contDiff_id)⟩

theorem supportedSphereMultiplier_iteratedDerivative_eq_of_eqOn
    (hY : IsOpen Y) (m : ∀ x ∈ Y,SmoothData dim)
    (hM : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m))
    {U : Set (X dim)} (hU : IsOpen U) (hUY : U ⊆ Y)
    (f : X dim × X dim → ℝ) (hf : ContDiff ℝ ∞ f)
    (hr : ∀ x ∈ U,∀ hx : x ∈ Y,∀ z ∈ standardSphere dim,f (x,z) = (m x hx).1 z)
    (n : ℕ) (a : Fin n → X dim) {x : X dim} (hx : x ∈ U) :
    let F : RegularTraceFiberFamily Y := ⟨supportedSphereMultiplierFamily m,hM⟩
    (F.iteratedDerivative hY n a).1 x =
      smoothSphereTraceMul (smoothParametricScalarSlice (parametricScalarBaseDerivative f n a)
        (contDiff_parametricScalarBaseDerivative f hf n a) x) := by
  dsimp only
  let F : RegularTraceFiberFamily Y := ⟨supportedSphereMultiplierFamily m,hM⟩
  induction n generalizing x with
  | zero =>
    rw [show (F.iteratedDerivative hY 0 a).1 x = smoothSphereTraceMul (m x (hUY hx)) by
      simp only [RegularTraceFiberFamily.iteratedDerivative,F,supportedSphereMultiplierFamily,dite_eq_left (hUY hx)]]
    ext u : 1
    apply Subtype.ext
    funext z
    rw [smoothSphereTraceMul_apply,smoothSphereTraceMul_apply]
    exact congrArg (· * u.1 z) (hr x hx (hUY hx) z z.2).symm
  | succ n ih =>
    let g := parametricScalarBaseDerivative f n (Fin.tail a)
    let hg := contDiff_parametricScalarBaseDerivative f hf n (Fin.tail a)
    let G := F.iteratedDerivative hY n (Fin.tail a)
    let p (y : X dim) (_ : y ∈ Y) := smoothParametricScalarSlice g hg y
    have hP : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily p) :=
      supportedSphereMultiplierFamily_regular hY p
        (fun y hy => ⟨Y,g,hY,hy,Subset.rfl,hg.contDiffOn,fun _ _ _ _ _ => rfl⟩)
    have he : G.1 =ᶠ[𝓝 x] supportedSphereMultiplierFamily p := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [supportedSphereMultiplierFamily,dite_eq_left (hUY hy)]
      exact ih (Fin.tail a) hy
    change smoothSupportedTraceFiberDerivative hY G.1 G.2 (a 0) x = _
    rw [smoothSupportedTraceFiberDerivative_eq_of_eventuallyEq hY G.2 hP (a 0) (hUY hx) he]
    apply supportedSphereMultiplierFamily_derivative_eq hY p hP (hUY hx) (a 0) g
      (fun _ _ => hg.contDiffAt) (fun _ _ => Filter.Eventually.of_forall fun _ _ => rfl)
    intro z _
    exact fderiv_productSlice_left_apply hg x z (a 0)

end CalderonN
