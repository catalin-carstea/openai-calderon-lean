module

public import Proof.CalderonN.SmoothSupportedTraceCoefficientBounds
public import Proof.CalderonN.SmoothTraceMultiplierJetBounds

import Mathlib.Tactic

/-! An ordinary rescaled chart budget gives uniform bounds for the
actual multiplier family and its ordinary base derivative. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem localSmoothJetBudget_angular_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E × X dim → ℝ) (x : E) (a z : X dim) {N : ℕ} {C : ℝ}
    (h : LocalSmoothJetBudget f (x,a) N C) :
    LocalSmoothJetBudget (fun w => f (x,a+(w-z))) z N ((N.factorial:ℝ)*C) := by
  let L := ContinuousLinearMap.inr ℝ E (X dim)
  let v : E × X dim := (x,a-z)
  let p (w : X dim) := v+L w
  have he (w : X dim) : p w = (x,a+(w-z)) := by
    change (x+0,a-z+w) = (x,a+(w-z))
    rw [add_zero]
    congr 1
    abel
  have hp : p z = (x,a) := by rw [he,sub_self,add_zero]
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    simp [L]
  have hP : ContDiffAt ℝ ∞ p z := contDiffAt_const.add L.contDiff.contDiffAt
  have hJets := LocalSmoothJetBudget.comp_of_positive_inner hP (hp.symm ▸ h) le_rfl
    (fun j hj _ => (norm_iteratedFDeriv_affine_pos_le L v z j hj).trans hL)
  simpa only [Function.comp_def,he,one_pow,mul_one] using hJets

theorem normalized_multiplier_baseAxis
    (f : X dim × X dim → ℝ) (hf : ContDiff ℝ ∞ f)
    (x z : X dim) (β : ℝ) (a : X dim) :
    (fun q : X dim × X dim => fderiv ℝ (fun w : X dim × X dim =>
      f (x+β⁻¹ • w.1,z+w.2)) q (a,0)) =
      fun q => β⁻¹ • fderiv ℝ f (x+β⁻¹ • q.1,z+q.2) (a,0) := by
  let L : X dim × X dim →L[ℝ] X dim × X dim :=
    (β⁻¹ • ContinuousLinearMap.fst ℝ (X dim) (X dim)).prod (ContinuousLinearMap.snd ℝ (X dim) (X dim))
  let g (q : X dim × X dim) := (x,z)+L q
  have hg (q : X dim × X dim) : g q = (x+β⁻¹ • q.1,z+q.2) := rfl
  funext q
  change fderiv ℝ (f ∘ g) q (a,0) = _
  rw [((hf.differentiable (by simp) (g q)).hasFDerivAt.comp q
    (L.hasFDerivAt.const_add (x,z))).fderiv,ContinuousLinearMap.comp_apply,hg]
  change fderiv ℝ f (x+β⁻¹ • q.1,z+q.2) (β⁻¹ • a,0) = _
  rw [show (β⁻¹ • a,(0:X dim)) = β⁻¹ • (a,(0:X dim)) by simp]
  exact map_smul _ _ _

theorem supportedSphereMultiplier_bounds_of_normalized_jets (hn : 3 ≤ dim)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f, B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f))
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (hY : IsOpen Y) (x : X dim) (hx : x ∈ Y) (β : ℝ), 0 < β →
      ∀ (m : ∀ y ∈ Y,SmoothData dim)
        (hF : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m))
        (f : X dim × X dim → ℝ) (hf : ContDiff ℝ ∞ f),
        (∀ z ∈ standardSphere dim,∀ᶠ y in 𝓝 x,∀ hy : y ∈ Y,f (y,z) = (m y hy).1 z) →
        (∀ z ∈ closedBall (0:X dim) 1,LocalSmoothJetBudget
          (fun q : X dim × X dim => f (x+β⁻¹ • q.1,z+q.2)) 0 4 C) →
        SmoothSupportedTraceCoefficientBounds hn B hY x β 0 D (supportedSphereMultiplierFamily m) hF := by
  let U := smoothTraceMultiplierJetConstant dim (6*C)
  let R := smoothTraceMultiplierJetConstant dim (8*(6*C))
  let V := 64*(6*C)
  let V₁ := smoothTraceRotationLiftConstant dim V V
  let V₂ := smoothTraceRotationLiftConstant dim V₁ V₁
  let J := 2*(dim:ℝ)^4*(V+V₁+V₂)
  let D := U+R+J
  have hU := smoothTraceMultiplierJetConstant_nonneg (dim:=dim) (6*C) (by positivity)
  have hR := smoothTraceMultiplierJetConstant_nonneg (dim:=dim) (8*(6*C)) (by positivity)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hV₁ : 0 ≤ V₁ := Real.sqrt_nonneg _
  have hV₂ : 0 ≤ V₂ := Real.sqrt_nonneg _
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  refine ⟨D,by dsimp only [D]; positivity,?_⟩
  intro hY x hx β hβ m hF f hf hRep hJets
  let F := supportedSphereMultiplierFamily m
  let M : SmoothData dim := ⟨fun z => f (x,z), hf.comp (contDiff_const.prodMk contDiff_id)⟩
  have hM : F x = smoothSphereTraceMul M := by
    ext u : 1
    apply Subtype.ext
    funext z
    simp only [F,supportedSphereMultiplierFamily,dite_eq_left hx,smoothSphereTraceMul_apply,M]
    rw [(hRep z.1 z.2).self_of_nhds hx]
  constructor
  · change SmoothTraceCommutatorBounds hn B 0 D (F x)
    rw [hM]
    have hSlice (z : X dim) (hz : z ∈ closedBall (0:X dim) 1) :
        LocalSmoothJetBudget M.1 z 3 (6*C) := by
      have hh := localSmoothJetBudget_angular_slice _ (0:X dim) 0 z ((hJets z hz).mono_order (show 3 ≤ 4 by decide))
      simpa [M,smul_zero,add_zero,zero_add,add_sub_cancel,Nat.factorial] using hh
    exact smoothTraceMultiplier_commutatorBounds_of_jets hn B hB hFin M (6*C) (by positivity) hSlice
  · intro a ha
    let g : SmoothData dim :=
      ⟨fun z => fderiv ℝ (fun y => f (y,z)) x a, by
        have hE : (fun z => fderiv ℝ (fun y => f (y,z)) x a) =
            fun z => fderiv ℝ f (x,z) (a,0) := by
          funext z
          exact congrArg (fun L : X dim →L[ℝ] ℝ => L a)
            ((hf.differentiable (by simp) (x,z)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x z)).fderiv
        rw [hE]
        exact (((hf.fderiv_right (m:=∞) (by simp)).comp (contDiff_const.prodMk contDiff_id)).clm_apply
          contDiff_const)⟩
    let g₀ : SmoothData dim := ⟨fun z => β⁻¹*g.1 z,contDiff_const.mul g.2⟩
    rw [supportedSphereMultiplierFamily_derivative_eq hY m hF hx a f
      (fun _ _ => hf.contDiffAt) hRep g (fun _ _ => rfl)]
    have hS (z : X dim) (hz : z ∈ closedBall (0:X dim) 1) :
        LocalSmoothJetBudget g₀.1 z 3 (6*C) := by
      have hBase := (hJets z hz).base_axis a ha
      rw [normalized_multiplier_baseAxis f hf x z β a] at hBase
      have hSlice := localSmoothJetBudget_angular_slice _ (0:X dim) 0 z hBase
      have hEq : (fun w => β⁻¹ • fderiv ℝ f
          (x+β⁻¹ • (0 : X dim),z+((0:X dim)+(w-z))) (a,0)) = g₀.1 := by
        funext w
        dsimp only [g₀,g]
        rw [smul_zero,add_zero,zero_add,add_sub_cancel]
        have hD : fderiv ℝ (fun y => f (y,w)) x =
            (fderiv ℝ f (x,w)).comp (ContinuousLinearMap.inl ℝ (X dim) (X dim)) :=
          ((hf.differentiable (by simp) (x,w)).hasFDerivAt.comp x
            (hasFDerivAt_prodMk_left x w)).fderiv
        rw [hD]
        rfl
      rw [hEq] at hSlice
      simpa [Nat.factorial] using hSlice
    have hEq : smoothSphereTraceMul g = β • smoothSphereTraceMul g₀ := by
      ext u : 1
      apply Subtype.ext
      funext z
      simp only [LinearMap.smul_apply,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,smoothSphereTraceMul_apply,g₀]
      field_simp [hβ.ne']
    rw [hEq]
    have h := (smoothTraceMultiplier_angularBound_of_jets hn g₀ (6*C) (by positivity)
      (fun z hz => (hS z hz).mono_order (by decide))).const_smul β
    refine h.enlarge ?_
    rw [abs_of_pos hβ,mul_comm β]
    exact mul_le_mul_of_nonneg_right (show U ≤ D by dsimp only [D]; linarith) hβ.le

end CalderonN
