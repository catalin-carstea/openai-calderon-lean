module

public import Proof.CalderonN.SmoothSupportedFiberJetBounds
public import Proof.CalderonN.LocalSmoothJetBudget

import Proof.CalderonN.ActualConormalCoefficientBounds
import Mathlib.Tactic

/-! Operations on the regular coefficient families and their local
angular bounds for ordinary base derivatives. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff InnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

namespace RegularTraceFiberFamily

@[expose] def action (hY : IsOpen Y) (F : RegularTraceFiberFamily Y) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  smoothSupportedTraceFiberAction hY F.1 F.2

@[simp] theorem action_fiber (hY : IsOpen Y) (F : RegularTraceFiberFamily Y)
    (u : SmoothSupportedTraceSection Y) (x : X dim) :
    smoothSupportedTraceFiberL x (F.action hY u) = F.1 x (smoothSupportedTraceFiberL x u) :=
  smoothSupportedTraceFiberAction_fiber hY F.1 F.2 u x

theorem action_add (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y) :
    (F.add G).action hY = F.action hY+G.action hY :=
  smoothSupportedTraceFiberAction_add hY F.1 G.1 F.2 G.2

theorem action_sub (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y) :
    (F.sub G).action hY = F.action hY-G.action hY := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [action_fiber,sub,LinearMap.sub_apply,map_sub]

theorem action_mul (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y) :
    (F.mul hY G).action hY = F.action hY*G.action hY :=
  smoothSupportedTraceFiberAction_mul hY F.1 G.1 F.2 G.2

theorem action_congr (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y) (he : EqOn F.1 G.1 Y) :
    F.action hY = G.action hY := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  simp only [action_fiber,he hx]

theorem action_derivative (hY : IsOpen Y) (F : RegularTraceFiberFamily Y) (a : X dim) :
    (F.derivative hY a).action hY =
      smoothSupportedTraceBaseDiff a*F.action hY-F.action hY*smoothSupportedTraceBaseDiff a := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  rw [action_fiber]
  exact smoothSupportedTraceFiberDerivative_apply hY F.1 F.2 a hx u

@[expose] def scalar (hY : IsOpen Y) (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y) :
    RegularTraceFiberFamily Y :=
  ⟨fun y => f y • (1 : Module.End ℝ (SmoothSphereTrace dim)),smoothSupportedTraceFiberRegular_smul hY hf⟩

@[simp] theorem action_scalar (hY : IsOpen Y) (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y) :
    (scalar hY f hf).action hY = smoothSupportedTraceBaseMul hY f hf := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [action_fiber,scalar,smoothSupportedTraceBaseMul_fiber,LinearMap.smul_apply,Module.End.one_apply]

@[expose] def finiteSum {ι : Type*} (s : Finset ι) (F : ι → RegularTraceFiberFamily Y) :
    RegularTraceFiberFamily Y :=
  ⟨fun y => ∑ i ∈ s,(F i).1 y,SmoothSupportedTraceFiberRegular.sum s _ (fun i _ => (F i).2)⟩

theorem action_finiteSum {ι : Type*} (hY : IsOpen Y) (s : Finset ι) (F : ι → RegularTraceFiberFamily Y) :
    (finiteSum s F).action hY = ∑ i ∈ s,(F i).action hY := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [action_fiber,finiteSum,LinearMap.sum_apply,map_sum]

private theorem eq_of_all_matrixElements (hn : 3 ≤ dim) {S T : Module.End ℝ (SmoothSphereTrace dim)}
    (h : ∀ u v,⟪smoothSphereTraceL2 hn (S u),smoothSphereTraceL2 hn v⟫_ℝ =
      ⟪smoothSphereTraceL2 hn (T u),smoothSphereTraceL2 hn v⟫_ℝ) : S = T := by
  ext u : 1
  apply smoothSphereTraceL2_injective hn
  have h' := h u (S u-T u)
  rw [map_sub] at h'
  have h'' := sub_eq_zero.mpr h'
  rw [← inner_sub_left,real_inner_self_eq_norm_sq] at h''
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h''))

theorem iteratedDerivative_constFamily (hn : 3 ≤ dim) (hY : IsOpen Y)
    (T : Module.End ℝ (SmoothSphereTrace dim)) (hT : SmoothSupportedTraceFiberRegular Y (fun _ => T))
    (n : ℕ) (a : Fin (n+1) → X dim) {x : X dim} (hx : x ∈ Y) :
    (iteratedDerivative hY (⟨_,hT⟩ : RegularTraceFiberFamily Y) (n+1) a).1 x = 0 := by
  apply eq_of_all_matrixElements hn
  intro u v
  rw [← iteratedDerivative_matrixElement hn hY _ u v (n+1) a hx]
  change iteratedFDeriv ℝ n.succ (fun _ : X dim =>
    ⟪smoothSphereTraceL2 hn (T u),smoothSphereTraceL2 hn v⟫_ℝ) x a = _
  rw [iteratedFDeriv_succ_const]
  simp only [Pi.zero_apply,ContinuousMultilinearMap.zero_apply,LinearMap.zero_apply,map_zero,inner_zero_left]

theorem iteratedDerivative_scalar (hn : 3 ≤ dim) (hY : IsOpen Y)
    (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y) (n : ℕ) (a : Fin n → X dim)
    {x : X dim} (hx : x ∈ Y) :
    ((scalar hY f hf).iteratedDerivative hY n a).1 x = iteratedFDeriv ℝ n f x a • 1 := by
  apply eq_of_all_matrixElements hn
  intro u v
  rw [← iteratedDerivative_matrixElement hn hY _ u v n a hx]
  simp only [scalar,LinearMap.smul_apply,Module.End.one_apply,map_smul,real_inner_smul_left]
  let b := ⟪smoothSphereTraceL2 hn u,smoothSphereTraceL2 hn v⟫_ℝ
  have hfa := ((hf.contDiffAt (hY.mem_nhds hx)).of_le (by simp : (n:ℕ∞ω) ≤ ∞))
  change iteratedFDeriv ℝ n (fun y => f y*b) x a = _
  rw [show (fun y => f y*b) = b • f by funext y; exact mul_comm _ _,
    iteratedFDeriv_const_smul_apply hfa,ContinuousMultilinearMap.smul_apply,smul_eq_mul,mul_comm]

theorem iteratedDerivative_paired (hn : 3 ≤ dim) (hY : IsOpen Y)
    (F G : RegularTraceFiberFamily Y) (hAdj : ∀ x ∈ Y,SmoothTraceAdjoint hn (F.1 x) (G.1 x))
    (n : ℕ) (a : Fin n → X dim) {x : X dim} (hx : x ∈ Y) :
    SmoothTraceAdjoint hn ((F.iteratedDerivative hY n a).1 x) ((G.iteratedDerivative hY n a).1 x) := by
  intro u v
  have hEq : (fun y => ⟪smoothSphereTraceL2 hn (F.1 y u),smoothSphereTraceL2 hn v⟫_ℝ) =ᶠ[𝓝 x]
      fun y => ⟪smoothSphereTraceL2 hn (G.1 y v),smoothSphereTraceL2 hn u⟫_ℝ := by
    filter_upwards [hY.mem_nhds hx] with y hy
    exact (hAdj y hy u v).trans (real_inner_comm _ _)
  rw [← iteratedDerivative_matrixElement hn hY F u v n a hx,real_inner_comm,
    ← iteratedDerivative_matrixElement hn hY G v u n a hx,(hEq.iteratedFDeriv ℝ n).eq_of_nhds]

end RegularTraceFiberFamily

namespace SmoothSupportedFiberJetBound
variable {hn : 3 ≤ dim} {hY : IsOpen Y} {x : X dim} {β C : ℝ} {N k : ℕ}
variable {F G : RegularTraceFiberFamily Y}

theorem value (h : SmoothSupportedFiberJetBound hn hY x β N k C F) :
    SmoothTraceAngularBound hn k C (F.1 x) := by
  simpa only [RegularTraceFiberFamily.iteratedDerivative,pow_zero,mul_one] using
    h 0 (Nat.zero_le N) Fin.elim0 (fun i => Fin.elim0 i)

theorem atAxis (h : SmoothSupportedFiberJetBound hn hY x β N k C F)
    (hN : 1 ≤ N) (i : I dim) :
    SmoothTraceAngularBound hn k (C*β) ((F.derivative hY (axis i)).1 x) := by
  simpa only [RegularTraceFiberFamily.iteratedDerivative,pow_one] using
    h 1 hN (fun _ => axis i) (fun _ => (norm_axis i).le)

theorem paired (h : SmoothSupportedFiberJetBound hn hY x β N k C F)
    (hx : x ∈ Y) (hβ : 0 ≤ β) (hC : 0 ≤ C) (hAdj : ∀ y ∈ Y,SmoothTraceAdjoint hn (F.1 y) (G.1 y)) :
    SmoothSupportedFiberJetBound hn hY x β N k C G :=
  fun n hnN a ha => (h n hnN a ha).adjoint (mul_nonneg hC (pow_nonneg hβ _))
    (F.iteratedDerivative_paired hn hY G hAdj n a hx)

theorem weaken (h : SmoothSupportedFiberJetBound hn hY x β N k C F)
    (hβ : 0 ≤ β) (hC : 0 ≤ C) {l : ℕ} (hkl : k ≤ l) :
    SmoothSupportedFiberJetBound hn hY x β N l C F :=
  fun n hnN a ha => (h n hnN a ha).weaken (mul_nonneg hC (pow_nonneg hβ _)) hkl

theorem constFamily {T : Module.End ℝ (SmoothSphereTrace dim)}
    (hF : SmoothSupportedTraceFiberRegular Y (fun _ => (T : Module.End ℝ (SmoothSphereTrace dim))))
    (hx : x ∈ Y) (hβ : 0 ≤ β) (hC : 0 ≤ C) (hT : SmoothTraceAngularBound hn k C T) :
    SmoothSupportedFiberJetBound hn hY x β N k C ⟨_,hF⟩ := by
  intro n hnN a ha
  cases n with
  | zero => simpa only [RegularTraceFiberFamily.iteratedDerivative,pow_zero,mul_one] using hT
  | succ n =>
    rw [RegularTraceFiberFamily.iteratedDerivative_constFamily hn hY T hF n a hx]
    exact smoothTraceAngularBound_zero hn _ (mul_nonneg hC (pow_nonneg hβ _))

theorem ofScalar (hx : x ∈ Y) (hβ : 0 ≤ β)
    (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y)
    (h : ∀ n ≤ N, ‖iteratedFDeriv ℝ n f x‖ ≤ C*β^n) :
    SmoothSupportedFiberJetBound hn hY x β N 0 C (RegularTraceFiberFamily.scalar hY f hf) := by
  intro n hnN a ha
  rw [RegularTraceFiberFamily.iteratedDerivative_scalar hn hY f hf n a hx]
  have hProd : ∏ i,‖a i‖ ≤ 1 := Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ha i)
  have hVal := ((iteratedFDeriv ℝ n f x).le_opNorm a).trans
    ((mul_le_of_le_one_right (norm_nonneg _) hProd).trans (h n hnN))
  exact (((smoothTraceIdentity_commutatorBounds hn 0).bound.const_smul
    (iteratedFDeriv ℝ n f x a)).enlarge (by simpa only [mul_one,Real.norm_eq_abs] using hVal))

end SmoothSupportedFiberJetBound

end CalderonN
