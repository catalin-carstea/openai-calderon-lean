module

public import Proof.CalderonN.SmoothSupportedFiberRotationDerivative
public import Proof.CalderonN.SupportedSphereMultiplierDerivative

import Mathlib.Tactic

/-! Higher base derivatives on the smooth trace core are tested by
ordinary derivatives of their scalar matrix elements. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

abbrev RegularTraceFiberFamily (Y : Set (X dim)) :=
  {F : X dim → Module.End ℝ (SmoothSphereTrace dim) // SmoothSupportedTraceFiberRegular Y F}

namespace RegularTraceFiberFamily

@[expose] def derivative (hY : IsOpen Y) (a : X dim) (F : RegularTraceFiberFamily Y) :
    RegularTraceFiberFamily Y :=
  ⟨smoothSupportedTraceFiberDerivative hY F.1 F.2 a,
    smoothSupportedTraceFiberDerivative_regular hY F.1 F.2 a⟩

@[expose] def iteratedDerivative (hY : IsOpen Y) (F : RegularTraceFiberFamily Y) :
    (n : ℕ) → (Fin n → X dim) → RegularTraceFiberFamily Y
  | 0, _ => F
  | n+1, a => derivative hY (a 0) (iteratedDerivative hY F n (Fin.tail a))

@[expose] def rotationComm (hY : IsOpen Y) (F : RegularTraceFiberFamily Y) (i j : I dim) :
    RegularTraceFiberFamily Y :=
  ⟨supportedFiberRotationComm F.1 i j,supportedFiberRotationComm_regular hY F.1 F.2 i j⟩

theorem iteratedDerivative_matrixElement (hn : 3 ≤ dim) (hY : IsOpen Y)
    (F : RegularTraceFiberFamily Y) (u v : SmoothSphereTrace dim) (n : ℕ)
    (a : Fin n → X dim) {x : X dim} (hx : x ∈ Y) :
    iteratedFDeriv ℝ n (fun y => ⟪smoothSphereTraceL2 hn (F.1 y u),smoothSphereTraceL2 hn v⟫_ℝ) x a =
      ⟪smoothSphereTraceL2 hn ((F.iteratedDerivative hY n a).1 x u),smoothSphereTraceL2 hn v⟫_ℝ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    let p (y : X dim) := ⟪smoothSphereTraceL2 hn (F.1 y u),smoothSphereTraceL2 hn v⟫_ℝ
    let G := F.iteratedDerivative hY n (Fin.tail a)
    have hp : DifferentiableAt ℝ (iteratedFDeriv ℝ n p) x :=
      ((contDiffAt_smoothTrace_fiber_matrix_element hn hY hx F.1 F.2 u v).iteratedFDeriv_right
        (m:=∞) (by simp)).differentiableAt (by simp)
    have he : (fun y => iteratedFDeriv ℝ n p y (Fin.tail a)) =ᶠ[𝓝 x]
        fun y => ⟪smoothSphereTraceL2 hn (G.1 y u),smoothSphereTraceL2 hn v⟫_ℝ := by
      filter_upwards [hY.mem_nhds hx] with y hy
      exact ih (Fin.tail a) hy
    change iteratedFDeriv ℝ (n+1) p x a = _
    rw [hp.iteratedFDeriv_succ_apply_left',he.fderiv_eq,fderiv_smoothTrace_fiber_matrix_element hn hY hx]
    rfl

theorem iteratedDerivative_symmetric (hn : 3 ≤ dim) (hY : IsOpen Y)
    (F : RegularTraceFiberFamily Y) (hF : ∀ x ∈ Y,SmoothTraceAdjoint hn (F.1 x) (F.1 x))
    (n : ℕ) (a : Fin n → X dim) {x : X dim} (hx : x ∈ Y) :
    SmoothTraceAdjoint hn ((F.iteratedDerivative hY n a).1 x) ((F.iteratedDerivative hY n a).1 x) := by
  induction n generalizing x with
  | zero => exact hF x hx
  | succ n ih =>
    let G := F.iteratedDerivative hY n (Fin.tail a)
    exact smoothSupportedTraceFiberDerivative_symmetric hn hY G.1 G.2 (fun y hy => ih _ hy) (a 0) hx

theorem iteratedDerivative_rotationComm (hn : 3 ≤ dim) (hY : IsOpen Y)
    (F : RegularTraceFiberFamily Y) (i j : I dim) (n : ℕ) (a : Fin n → X dim)
    {x : X dim} (hx : x ∈ Y) :
    ((F.rotationComm hY i j).iteratedDerivative hY n a).1 x =
      ((F.iteratedDerivative hY n a).rotationComm hY i j).1 x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    let F₀ := (F.rotationComm hY i j).iteratedDerivative hY n (Fin.tail a)
    let F₁ := F.iteratedDerivative hY n (Fin.tail a)
    let F₂ := F₁.rotationComm hY i j
    have he : F₀.1 =ᶠ[𝓝 x] F₂.1 := by
      filter_upwards [hY.mem_nhds hx] with y hy
      exact ih (Fin.tail a) hy
    change smoothSupportedTraceFiberDerivative hY F₀.1 F₀.2 (a 0) x = _
    rw [smoothSupportedTraceFiberDerivative_eq_of_eventuallyEq hY F₀.2 F₂.2 (a 0) hx he]
    exact supportedFiberRotationComm_derivative hn hY F₁.1 F₁.2 i j (a 0) hx

theorem abs_iteratedDerivative_pair_of_entry (hn : 3 ≤ dim) (hY : IsOpen Y)
    {x : X dim} (hx : x ∈ Y) (F : RegularTraceFiberFamily Y) (u v : SmoothSphereTrace dim)
    (n : ℕ) (a : Fin n → X dim) (ha : ∀ i,‖a i‖ ≤ 1) (E : X dim → ℝ) (C : ℝ)
    (hE : E =ᶠ[𝓝 x] fun y => unitSphereArea dim *
      ⟪smoothSphereTraceL2 hn (F.1 y u),smoothSphereTraceL2 hn v⟫_ℝ)
    (hB : ‖iteratedFDeriv ℝ n E x‖ ≤ C) :
    |⟪smoothSphereTraceL2 hn ((F.iteratedDerivative hY n a).1 x u),smoothSphereTraceL2 hn v⟫_ℝ| ≤
      C/unitSphereArea dim := by
  have hσ : 0 < unitSphereArea dim := unitSphereArea_pos
  let p (y : X dim) := ⟪smoothSphereTraceL2 hn (F.1 y u),smoothSphereTraceL2 hn v⟫_ℝ
  have hp := (contDiffAt_smoothTrace_fiber_matrix_element hn hY hx F.1 F.2 u v).of_le
    (by simp : (n:ℕ∞ω) ≤ ∞)
  have he : iteratedFDeriv ℝ n E x a = unitSphereArea dim * iteratedFDeriv ℝ n p x a := by
    rw [(hE.iteratedFDeriv ℝ n).eq_of_nhds]
    change iteratedFDeriv ℝ n (unitSphereArea dim • p) x a = _
    rw [iteratedFDeriv_const_smul_apply hp,ContinuousMultilinearMap.smul_apply,smul_eq_mul]
  have ha' : ‖iteratedFDeriv ℝ n E x a‖ ≤ C := by
    have hProd : ∏ i,‖a i‖ ≤ 1 := Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ha i)
    exact ((iteratedFDeriv ℝ n E x).le_opNorm a).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hProd).trans hB)
  rw [Real.norm_eq_abs,he,abs_mul,abs_of_pos hσ,F.iteratedDerivative_matrixElement hn hY u v n a hx] at ha'
  exact (le_div_iff₀ hσ).mpr (by rwa [mul_comm])

end RegularTraceFiberFamily

end CalderonN
