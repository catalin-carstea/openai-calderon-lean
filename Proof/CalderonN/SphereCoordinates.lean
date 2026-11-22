module

public import Proof.CalderonN.Chart

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The unit direction in the fixed Euclidean coordinate sphere. -/
@[expose] def sphereDirection (v : (X dim)) : ↥(sphere (0 : X dim) 1) :=
  if h : v ≠ 0 then
    (homeomorphUnitSphereProd (X dim) ⟨v,by simpa using h⟩).1
  else ⟨axis (0 : I dim), by simp [axis, Metric.mem_sphere]⟩

theorem sphereDirection_val {v : (X dim)} (hv : v ≠ 0) :
    (sphereDirection v : (X dim)) = ‖v‖⁻¹ • v := by
  simp [sphereDirection,hv,homeomorphUnitSphereProd_apply_fst_coe]

theorem sphereDirection_pos_smul {v : (X dim)} (hv : ‖v‖ = 1) {s : ℝ} (hs : 0 < s) :
    (sphereDirection (s • v) : (X dim)) = v := by
  rw [sphereDirection_val (smul_ne_zero hs.ne' (norm_ne_zero_iff.mp (by simp [hv]))),
    norm_smul,Real.norm_eq_abs,abs_of_pos hs,hv,mul_one,inv_smul_smul₀ hs.ne']

theorem continuousOn_sphereDirection : ContinuousOn sphereDirection ({0}ᶜ : Set (X dim)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine (homeomorphUnitSphereProd (X dim)).continuous.fst.congr fun v => ?_
  have hv : (v : (X dim)) ≠ 0 := fun h => v.property (mem_singleton_iff.mpr h)
  simp [sphereDirection,hv]

end CalderonN
