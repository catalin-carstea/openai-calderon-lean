import Proof.PrincipalCoefficientWeights
import Proof.Archive.PrincipalCommutator
import Proof.PrincipalAdjointBudgetDefinitions
import Proof.NormalGeodesicBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.PrincipalCommutator

def principalModelRaisingCoordinateWeight (d : Data) (a b : I) (x : X) : ℝ :=
  2*((principal d.γ d.g₂ x-(d.γ x)⁻¹) a b)

lemma Admissible.contDiffOn_principalModelRaisingCoordinateWeight {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (a b : I) :
    ContDiffOn ℝ ∞ (principalModelRaisingCoordinateWeight d a b) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ := ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  exact contDiffOn_const.mul ((contDiffOn_principal_entry hg hg2 hK a b).sub (hg.contDiffOn_inverse_entry hK a b))

/-- The original zeroth and first h-smallness assumptions provide the
    actual fixed-coordinate raising weights. -/
theorem Admissible.principalModelRaisingCoordinateWeight_bounds {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (a b i : I) :
    |principalModelRaisingCoordinateWeight d a b y| ≤ 2*ε/beta d.γ d.radius y ∧
      |directionalFDeriv (axis i) (principalModelRaisingCoordinateWeight d a b) y| ≤ 2*ε := by
  have hK0 := zero_lt_one.trans_le hK
  have hp := hd.2.2.2.2.1.2 y hy
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans hp.2.1
  have hβP : 0 < beta d.γ d.radius y := zero_lt_one.trans_le hβ
  have hR := radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hp.1.le hf hp.2.1
    (hd.2.2.2.2.2 y hy).2
  have hrβ : d.radius y*beta d.γ d.radius y ≤ 1 := hR.2.1.trans ((div_le_self hε hf).trans hε1)
  have hrβ' : d.radius y ≤ 1/beta d.γ d.radius y := (le_div_iff₀ hβP).mpr hrβ
  have hr1 : d.radius y ≤ 1 := hR.2.2.trans hε1
  have h0 := hd.2.2.2.2.2.component_bound hy a b
  have h1 := hd.2.2.2.2.2.coordinate_component_bound hy i a b
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun j k => (hd.1.1.1 j k).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ := ⟨fun j k => (hd.1.2.2.1.1 j k).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hδ : DifferentiableAt ℝ (fun x => (principal d.γ d.g₂ x-(d.γ x)⁻¹) a b) y :=
    (((contDiffOn_principal_entry hg hg2 hK0 a b).sub (hg.contDiffOn_inverse_entry hK0 a b)).contDiffAt
      (hY.mem_nhds hy)).differentiableAt (by simp)
  have hDer : directionalFDeriv (axis i) (principalModelRaisingCoordinateWeight d a b) y=
      2*coordDeriv i (fun x => (principal d.γ d.g₂ x-(d.γ x)⁻¹) a b) y := by
    unfold directionalFDeriv principalModelRaisingCoordinateWeight coordDeriv
    rw [(hδ.hasFDerivAt.const_mul 2).fderiv]
    rfl
  refine ⟨?_,?_⟩
  · unfold principalModelRaisingCoordinateWeight
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _ ≤ 2*(ε*d.radius y) := mul_le_mul_of_nonneg_left h0 (by norm_num)
      _ = (2*ε)*d.radius y := by ring
      _ ≤ (2*ε)*(1/beta d.γ d.radius y) := mul_le_mul_of_nonneg_left hrβ' (by positivity)
      _ = _ := by ring
  · rw [hDer,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _ ≤ 2*(ε*d.radius y) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (2*ε)*d.radius y := by ring
      _ ≤ (2*ε)*1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
      _ = _ := mul_one _
end ShrinkingSpheres
