import Proof.PrincipalModelRaisingCoordinateWeights
import Proof.CoordinateSecondJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.PrincipalCommutator

/-- The original zeroth, first and second small-tensor assumptions control
the SAME model raising coordinate weight through two ordinary derivatives. -/
theorem Admissible.principalModelRaisingCoordinateWeight_two_jet_bounds {Y Ω : Set X}
    (hY : IsOpen Y) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (a b i j : I) :
    |principalModelRaisingCoordinateWeight d a b y| ≤ 2*ε/beta d.γ d.radius y ∧
      |fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i)| ≤ 2*ε ∧
      |fderiv ℝ (fun x => fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i))
        y (axis j)| ≤ 2*ε := by
  have h01 := hd.principalModelRaisingCoordinateWeight_bounds hY hK hf hε hε1 hy a b i
  refine ⟨h01.1,h01.2,?_⟩
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hKP := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ := ⟨fun k l => (hd.1.1.1 k l).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ := ⟨fun k l => (hd.1.2.2.1.1 k l).mono hSub,
    fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  let δ := fun x => (principal d.γ d.g₂ x-(d.γ x)⁻¹) a b
  have hδ : ContDiffOn ℝ ∞ δ Y := by
    simpa only [δ,Matrix.sub_apply] using
      (contDiffOn_principal_entry hg hg2 hKP a b).sub (hg.contDiffOn_inverse_entry hKP a b)
  have hSecond : coordDeriv j (coordDeriv i (principalModelRaisingCoordinateWeight d a b)) y =
      2*coordDeriv j (coordDeriv i δ) y := by
    have hh := coordinate_second_mul hY (f:=fun _ : X => (2:ℝ)) (g:=δ)
      contDiffOn_const hδ hy j i
    have hConst (k : I) : coordDeriv k (fun _ : X => (2:ℝ)) = fun _ => (0:ℝ) := by
      funext x
      simp [coordDeriv]
    simp only [hConst] at hh
    change coordDeriv j (coordDeriv i (fun x => 2*δ x)) y = _
    simpa [coordDeriv] using hh
  have hSmall : |coordDeriv j (coordDeriv i δ) y| ≤ ε*d.radius y :=
    hd.2.2.2.2.2.coordinate_second_component_bound hY hg hg2 hKP hy j i a b
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  have hr1 : d.radius y ≤ 1 :=
    ((radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr hf
      (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2).trans hε1
  change |coordDeriv j (coordDeriv i (principalModelRaisingCoordinateWeight d a b)) y| ≤ _
  rw [hSecond,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (mul_le_mul_of_nonneg_left hSmall (by norm_num)).trans
    (by nlinarith only [mul_le_mul_of_nonneg_left hr1 hε])

end ShrinkingSpheres
