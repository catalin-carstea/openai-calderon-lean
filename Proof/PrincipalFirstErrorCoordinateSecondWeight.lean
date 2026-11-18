import Proof.PrincipalFirstErrorCoordinateWeights
import Proof.PrincipalSecondCoefficientWeight
import Proof.CoordinateScalarFirstRules

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.PrincipalCommutator

/-- The actual second ordinary derivative of the SAME coordinate weight
has the original epsilon gain, before weakening to an unweighted beta budget. -/
theorem Admissible.principalFirstErrorCoordinateWeight_second_small_bound {Y Ω : Set X}
    (hY : IsOpen Y) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (a b i j : I) :
    |fderiv ℝ (fun x => fderiv ℝ (principalFirstErrorCoordinateWeight d a b) x (axis i))
      y (axis j)| ≤ (2*principalSecondBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2))*ε := by
  let A2 := principalSecondBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  have hKP := zero_lt_one.trans_le hK
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun k l => (hd.1.1.1 k l).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ := ⟨fun k l => (hd.1.2.2.1.1 k l).mono hSub,
    fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  let f := fun (k l : I) (x : X) => d.radius x*principal d.γ d.g₂ x k l
  have hfs (k l : I) : ContDiffOn ℝ ∞ (f k l) Y :=
    hd.2.2.2.2.1.1.mul (contDiffOn_principal_entry hg hg2 hKP k l)
  have hfun : principalFirstErrorCoordinateWeight d a b = fun x => f a b x+f b a x := by
    funext x
    exact mul_add _ _ _
  have hFirst : (fun x => fderiv ℝ (principalFirstErrorCoordinateWeight d a b) x (axis i)) =ᶠ[𝓝 y]
      (fun x => coordDeriv i (f a b) x+coordDeriv i (f b a) x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    change coordDeriv i (principalFirstErrorCoordinateWeight d a b) x = _
    rw [hfun]
    exact coordDeriv_add_at _ _ (((hfs a b).contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
      (((hfs b a).contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)) i
  have hSecond : fderiv ℝ (fun x => fderiv ℝ (principalFirstErrorCoordinateWeight d a b) x (axis i))
      y (axis j) = coordDeriv j (coordDeriv i (f a b)) y+coordDeriv j (coordDeriv i (f b a)) y := by
    rw [hFirst.fderiv_eq,fderiv_fun_add
      (((contDiffOn_coordDeriv hY (hfs a b) i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((contDiffOn_coordDeriv hY (hfs b a) i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))]
    rfl
  have hEach (k l : I) : |coordDeriv j (coordDeriv i (f k l)) y| ≤ A2*ε :=
    principal_radius_second_weight hY hg hg2 hK d.frame
      (fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)) hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy
      |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (abs_nonneg _) (abs_nonneg _)
      (fun k l => (hd.1.reference_fderiv_bound (by omega) (hSub hy) k l).trans (le_abs_self _))
      (fun k l => (hd.1.reference_second_fderiv_bound hm (hSub hy) k l).trans (le_abs_self _)) k l i j
  rw [hSecond]
  calc
    _ ≤ |coordDeriv j (coordDeriv i (f a b)) y|+|coordDeriv j (coordDeriv i (f b a)) y| := abs_add_le _ _
    _ ≤ A2*ε+A2*ε := add_le_add (hEach a b) (hEach b a)
    _ = (2*A2)*ε := by ring

end ShrinkingSpheres
