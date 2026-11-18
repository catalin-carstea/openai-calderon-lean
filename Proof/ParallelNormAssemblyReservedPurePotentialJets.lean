import Proof.ParallelNormAssemblyReservedRadiusJets
import Proof.ParallelNormAssemblyReservedCoordinates
import Proof.CoordinateProductThreeJetAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

/-- The fixed-coordinate pure-raising potential coefficient has the
original epsilon, epsilon*beta and epsilon*beta² scalar jets. Only the
original small tensor's first TWO coordinate derivatives are used. -/
theorem uniform_pure_raising_potential_two_jet_weights {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 1 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ a b i j : I,∀ y ∈ Y,
    let p := fun x => potentialCoordinateWordCoefficient d x (.inr (.inl a)) (.inr (.inl b))
    |p y| ≤ C*ε ∧ |coordDeriv i p y| ≤ C*ε*beta d.γ d.radius y ∧
      |coordDeriv j (coordDeriv i p) y| ≤ C*ε*(beta d.γ d.radius y)^2 := by
  obtain ⟨CI,hCI,hInv⟩ := uniform_radius_inverse_two_jet_weights hY hSub hm K ρ c₀ M Cj hK
  let C := 1+3*CI
  have hC : 0 ≤ C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro floor hf ε hε d hd a b i j y hy
  dsimp only
  let β := beta d.γ d.radius y
  let r := d.radius y
  let p := fun x => potentialCoordinateWordCoefficient d x (.inr (.inl a)) (.inr (.inl b))
  let δ := fun x => (principal d.γ d.g₂ x-(d.γ x)⁻¹) a b
  let w := fun x => (d.radius x)⁻¹
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ0 := zero_le_one.trans hβ
  have hg : Elliptic Y K d.γ :=
    ⟨fun c e => (hd.1.1.1 c e).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun c e => (hd.1.2.2.1.1 c e).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hδ : ContDiffOn ℝ ∞ δ Y := by
    simpa only [δ,Matrix.sub_apply] using (contDiffOn_principal_entry hg hg2 (zero_lt_one.trans_le hK) a b).sub
      (hg.contDiffOn_inverse_entry (zero_lt_one.trans_le hK) a b)
  have hw : ContDiffOn ℝ ∞ w Y := hd.2.2.2.2.1.1.inv (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hP : p=(fun x => w x*δ x) := by
    funext x
    simp only [p,potentialCoordinateWordCoefficient,w,δ,div_eq_mul_inv]
    ring
  have hδ0 : ‖δ y‖ ≤ ε*r := by simpa only [Real.norm_eq_abs] using hd.2.2.2.2.2.component_bound hy a b
  have hδ1 (k : I) : ‖coordDeriv k δ y‖ ≤ ε*r*β := by
    have hh : |coordDeriv k δ y| ≤ ε*r := hd.2.2.2.2.2.coordinate_component_bound hy k a b
    exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ (mul_nonneg hε hr.le))
  have hδ2 : ‖coordDeriv j (coordDeriv i δ) y‖ ≤ ε*r*β^2 := by
    have hh : |coordDeriv j (coordDeriv i δ) y| ≤ ε*r :=
      hd.2.2.2.2.2.coordinate_second_component_bound hY hg hg2 (zero_lt_one.trans_le hK) hy j i a b
    have hβ2 : 1 ≤ β^2 := one_le_pow₀ hβ
    exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ2 (mul_nonneg hε hr.le))
  obtain ⟨hI1,hI2⟩ := hInv floor hf ε d hd y hy
  have hN := radius_normalized_two_jet_norms (δ y) (coordDeriv i δ y) (coordDeriv j δ y)
    (coordDeriv j (coordDeriv i δ) y) (w y) (coordDeriv i w y) (coordDeriv j w y)
    (coordDeriv j (coordDeriv i w) y) ε ε ε CI r β hε hε hε hCI hr hβ0
    (by change |r⁻¹| ≤ r⁻¹;rw [abs_of_pos (inv_pos.mpr hr)]) (hI1 i) (hI1 j) (hI2 j i) hδ0 (hδ1 i) (hδ1 j) hδ2
  simp only [Real.norm_eq_abs,smul_eq_mul] at hN
  have hD1 : coordDeriv i p y=w y*coordDeriv i δ y+coordDeriv i w y*δ y := by
    rw [hP,coordinate_mul hY hw hδ hy i]
    ring
  have hD2 : coordDeriv j (coordDeriv i p) y=
      (w y*coordDeriv j (coordDeriv i δ) y+coordDeriv j w y*coordDeriv i δ y)+
      (coordDeriv i w y*coordDeriv j δ y+coordDeriv j (coordDeriv i w) y*δ y) := by
    rw [hP,coordinate_second_mul hY hw hδ hy j i]
    ring
  have h0 : |p y| ≤ ε := by
    rw [hP]
    exact hN.1
  have h1 : |coordDeriv i p y| ≤ (1+CI)*ε*β := by
    rw [hD1]
    convert hN.2.1 using 1 <;> ring
  have h2 : |coordDeriv j (coordDeriv i p) y| ≤ C*ε*β^2 := by
    rw [hD2]
    convert hN.2.2 using 1 <;> dsimp only [C] <;> ring
  refine ⟨h0.trans ?_,h1.trans ?_,h2⟩
  · have h1C : 1 ≤ C := by dsimp only [C];linarith only [hCI]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h1C hε
  · have h1C : 1+CI ≤ C := by dsimp only [C];linarith only [hCI]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1C hε) hβ0

end ShrinkingSpheres.ParallelEnergy
