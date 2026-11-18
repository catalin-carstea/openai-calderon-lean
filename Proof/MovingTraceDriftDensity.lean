import Proof.MovingTraceDriftFiber
import Proof.RemainderAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres

theorem horizontal_fiber_density_le (g : MetricField) (e : Frame) (r : X → ℝ) (φ : Field) (y : X) :
    metricDensity g y*(∑ i : I,fiberSq e y (fun w => horizontal g φ y w (e y i))) ≤
      physicalEnergyDensity g e r φ y := by
  have hb : 0 ≤ beta g r y := Real.sqrt_nonneg _
  have hMass := mul_nonneg (sq_nonneg (beta g r y)) (sobolevSq_nonneg g e 1 y (fun w => φ (y,w)))
  have hHalf := mul_nonneg (inv_nonneg.mpr hb)
    (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sobolevSq_nonneg g e (1/2) y (fun w => horizontal g φ y w (e y i))))
  have hThree := mul_nonneg hb (sobolevSq_nonneg g e (3/2) y (fun w => φ (y,w)))
  apply mul_le_mul_of_nonneg_left (show _ ≤ _ by linarith) (show 0 ≤ metricDensity g y from Real.sqrt_nonneg _)

lemma drift_density_absorption (r β floor ε ρ D H S E cH cA : ℝ)
    (hr : 0 ≤ r) (hf : 1 ≤ floor) (hβ : floor ≤ β) (hSmall : r*β^2 ≤ ε) (hε : ε ≤ 1)
    (hρ : 0 ≤ ρ) (hH : 0 ≤ H) (hE : 0 ≤ E) (hcH : 0 ≤ cH) (hcA : 0 ≤ cA)
    (hD : D ≤ cH*r^2*H+cA*S) (hHDensity : ρ*H ≤ E) (hSDensity : floor^2*(ρ*S) ≤ E) :
    floor^2*(ρ*D) ≤ (1+cH+cA)^2*E := by
  have hf0 : 0 ≤ floor := zero_le_one.trans hf
  have hβ0 : 0 ≤ β := hf0.trans hβ
  have hSq : floor^2 ≤ β^2 := (sq_le_sq₀ hf0 hβ0).mpr hβ
  have hRF : r*floor^2 ≤ 1 := (mul_le_mul_of_nonneg_left hSq hr).trans (hSmall.trans hε)
  have hfSq : floor ≤ floor^2 := by nlinarith only [hf,sq_nonneg (floor-1)]
  have hrF : floor*r ≤ 1 := by
    have h := (mul_le_mul_of_nonneg_left hfSq hr).trans hRF
    simpa only [mul_comm] using h
  have hrFSq : (floor*r)^2 ≤ 1 := by
    have h0 := mul_nonneg hf0 hr
    nlinarith only [hrF,h0]
  have hLeading : cH*(floor*r)^2*(ρ*H) ≤ cH*(ρ*H) := by
    have h := mul_le_mul_of_nonneg_left hrFSq (mul_nonneg hcH (mul_nonneg hρ hH))
    convert h using 1 <;> ring
  have hBoth : cH*(ρ*H)+cA*(floor^2*(ρ*S)) ≤ (cH+cA)*E := by
    exact (add_le_add (mul_le_mul_of_nonneg_left hHDensity hcH)
      (mul_le_mul_of_nonneg_left hSDensity hcA)).trans_eq (by ring)
  let C := 1+cH+cA
  have hC1 : 1 ≤ C := by dsimp only [C];linarith
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hCC : C ≤ C^2 := by
    have h := mul_le_mul_of_nonneg_left hC1 hC0
    simpa only [mul_one,pow_two] using h
  have hBudget : cH+cA ≤ C^2 := (show cH+cA ≤ C by dsimp only [C];linarith).trans hCC
  calc
    floor^2*(ρ*D) ≤ floor^2*(ρ*(cH*r^2*H+cA*S)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hρ) (sq_nonneg floor)
    _ = cH*(floor*r)^2*(ρ*H)+cA*(floor^2*(ρ*S)) := by ring
    _ ≤ cH*(ρ*H)+cA*(floor^2*(ρ*S)) := add_le_add hLeading (le_refl _)
    _ ≤ (cH+cA)*E := hBoth
    _ ≤ C^2*E := mul_le_mul_of_nonneg_right hBudget hE

def movingTraceDriftBudget (K CA : ℝ) : ℝ := 1+54*K^4+18*K^2*CA^2

/-- Uniform density estimate for direct drift absorption, with no drift
    derivatives. The exact frozen four-term energy supplies the right hand side. -/
theorem uniform_movingTraceDrift_density_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD : ℝ,0 < η ∧ 0 ≤ CD ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ φ : Field,smoothNear φ (bundle Y d.γ) →
      floor^2*(metricDensity d.γ y*fiberSq d.frame y (fun w => movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ (y,w))) ≤
        CD^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  have hTheorem := uniform_movingTraceDrift_fiber_bound hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,CA,hηF,hCA,hProduce⟩ := hTheorem
  refine ⟨min ηF 1,movingTraceDriftBudget K CA,lt_min hηF zero_lt_one,by unfold movingTraceDriftBudget;positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy φ hφ
  have hHere := hProduce floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy φ hφ
  exact drift_density_absorption (d.radius y) (beta d.γ d.radius y) floor ε (metricDensity d.γ y) _ _ _ _
    (54*K^4) (18*K^2*CA^2) (hd.2.2.2.2.1.2 y hy).1.le hf (hd.2.2.2.2.1.2 y hy).2.1
    (hd.2.2.2.2.2 y hy).2 (hSmall.trans (min_le_right _ _)) (Real.sqrt_nonneg _)
    (Finset.sum_nonneg (fun _ _ => fiberSq_nonneg _ _ _)) (physicalEnergyDensity_nonneg _ _ _ _ _)
    (by positivity) (by positivity) hHere (horizontal_fiber_density_le _ _ _ _ _)
    (hd.2.2.2.2.1.sobolev_one_density_le (zero_le_one.trans hf) φ hy)

end ShrinkingSpheres
