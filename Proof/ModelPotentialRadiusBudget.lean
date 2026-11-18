import Proof.FrameLogRadiusComponentBound
import Proof.ScaledFrameLogRadius
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma Admissible.radius_frame_logRadius_product_small {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) (i j : I) :
    |d.radius y*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)*
      fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)| ≤ ε := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hI := frame_logRadius_component_bound d.γ d.frame d.radius y hFrame i
  have hJ := frame_logRadius_component_bound d.γ d.frame d.radius y hFrame j
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 0 ≤ beta d.γ d.radius y := Real.sqrt_nonneg _
  rw [abs_mul,abs_mul,abs_of_pos hr]
  calc
    _ ≤ (d.radius y*beta d.γ d.radius y)*beta d.γ d.radius y :=
      mul_le_mul (mul_le_mul_of_nonneg_left hI hr.le) hJ (abs_nonneg _) (mul_nonneg hr.le hβ)
    _ = d.radius y*(beta d.γ d.radius y)^2 := by ring
    _ ≤ ε := (hd.2.2.2.2.2 y hy).2

/-- Reuse the already checked full covariant log-radius coefficient budget;
subtract its weighted quadratic-gradient term to isolate the SAME Hessian. -/
lemma Admissible.radius_frame_logRadius_hessian_small {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) (i j : I) :
    |d.radius y*hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j)| ≤
      (|Cj 2|+2)*ε := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have he := fun k => (hd.1.2.2.2.2.2.2.1 k).mono hSub
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hCombined := hd.scaledFrameLogRadiusCovariant_frame_bound hY hy i j
  rw [scaledFrameLogRadiusCovariant_eq hY d.γ hd.2.2.2.2.1.1 he hy hr hFrame] at hCombined
  have hProduct := hd.radius_frame_logRadius_product_small hy i j
  let H := hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j)
  let fi := fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)
  let fj := fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)
  have hAlg : d.radius y*H=d.radius y*(H+fi*fj)-d.radius y*fi*fj := by ring
  calc
    _ = |d.radius y*H| := rfl
    _ ≤ |d.radius y*(H+fi*fj)|+|d.radius y*fi*fj| := by rw [hAlg];exact abs_sub _ _
    _ ≤ (|Cj 2|+1)*ε+ε := add_le_add hCombined hProduct
    _ = _ := by ring
end ShrinkingSpheres
