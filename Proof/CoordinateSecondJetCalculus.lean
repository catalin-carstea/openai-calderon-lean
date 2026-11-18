import Proof.PrincipalCoefficientWeights
import Proof.InverseMetricSecondDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma contDiffOn_coordDeriv {Y : Set X} (hY : IsOpen Y) {f : X → ℝ} (hf : ContDiffOn ℝ ∞ f Y) (i : I) :
    ContDiffOn ℝ ∞ (coordDeriv i f) Y :=
  (hf.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const

lemma coordinate_second_commute {Y : Set X} (hY : IsOpen Y) {f : X → ℝ} (hf : ContDiffOn ℝ ∞ f Y)
    {y : X} (hy : y ∈ Y) (i j : I) : coordDeriv i (coordDeriv j f) y = coordDeriv j (coordDeriv i f) y := by
  have hd := ((hf.fderiv_of_isOpen (m:=∞) hY (by simp)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  rw [coordinate_second_derivative f y hd i j,coordinate_second_derivative f y hd j i]
  exact ((hf.contDiffAt (hY.mem_nhds hy)).isSymmSndFDerivAt (by simp)).eq (axis i) (axis j)

lemma coordinate_second_sub {Y : Set X} (hY : IsOpen Y) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) {y : X} (hy : y ∈ Y) (i j : I) :
    coordDeriv i (coordDeriv j (fun x => f x-g x)) y = coordDeriv i (coordDeriv j f) y-coordDeriv i (coordDeriv j g) y := by
  have heq : coordDeriv j (fun x => f x-g x) =ᶠ[𝓝 y] (fun x => coordDeriv j f x-coordDeriv j g x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    unfold coordDeriv
    rw [fderiv_fun_sub ((hf.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
      ((hg.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))]
    rfl
  change (fderiv ℝ (coordDeriv j (fun x => f x-g x)) y) (axis i) = _
  rw [heq.fderiv_eq,fderiv_fun_sub (((contDiffOn_coordDeriv hY hf j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    (((contDiffOn_coordDeriv hY hg j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))]
  rfl

lemma coordinate_second_mul {Y : Set X} (hY : IsOpen Y) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) {y : X} (hy : y ∈ Y) (i j : I) :
    coordDeriv i (coordDeriv j (fun x => f x*g x)) y =
      coordDeriv i (coordDeriv j f) y*g y+coordDeriv j f y*coordDeriv i g y+
        coordDeriv i f y*coordDeriv j g y+f y*coordDeriv i (coordDeriv j g) y := by
  have hdf (x : X) (hx : x ∈ Y) := (hf.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  have hdg (x : X) (hx : x ∈ Y) := (hg.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  have heq : coordDeriv j (fun x => f x*g x) =ᶠ[𝓝 y] (fun x => coordDeriv j f x*g x+f x*coordDeriv j g x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    unfold coordDeriv
    rw [((hdf x hx).hasFDerivAt.fun_mul (hdg x hx).hasFDerivAt).fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  have hDfj := ((contDiffOn_coordDeriv hY hf j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hDgj := ((contDiffOn_coordDeriv hY hg j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hp := (hDfj.hasFDerivAt.fun_mul (hdg y hy).hasFDerivAt).fun_add
    ((hdf y hy).hasFDerivAt.fun_mul hDgj.hasFDerivAt)
  change (fderiv ℝ (coordDeriv j (fun x => f x*g x)) y) (axis i) = _
  rw [heq.fderiv_eq,hp.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,coordDeriv]
  ring

lemma Small.coordinate_second_component_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K) {r : X → ℝ} {ε : ℝ}
    (hs : Small Y g g₂ r ε) {y : X} (hy : y ∈ Y) (i j a b : I) :
    |coordDeriv i (coordDeriv j (fun x => (principal g g₂ x-(g x)⁻¹) a b)) y| ≤ ε*r y := by
  have hF : ContDiffOn ℝ ∞ (fun x => (principal g g₂ x-(g x)⁻¹) a b) Y := by
    simpa only [Matrix.sub_apply] using (contDiffOn_principal_entry h h₂ hK a b).sub (h.contDiffOn_inverse_entry hK a b)
  fin_cases i <;> fin_cases j
  · change |coordDeriv (0:I) (coordDeriv (0:I) _) y| ≤ ε*r y
    exact hs.partial_bound hy 2 0 0 (by decide) a b
  · change |coordDeriv (0:I) (coordDeriv (1:I) _) y| ≤ ε*r y
    exact hs.partial_bound hy 1 1 0 (by decide) a b
  · change |coordDeriv (0:I) (coordDeriv (2:I) _) y| ≤ ε*r y
    exact hs.partial_bound hy 1 0 1 (by decide) a b
  · change |coordDeriv (1:I) (coordDeriv (0:I) _) y| ≤ ε*r y
    rw [coordinate_second_commute hY hF hy 1 0]
    exact hs.partial_bound hy 1 1 0 (by decide) a b
  · change |coordDeriv (1:I) (coordDeriv (1:I) _) y| ≤ ε*r y
    exact hs.partial_bound hy 0 2 0 (by decide) a b
  · change |coordDeriv (1:I) (coordDeriv (2:I) _) y| ≤ ε*r y
    exact hs.partial_bound hy 0 1 1 (by decide) a b
  · change |coordDeriv (2:I) (coordDeriv (0:I) _) y| ≤ ε*r y
    rw [coordinate_second_commute hY hF hy 2 0]
    exact hs.partial_bound hy 1 0 1 (by decide) a b
  · change |coordDeriv (2:I) (coordDeriv (1:I) _) y| ≤ ε*r y
    rw [coordinate_second_commute hY hF hy 2 1]
    exact hs.partial_bound hy 0 1 1 (by decide) a b
  · change |coordDeriv (2:I) (coordDeriv (2:I) _) y| ≤ ε*r y
    exact hs.partial_bound hy 0 0 2 (by decide) a b

end ShrinkingSpheres
