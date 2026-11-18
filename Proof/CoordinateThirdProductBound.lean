import Proof.CoordinateThirdJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Local coordinate form of the supplied third product expansion. -/
lemma coordinate_third_mul {Y : Set X} (hY : IsOpen Y) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) {y : X} (hy : y ∈ Y) (i j k : I) :
    coordDeriv i (coordDeriv j (coordDeriv k (fun x => f x*g x))) y =
      coordDeriv i (coordDeriv j (coordDeriv k f)) y*g y+
      coordDeriv j (coordDeriv k f) y*coordDeriv i g y+
      coordDeriv i (coordDeriv k f) y*coordDeriv j g y+
      coordDeriv k f y*coordDeriv i (coordDeriv j g) y+
      coordDeriv i (coordDeriv j f) y*coordDeriv k g y+
      coordDeriv j f y*coordDeriv i (coordDeriv k g) y+
      coordDeriv i f y*coordDeriv j (coordDeriv k g) y+
      f y*coordDeriv i (coordDeriv j (coordDeriv k g)) y := by
  have hEq : coordDeriv j (coordDeriv k (fun x => f x*g x)) =ᶠ[𝓝 y]
      (fun x => coordDeriv j (coordDeriv k f) x*g x+coordDeriv k f x*coordDeriv j g x+
        coordDeriv j f x*coordDeriv k g x+f x*coordDeriv j (coordDeriv k g) x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact coordinate_second_mul hY hf hg hx j k
  have hF0 := (hf.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hG0 := (hg.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hF1 (a : I) := ((contDiffOn_coordDeriv hY hf a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hG1 (a : I) := ((contDiffOn_coordDeriv hY hg a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hF2 (a b : I) := ((contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY hf b) a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hG2 (a b : I) := ((contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY hg b) a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hSum := ((((hF2 j k).hasFDerivAt.fun_mul hG0.hasFDerivAt).fun_add
    ((hF1 k).hasFDerivAt.fun_mul (hG1 j).hasFDerivAt)).fun_add
    ((hF1 j).hasFDerivAt.fun_mul (hG1 k).hasFDerivAt)).fun_add
    (hF0.hasFDerivAt.fun_mul (hG2 j k).hasFDerivAt)
  change fderiv ℝ (coordDeriv j (coordDeriv k (fun x => f x*g x))) y (axis i) = _
  rw [hEq.fderiv_eq,hSum.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,coordDeriv]
  ring

lemma abs_eight_add_le (a b c d e f g h : ℝ) :
    |a+b+c+d+e+f+g+h| ≤ |a|+|b|+|c|+|d|+|e|+|f|+|g|+|h| := by
  linarith [abs_add_le a b,abs_add_le (a+b) c,abs_add_le (a+b+c) d,
    abs_add_le (a+b+c+d) e,abs_add_le (a+b+c+d+e) f,
    abs_add_le (a+b+c+d+e+f) g,abs_add_le (a+b+c+d+e+f+g) h]

structure CoordinateScalarThreeJetBound (f : X → ℝ) (y : X) (C : ℝ) : Prop where
  value : |f y| ≤ C
  first : ∀ i : I,|coordDeriv i f y| ≤ C
  second : ∀ i j : I,|coordDeriv i (coordDeriv j f) y| ≤ C
  third : ∀ i j k : I,|coordDeriv i (coordDeriv j (coordDeriv k f)) y| ≤ C

lemma CoordinateScalarThreeJetBound.mul_third_bound {Y : Set X} (hY : IsOpen Y) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) {y : X} (hy : y ∈ Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : CoordinateScalarThreeJetBound f y A) (hG : CoordinateScalarThreeJetBound g y B) (i j k : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k (fun x => f x*g x))) y| ≤ 8*A*B := by
  have hab (u v : ℝ) (hu : |u| ≤ A) (hv : |v| ≤ B) : |u*v| ≤ A*B := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) hA
  rw [coordinate_third_mul hY hf hg hy i j k]
  have h1 := hab _ _ (hF.third i j k) hG.value
  have h2 := hab _ _ (hF.second j k) (hG.first i)
  have h3 := hab _ _ (hF.second i k) (hG.first j)
  have h4 := hab _ _ (hF.first k) (hG.second i j)
  have h5 := hab _ _ (hF.second i j) (hG.first k)
  have h6 := hab _ _ (hF.first j) (hG.second i k)
  have h7 := hab _ _ (hF.first i) (hG.second j k)
  have h8 := hab _ _ hF.value (hG.third i j k)
  exact (abs_eight_add_le _ _ _ _ _ _ _ _).trans (by linarith)

end ShrinkingSpheres
