import Proof.ProfileLogThirdJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def profileRadiusThirdBudget (K G DG C2 C3 : ℝ) : ℝ :=
  K^3+3*K*(9*K^2*|C2|+3*G*K)+profileLogThirdBudget K G DG C2 C3

lemma profileRadiusThirdBudget_nonneg (K G DG C2 C3 : ℝ) (hK : 0 ≤ K) (hG : 0 ≤ G) (hDG : 0 ≤ DG) :
    0 ≤ profileRadiusThirdBudget K G DG C2 C3 := by
  have hL := profileLogThirdBudget_nonneg K G DG C2 C3 hK hG hDG
  unfold profileRadiusThirdBudget
  positivity

lemma Profile.coordinate_radius_third_identity {Y : Set X} (hY : IsOpen Y) {g : MetricField} {e : Frame}
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : X} (hy : y ∈ Y) (i j k : I) :
    let f := fun x => Real.log (r x)
    coordDeriv i (coordDeriv j (coordDeriv k r)) y = r y*
      (coordDeriv i f y*coordDeriv j f y*coordDeriv k f y+
        coordDeriv i f y*coordDeriv j (coordDeriv k f) y+
        coordDeriv i (coordDeriv j f) y*coordDeriv k f y+
        coordDeriv j f y*coordDeriv i (coordDeriv k f) y+
        coordDeriv i (coordDeriv j (coordDeriv k f)) y) := by
  let f := fun x => Real.log (r x)
  have hf : ContDiffOn ℝ ∞ f Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hD1 (a : I) := ((contDiffOn_coordDeriv hY hf a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hD2 (a b : I) := ((contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY hf b) a).contDiffAt
    (hY.mem_nhds hy)).differentiableAt (by simp)
  have hR := (hp.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hEq : coordDeriv j (coordDeriv k r) =ᶠ[𝓝 y]
      (fun x => r x*(coordDeriv j f x*coordDeriv k f x+coordDeriv j (coordDeriv k f) x)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hp.coordinate_radius_second_identity hY hx j k
  have hProduct := hR.hasFDerivAt.fun_mul
    (((hD1 j).hasFDerivAt.fun_mul (hD1 k).hasFDerivAt).fun_add (hD2 j k).hasFDerivAt)
  have hDer : coordDeriv i (coordDeriv j (coordDeriv k r)) y =
      coordDeriv i r y*(coordDeriv j f y*coordDeriv k f y+coordDeriv j (coordDeriv k f) y)+
      r y*(coordDeriv i (coordDeriv j f) y*coordDeriv k f y+
        coordDeriv j f y*coordDeriv i (coordDeriv k f) y+
        coordDeriv i (coordDeriv j (coordDeriv k f)) y) := by
    change fderiv ℝ (coordDeriv j (coordDeriv k r)) y (axis i) = _
    rw [hEq.fderiv_eq,hProduct.fderiv]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,coordDeriv]
    ring
  dsimp only
  rw [hDer,hp.coordinate_radius_first_identity hY hy i]
  ring

/-- The third coordinate radius derivative has its true r*beta^3 weight,
for every profile admitted by the frozen statement. -/
theorem Profile.coordinate_radius_third_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    (G DG : ℝ) (hG : 0 ≤ G) (hDG : 0 ≤ DG) {y : X} (hy : y ∈ Y)
    (hΓ : ∀ a b c : I,|christoffel g y a b c| ≤ G)
    (hDΓ : ∀ a b c d : I,|coordDeriv a (fun x => christoffel g x b c d) y| ≤ DG)
    (i j k : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k r)) y| ≤
      profileRadiusThirdBudget K G DG (Cj 2) (Cj 3)*r y*(beta g r y)^3 := by
  let f := fun x => Real.log (r x)
  let β := beta g r y
  let L2 := 9*K^2*|Cj 2|+3*G*K
  let L3 := profileLogThirdBudget K G DG (Cj 2) (Cj 3)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hL2 : 0 ≤ L2 := by dsimp [L2];positivity
  have hR := (hp.2 y hy).1
  have hD1 (a : I) : |coordDeriv a f y| ≤ K*β := h.coord_logRadius_bound hK e r hy (hframe y hy) a
  have hD2 (a b : I) : |coordDeriv a (coordDeriv b f) y| ≤ L2*β^2 :=
    hp.coordinate_log_second_bound h hK e hframe hf hG hy hΓ a b
  have hD3 : |coordDeriv i (coordDeriv j (coordDeriv k f)) y| ≤ L3*β^3 :=
    hp.coordinate_log_third_bound hY h hK e hframe hf G DG hG hDG hy hΓ hDΓ i j k
  have hP0 : |coordDeriv i f y*coordDeriv j f y*coordDeriv k f y| ≤ K^3*β^3 := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ (K*β)*(K*β)*(K*β) := by gcongr <;> exact hD1 _
      _ = _ := by ring
  have hP1 : |coordDeriv i f y*coordDeriv j (coordDeriv k f) y| ≤ K*L2*β^3 := by
    rw [abs_mul]
    exact (mul_le_mul (hD1 i) (hD2 j k) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hP2 : |coordDeriv i (coordDeriv j f) y*coordDeriv k f y| ≤ K*L2*β^3 := by
    rw [abs_mul]
    exact (mul_le_mul (hD2 i j) (hD1 k) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hP3 : |coordDeriv j f y*coordDeriv i (coordDeriv k f) y| ≤ K*L2*β^3 := by
    rw [abs_mul]
    exact (mul_le_mul (hD1 j) (hD2 i k) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hSum : |coordDeriv i f y*coordDeriv j f y*coordDeriv k f y+
        coordDeriv i f y*coordDeriv j (coordDeriv k f) y+
        coordDeriv i (coordDeriv j f) y*coordDeriv k f y+
        coordDeriv j f y*coordDeriv i (coordDeriv k f) y+
        coordDeriv i (coordDeriv j (coordDeriv k f)) y| ≤ (K^3+3*K*L2+L3)*β^3 := by
    have hAbs := (abs_add_le
      (coordDeriv i f y*coordDeriv j f y*coordDeriv k f y+
        coordDeriv i f y*coordDeriv j (coordDeriv k f) y+
        coordDeriv i (coordDeriv j f) y*coordDeriv k f y+
        coordDeriv j f y*coordDeriv i (coordDeriv k f) y)
      (coordDeriv i (coordDeriv j (coordDeriv k f)) y)).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    exact hAbs.trans ((add_le_add (add_le_add (add_le_add (add_le_add hP0 hP1) hP2) hP3) hD3).trans_eq (by ring))
  rw [hp.coordinate_radius_third_identity hY hy i j k,abs_mul,abs_of_pos hR]
  exact (mul_le_mul_of_nonneg_left hSum hR.le).trans_eq (by dsimp only [profileRadiusThirdBudget,L2,L3];ring)

end ShrinkingSpheres
