module

public import Proof.CalderonN.CenterCoefficientAtOrigin
public import Proof.CalderonN.ActualConormalRadialRow
public import Proof.CalderonN.BallDilationCalculus
public import Proof.CalderonN.AngularRadialWeight

import Proof.CalderonN.ChartBilinear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! The Gauss radial-row condition is linear at a fixed unit vector.
It therefore persists in the center and relative-radius derivatives. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SphereHarmonic

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def IsRadialRow (z : X dim) (A : Mat dim) : Prop :=
  ∀ j, ∑ i, z i*A i j = scalarQuadraticCoefficient (fun _ => A) z*z j

omit [Nontrivial (Fin dim)] in
theorem isRadialRow_of_weight {z : X dim} (hz : z ∈ standardSphere dim) (A : Mat dim) (w : ℝ)
    (h : ∀ j, ∑ i, z i*A i j = w*z j) : IsRadialRow z A := by
  have hz₁ : ‖z‖ = 1 := by simpa only [standardSphere,mem_sphere,dist_zero_right] using hz
  have hN : ∑ i : I dim, z i*z i = 1 := by
    simp only [← pow_two,← EuclideanSpace.real_norm_sq_eq,hz₁,one_pow]
  have hW : scalarQuadraticCoefficient (fun _ => A) z = w := by
    rw [scalarQuadraticCoefficient,Finset.sum_comm]
    simp_rw [← Finset.sum_mul,h,mul_assoc,← Finset.mul_sum,hN,mul_one]
  intro j
  rw [hW,h j]

omit [Nontrivial (Fin dim)] in
theorem isRadialRow_of_hasDerivAt {F : ℝ → Mat dim} {G : Mat dim} {t : ℝ} {z : X dim}
    (hF : HasDerivAt F G t) (hR : ∀ᶠ s in 𝓝 t, IsRadialRow z (F s)) :
    IsRadialRow z G := by
  intro j
  let P : Mat dim →L[ℝ] ℝ := ∑ i : I dim, z i • matrixEntryL i j
  let Q : Mat dim →L[ℝ] ℝ := ∑ i : I dim, ∑ k : I dim, (z i*z k*z j) • matrixEntryL i k
  have hP (A : Mat dim) : P A = ∑ i, z i*A i j := by
    simp only [P,ContinuousLinearMap.sum_apply,smul_apply,smul_eq_mul,matrixEntryL_apply]
  have hQ (A : Mat dim) : Q A = scalarQuadraticCoefficient (fun _ => A) z*z j := by
    simp only [Q,ContinuousLinearMap.sum_apply,smul_apply,smul_eq_mul,
      matrixEntryL_apply,scalarQuadraticCoefficient,Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hSame : P ∘ F =ᶠ[𝓝 t] (Q ∘ F) := by
    filter_upwards [hR] with s hs
    exact (hP (F s)).trans ((hs j).trans (hQ (F s)).symm)
  have hDP := P.hasFDerivAt.comp_hasDerivAt t hF
  have hDQ := Q.hasFDerivAt.comp_hasDerivAt t hF
  exact (hP G).symm.trans ((hDP.unique (hDQ.congr_of_eventuallyEq hSame)).trans (hQ G))

theorem smoothBallConormal_eq_of_radialRow (A : X dim → Mat dim) (z : X dim) (u : X dim → ℝ)
    (h : IsRadialRow z (A z)) :
    smoothBallConormal A u z = scalarQuadraticCoefficient A z*fderiv ℝ u z z := by
  rw [smoothBallConormal,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct,smoothBallFlux_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  have hSum (j : I dim) : (∑ i : I dim, (A z i j*coordDeriv j u z)*z i) =
      (∑ i : I dim, z i*A z i j)*coordDeriv j u z := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hD : fderiv ℝ u z z = ∑ j : I dim, coordDeriv j u z*z j :=
    covector_axis_sum (fderiv ℝ u z) z
  rw [hD,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he := (hSum j).trans (congrArg (fun a : ℝ => a*coordDeriv j u z) (h j))
  exact he.trans (by
    change scalarQuadraticCoefficient A z*z j*coordDeriv j u z = _
    ring)

private theorem initial_velocity_mem_interior_of_sphere {Y Ω : Set (X dim)} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {y : X dim} {F : Frame dim} (he : ∀ i j, metricPair d.γ y (F y i) (F y j) = if i=j then 1 else 0)
    {s : ℝ} (hs : 0 < s) (hsρ : s < ρ) {z : X dim} (hz : z ∈ standardSphere dim) :
    s • frameVector F y z ∈ interior (disk d.γ y (max ρ (d.radius y))) := by
  apply mem_interior_disk_of_metricPair_lt
  have hz' : ‖z‖ = 1 := by simpa only [standardSphere,mem_sphere,dist_zero_right] using hz
  rw [metricPair_smul_left,metricPair_smul_right,metricPair_frameVector_self d.γ F y z he,hz']
  have hR : 0 ≤ max ρ (d.radius y) := hs.le.trans (hsρ.le.trans (le_max_left _ _))
  have hSq := (sq_lt_sq₀ hs.le hR).2 (hsρ.trans_le (le_max_left _ _))
  simpa only [one_pow,mul_one,pow_two] using hSq

theorem isRadialRow_scaledCenterCoefficientDerivative (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (a : X dim) (hrρ : d.radius y < ρ)
    {z : X dim} (hz : z ∈ standardSphere dim) :
    IsRadialRow z (actualCenterNormalCoefficientDerivative d y a (d.radius y • z)) := by
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hr := (hd.2.2.2.2.1.2 y hy).1
  let r := d.radius y
  obtain ⟨F,hF,hF₀,hFnear⟩ := hd.1.1.exists_local_center_parallelFrame hΩ hK y a hyΩ
    (d.frame y) hFrame
  let q (t : ℝ) := y+t • a
  let U (t : ℝ) := frameVectorLinear (fun _ => F t) (q t)
  let T := transportedCenterCoefficient d y a U
  have hq : Continuous q := continuous_const.add (continuous_id.smul continuous_const)
  have hq₀ : q 0 = y := by simp [q]
  have hU₀ : U 0 = frameVectorLinear d.frame y := by simp [U,hF₀,frameVectorLinear_eq_sum]
  have hUD : HasDerivAt U (parallelFrameFirstJet d y a) 0 :=
    hasDerivAt_parallelFrameOperator d y a F hF₀
      (fun i => by simpa only [zero_smul,add_zero] using hFnear.self_of_nhds.2.1 i)
  have hb := (hd.1.contDiffOn_centerInverseDensity hK).contDiffAt (hΩ.mem_nhds hyΩ)
  have hCh := hd.contDiffAt_centerChartCoefficient hΩ hK hy (r • z)
    (by rw [map_smul,frameVectorLinear_apply]
        exact interior_subset (initial_velocity_mem_interior_of_sphere hd hFrame hr hrρ hz))
  have hD := hasDerivAt_transportedCenterCoefficient d y a (r • z) U hU₀ hUD (hb.differentiableAt (by simp))
    hCh (contDiffAt_actualCenterCoefficientFamilyJet d y a (r • z) hCh)
  apply isRadialRow_of_hasDerivAt hD
  have hyN : ∀ᶠ t in 𝓝 (0:ℝ), q t ∈ Y := hq.continuousAt.eventually (hY.mem_nhds (hq₀ ▸ hy))
  filter_upwards [hyN,hFnear] with t hqt ht
  let dt : Data dim := {d with frame := fun _ => F t}
  have hVel := initial_velocity_mem_interior_of_sphere (F := dt.frame) hd ht.2.2 hr hrρ hz
  have hT : T (t,r • z) =
      firstNormalVelocityCoefficient dt (q t) (r • frameVector dt.frame (q t) z) := by
    ext i j
    rw [firstNormalVelocityCoefficient_rescaled]
    exact transportedCenterCoefficient_eq_rescaled d y a z F t r i j
  change IsRadialRow z (T (t,r • z))
  rw [hT]
  exact isRadialRow_of_weight hz _ _ fun j => actualNormalCoeff_radial_row_of_frame
    (d:=dt) hn hΩ hd.1 hd.2.1 hK hqt ht.2.2 hr.ne' z hVel j

theorem isRadialRow_ballDilationCoefficient (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : d.radius y < ρ)
    {z : X dim} (hz : z ∈ standardSphere dim) {A : X dim → Mat dim}
    (hA : ContDiff ℝ ∞ A)
    (hEq : EqOn A (fun z => firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z))
      (ball (0 : X dim) (5/4))) : IsRadialRow z (ballDilationCoefficient A z) := by
  let r := d.radius y
  let F (t : ℝ) := (1+t) • z
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hF₀ : F 0 = z := by simp [F]
  have hF : HasDerivAt F z 0 := by
    simpa only [F,id_eq,one_smul] using (((hasDerivAt_id (0:ℝ)).const_add 1).smul_const z)
  have hD := (show HasFDerivAt A (fderiv ℝ A z) (F 0) by
    rw [hF₀]; exact (hA.differentiable (by simp) z).hasFDerivAt).comp_hasDerivAt 0 hF
  apply isRadialRow_of_hasDerivAt hD
  have hzB : z ∈ ball (0 : X dim) (5/4) :=
    closedBall_subset_ball (by norm_num : (1:ℝ) < 5/4) (sphere_subset_closedBall hz)
  have hNear : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), F t ∈ ball (0 : X dim) (5/4) :=
    hF.continuousAt.eventually (isOpen_ball.mem_nhds (hF₀ ▸ hzB))
  have hS : Continuous (fun t : ℝ => r*(1+t)) := continuous_const.mul (continuous_const.add continuous_id)
  have hR : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), r*(1+t) ∈ Ioo 0 ρ :=
    hS.continuousAt.eventually (isOpen_Ioo.mem_nhds (by simpa only [add_zero,mul_one] using
      (show r ∈ Ioo 0 ρ from ⟨hr,hrρ⟩)))
  filter_upwards [hNear,hR] with t ht hrt
  rw [Function.comp_apply,hEq ht]
  change IsRadialRow z (firstNormalVelocityCoefficient d y (r • frameVector d.frame y (F t)))
  rw [← frameVectorLinear_apply,show F t = (1+t) • z from rfl,
    map_smul,smul_smul,frameVectorLinear_apply]
  have hf := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hVel := initial_velocity_mem_interior_of_sphere hd hf hrt.1 hrt.2 hz
  exact isRadialRow_of_weight hz _ _ fun j => hd.actualNormalCoeff_radial_row hn hΩ hK hy hrt.1.ne' z hVel j

end CalderonN
