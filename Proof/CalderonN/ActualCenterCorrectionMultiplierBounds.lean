module

public import Proof.CalderonN.SupportedSphereMultiplierGerms

public import Proof.CalderonN.ActualCenterCorrectionGerms

import Mathlib.Tactic

/-! The exact normal and tangential multipliers of the quadratic center
correction inherit the joint scaled chart bounds. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 5300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem LocalSmoothJetBudget.sphere_coordinate_inner {f : X dim × X dim → X dim} {q : X dim × X dim}
    {N : ℕ} {C : ℝ} (h : LocalSmoothJetBudget f q N C) {z : X dim} (hz : ‖z+q.2‖ ≤ 1) :
    LocalSmoothJetBudget (fun w => ⟪z+w.2,f w⟫_ℝ) q N
      ((2:ℝ)^N*‖innerSL ℝ (E:=X dim)‖*1*C) := by
  let L := ContinuousLinearMap.snd ℝ (X dim) (X dim)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    rw [one_mul]
    exact norm_snd_le w
  have hZ : LocalSmoothJetBudget (fun w : X dim × X dim => z+w.2) q N 1 := by
    refine ⟨contDiffAt_const.add contDiffAt_snd,?_⟩
    intro n hn
    by_cases h : n=0
    · subst n; rwa [norm_iteratedFDeriv_zero]
    · exact (norm_iteratedFDeriv_affine_pos_le L z q n (by omega)).trans hL
  exact hZ.bilinear h (innerSL ℝ)

theorem LocalSmoothJetBudget.sphere_coordinate_product {f : X dim × X dim → X dim} {q : X dim × X dim}
    {N : ℕ} {C : ℝ} (h : LocalSmoothJetBudget f q N C) {z : X dim} (hz : ‖z+q.2‖ ≤ 1)
    (i j : I dim) :
    LocalSmoothJetBudget (fun w => (z+w.2) i*f w j) q N ((2:ℝ)^N*‖ContinuousLinearMap.mul ℝ ℝ‖*1*C) := by
  let L := ContinuousLinearMap.snd ℝ (X dim) (X dim)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    rw [one_mul]
    exact norm_snd_le w
  have hZ : LocalSmoothJetBudget (fun w : X dim × X dim => z+w.2) q N 1 := by
    refine ⟨contDiffAt_const.add contDiffAt_snd,?_⟩
    intro n hn
    by_cases h : n=0
    · subst n; rwa [norm_iteratedFDeriv_zero]
    · exact (norm_iteratedFDeriv_affine_pos_le L z q n (by omega)).trans hL
  have hi : LocalSmoothJetBudget (fun w : X dim × X dim => (z+w.2) i) q N 1 :=
    (hZ.linear_postcomp (EuclideanSpace.proj (𝕜:=ℝ) i)).enlarge (by
      simpa only [mul_one] using norm_euclidean_proj_le_one i)
  have hj : LocalSmoothJetBudget (fun w => f w j) q N C :=
    (h.linear_postcomp (EuclideanSpace.proj (𝕜:=ℝ) j)).enlarge
      ((mul_le_mul_of_nonneg_right (norm_euclidean_proj_le_one j) h.nonneg).trans_eq (one_mul _))
  exact hi.real_mul hj

theorem uniform_actual_centerCorrectionMultiplier_germs
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (D : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim),
        let N := supportedSphereMultiplierFamily (fun y hy => smoothVelocityNormal ((D y hy).centerCorrection i))
        let V (a b : I dim) := supportedSphereMultiplierFamily
          (fun y hy => smoothVelocityAngular ((D y hy).centerCorrection i) a b)
        ∃ (hN : SmoothSupportedTraceFiberRegular Y N) (hV : ∀ a b,SmoothSupportedTraceFiberRegular Y (V a b)),
          ∀ x ∈ Y,
          let β := beta d.γ d.radius x
          SupportedSphereMultiplierGerm (fun y hy => smoothVelocityNormal ((D y hy).centerCorrection i)) x β C ∧
          ∀ a b,SupportedSphereMultiplierGerm
            (fun y hy => smoothVelocityAngular ((D y hy).centerCorrection i) a b) x β C := by
  obtain ⟨η,C₀,hη,hC₀,hCore⟩ := uniform_actual_centerCorrection_germs
    hY hΩ hYc hSub 4 (by decide) hm K ρ c₀ M Cj hK hρ
  let A := (2:ℝ)^4*(‖innerSL ℝ (E:=X dim)‖+‖ContinuousLinearMap.mul ℝ ℝ‖)*C₀
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨η,A,hη,hA,?_⟩
  intro floor hFloor ε hε hs d hd hFrame D i
  dsimp only
  let mN (y : X dim) (hy : y ∈ Y) := smoothVelocityNormal ((D y hy).centerCorrection i)
  let mV (a b : I dim) (y : X dim) (hy : y ∈ Y) := smoothVelocityAngular ((D y hy).centerCorrection i) a b
  let P (p : X dim × X dim → X dim) (q : X dim × X dim) := ⟪q.2,p q⟫_ℝ
  let Q (p : X dim × X dim → X dim) (a b : I dim) (q : X dim × X dim) := q.2 a*p q b
  have hP {p : X dim × X dim → X dim} (hp : ContDiff ℝ ∞ p) : ContDiff ℝ ∞ (P p) :=
    contDiff_snd.inner ℝ hp
  have hQ {p : X dim × X dim → X dim} (hp : ContDiff ℝ ∞ p) (a b : I dim) :
      ContDiff ℝ ∞ (Q p a b) :=
    ((EuclideanSpace.proj (𝕜:=ℝ) a).contDiff.comp contDiff_snd).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.comp hp)
  have hN : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily mN) := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    obtain ⟨V,p,hV,hxV,hVY,hp,hRep,_⟩ := hCore floor hFloor ε hε hs d hd hFrame D i x hx
    refine ⟨V,P p,hV,hxV,hVY,(hP hp).contDiffOn,fun y hy hyY z hz => ?_⟩
    change ⟪z,p (y,z)⟫_ℝ = ⟪z,((D y hyY).centerCorrection i).1 z⟫_ℝ
    rw [hRep y hy hyY z hz]
  have hV (a b : I dim) : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily (mV a b)) := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    obtain ⟨V,p,hV,hxV,hVY,hp,hRep,_⟩ := hCore floor hFloor ε hε hs d hd hFrame D i x hx
    refine ⟨V,Q p a b,hV,hxV,hVY,(hQ hp a b).contDiffOn,fun y hy hyY z hz => ?_⟩
    change z a*p (y,z) b = z a*((D y hyY).centerCorrection i).1 z b
    rw [hRep y hy hyY z hz]
  refine ⟨hN,hV,?_⟩
  intro x hx
  obtain ⟨V,p,hVo,hxV,hVY,hp,hRep,hJet⟩ := hCore floor hFloor ε hε hs d hd hFrame D i x hx
  refine ⟨⟨V,P p,hVo,hxV,hVY,hP hp,?_,?_⟩,fun a b =>
    ⟨V,Q p a b,hVo,hxV,hVY,hQ hp a b,?_,?_⟩⟩
  · intro y hy hyY z hz
    exact congrArg (fun w => ⟪z,w⟫_ℝ) (hRep y hy hyY z hz)
  · intro z hz
    exact ((hJet z hz).sphere_coordinate_inner
      (show ‖z+(0:X dim × X dim).2‖ ≤ 1 by simpa using mem_closedBall_zero_iff.mp hz)).enlarge (by
        dsimp only [A]; rw [mul_one]; gcongr; exact le_add_of_nonneg_right (norm_nonneg (ContinuousLinearMap.mul ℝ ℝ)))
  · intro y hy hyY z hz
    exact congrArg (fun w : X dim => z a*w b) (hRep y hy hyY z hz)
  · intro z hz
    exact ((hJet z hz).sphere_coordinate_product
      (show ‖z+(0:X dim × X dim).2‖ ≤ 1 by simpa using mem_closedBall_zero_iff.mp hz) a b).enlarge (by
        dsimp only [A]; rw [mul_one]; gcongr; exact le_add_of_nonneg_left (norm_nonneg (innerSL ℝ (E:=X dim))))

theorem uniform_actual_centerCorrectionMultiplier_bounds (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f,B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f)) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (D : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim),
        let N := supportedSphereMultiplierFamily (fun y hy => smoothVelocityNormal ((D y hy).centerCorrection i))
        let V (a b : I dim) := supportedSphereMultiplierFamily
          (fun y hy => smoothVelocityAngular ((D y hy).centerCorrection i) a b)
        ∃ (hN : SmoothSupportedTraceFiberRegular Y N) (hV : ∀ a b,SmoothSupportedTraceFiberRegular Y (V a b)),
          ∀ x ∈ Y,
          let β := beta d.γ d.radius x
          SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C N hN ∧
          ∀ a b,SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C (V a b) (hV a b) := by
  obtain ⟨η,A,hη,hA,hG⟩ := uniform_actual_centerCorrectionMultiplier_germs hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨C,hC,hLift⟩ := supportedSphereMultiplier_bounds_of_germ (Y:=Y) hn B hB hFin A hA
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hFloor ε hε hs d hd hf D i
  obtain ⟨hN,hV,h⟩ := hG floor hFloor ε hε hs d hd hf D i
  refine ⟨hN,hV,?_⟩
  intro x hx
  have hβ := zero_lt_one.trans_le (hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1)
  exact ⟨hLift hY x hx _ hβ _ hN (h x hx).1,fun a b => hLift hY x hx _ hβ _ (hV a b) ((h x hx).2 a b)⟩

end CalderonN
