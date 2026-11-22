module

public import Proof.CalderonN.NativeCoefficientSmoothBounds
public import Proof.CalderonN.MultiplierDefectBulkTaylor
public import Proof.CalderonN.MultiplierConormalHalfBound
public import Proof.CalderonN.SmoothMultiplierCommutatorCompletion
public import Proof.CalderonN.SmoothPoissonWeakTaylor

import Proof.CalderonN.SmoothConormalTaylorSymmetry
import Mathlib.Tactic

/-! The Dirichlet bulk estimate controls the conormal multiplication
commutator in the boundary half-order norm. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 7600000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def SmoothMultiplierJetBound (m : SmoothData dim) (J : ℝ) : Prop :=
  ∀ z ∈ ball (0 : X dim) 1,
    (‖fderiv ℝ m.1 z‖ ≤ J ∧ ∀ i, ‖fderiv ℝ (coordDeriv i m.1) z‖ ≤ J) ∧
    (|fderiv ℝ m.1 z z| ≤ J ∧ ‖fderiv ℝ (fun x => fderiv ℝ m.1 x x) z‖ ≤ J)

theorem norm_normalized_multiplier_commutator (hn : 3 ≤ dim)
    (P Q Inv C : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hInv : 0 ≤ Inv) (hC : 0 ≤ C) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (F F₀ F₁ : SmoothCoefficientMatrix dim 2) (ell : X dim →L[ℝ] ℝ) (r : ℝ),
    let A := coefficientMatrixField 2 F
    let hA := contDiff_coefficientMatrixField 2 F
    let E := fixedBallSmoothEnergyL hA.continuous
    let E₀ := fixedBallFlatEnergyL dim
    let E₁ := fixedBallSmoothEnergyL (ell.continuous.smul
      (show Continuous (fun _ : X dim => (1 : Mat dim)) from continuous_const))
    (∀ z ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F₀ z = 1) →
    EqOn (coefficientMatrixField 2 F₁) (fun z => ell z • (1 : Mat dim)) (ball (0 : X dim) 1) →
    (∀ z ∈ ball (0 : X dim) 1, (A z).IsSymm) →
    (∀ v : FixedBallH1Zero dim, (1/10:ℝ)*‖v‖^2 ≤ E (v : FixedBallH1 dim) (v : FixedBallH1 dim)) →
    ‖E₁‖ ≤ (dim:ℝ)^2*P → ‖E-E₀‖ ≤ (dim:ℝ)^2*(P+Q)*r →
    ‖E-E₀-r • E₁‖ ≤ (dim:ℝ)^2*Q*r^2 →
    0 ≤ r → r ≤ 1 → ‖F₁‖ ≤ P → ‖F-F₀‖ ≤ (P+Q)*r → ‖F-F₀-r • F₁‖ ≤ Q*r^2 →
    ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ Inv →
    ‖(strongDirichletOperator fixedSobolevCalculus 0 F₀).inverse‖ ≤ Inv →
    ∀ lo hi, UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi →
    ∀ (W D_W R_W : SmoothData dim)
      (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f),
    (∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim)) →
    EqOn D_W.1 (fun z => W.1 z-1) (standardSphere dim) →
    EqOn R_W.1 (fun z => W.1 z-1-r*ell z) (standardSphere dim) →
    (∀ z ∈ ball (0 : X dim) 1,
      (|W.1 z| ≤ C ∧ ‖fderiv ℝ W.1 z‖ ≤ C) ∧
      (|D_W.1 z| ≤ C*r ∧ ‖fderiv ℝ D_W.1 z‖ ≤ C*r) ∧
      (|R_W.1 z| ≤ C*r^2 ∧ ‖fderiv ℝ R_W.1 z‖ ≤ C*r^2)) →
    ∀ (m : SmoothData dim) (J : ℝ), 0 ≤ J → SmoothMultiplierJetBound m J →
    ∀ u : SmoothData dim,
      let T (f : SmoothData dim) := (S f).remainder hA r
      ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num)
        (smoothSubtractData (T (smoothDataMul m u)) (smoothDataMul m (T u)))‖ ≤
      L*J*r^2*‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u‖ := by
  let c := (1/10:ℝ)
  let P_w := (dim:ℝ)^2*(P+Q)
  let Q_w := (dim:ℝ)^2*Q
  let G_w := (dim:ℝ)^2*P
  let q₁ := G_w/c
  let q_R := (Q_w+P_w*q₁)/c
  let k := 4*(dim:ℝ)^2
  let a := ‖fullBallCoefficientOperatorL dim 0‖
  let a₁ := a*P
  let a_D := a*(P+Q)
  let a_R := a*Q
  let jA := k*(1+P+Q)
  let j₀ := k
  let j₁ := k*P
  let jD := k*(P+Q)
  let jR := k*Q
  let C₀ := Inv*j₀
  let C₁ := Inv*(a₁*C₀+j₁+j₀*q₁)
  let C_e := Inv*(jA*q_R+jR+jD*q₁+a_R*C₀+a_D*C₁)
  let V := Real.sqrt (unitSphereArea dim)
  let L₀ := 2*Real.sqrt ((dim:ℝ)+3)
  let L₁ := Real.sqrt ((((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2)/(unitSphereArea dim))
  let L := L₀*C*L₁*((C₀+C₁+C_e)*V)+L₀^2*C
  have hcs : 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C_e := by
    dsimp only [C₀,C₁,C_e,a₁,a_D,a_R,jA,j₀,j₁,jD,jR,q₁,q_R,c,P_w,Q_w,G_w,k,a]
    exact ⟨by positivity,by positivity,by positivity⟩
  refine ⟨L,by dsimp only [L,L₀,L₁,V]; positivity,?_⟩
  intro F F₀ F₁ ell r
  dsimp only
  intro hF₀ hF₁ hSym hCoer hG hDE hRE hr hr₁ hP₁ hD₁ hR₁ hInvF hInvF₀
    lo hi hEll W D_W R_W S hW hD_W hR_W hWeight m J hJ hM u
  let A := coefficientMatrixField 2 F
  let A₀ : X dim → Mat dim := fun _ => 1
  let A₁ : X dim → Mat dim := fun z => ell z • 1
  let D := A-A₀
  let R := D-r • A₁
  let hA := contDiff_coefficientMatrixField 2 F
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hA₁ : ContDiff ℝ ∞ A₁ := ell.contDiff.smul contDiff_const
  have hD : ContDiff ℝ ∞ D := hA.sub hA₀
  have hR : ContDiff ℝ ∞ R := hD.sub (hA₁.const_smul r)
  let T (f : SmoothData dim) := (S f).remainder hA r
  have hSym' (z : X dim) (hz : z ∈ ball (0 : X dim) 1) (i j : Fin dim) : A z i j = A z j i :=
    (hSym z hz).apply j i
  have hF₀unit : EqOn (coefficientMatrixField 2 F₀) A₀ (ball (0 : X dim) 1) :=
    fun z hz => hF₀ z (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (ball_subset_closedBall hz))
  have hF_D : EqOn (coefficientMatrixField 2 (F-F₀)) D (ball (0 : X dim) 1) := by
    intro z hz
    rw [coefficientMatrixField_two_sub]
    change A z-coefficientMatrixField 2 F₀ z = A z-A₀ z
    rw [hF₀unit hz]
  have hF_R : EqOn (coefficientMatrixField 2 (F-F₀-r • F₁)) R (ball (0 : X dim) 1) := by
    intro z hz
    rw [coefficientMatrixField_two_sub,coefficientMatrixField_two_smul]
    change coefficientMatrixField 2 (F-F₀) z-r • coefficientMatrixField 2 F₁ z = D z-r • A₁ z
    rw [hF_D hz,hF₁ hz]
  have hEll₀ := uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))
  have hEllF₀ : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F₀) 1 1 := by
    refine ⟨hEll₀.1,hEll₀.2.1,fun z hz => ?_⟩
    rw [hF₀unit hz]
    exact hEll₀.2.2 hz
  have hInv₀ (v g : SmoothData dim) (hv : EqOn v.1 0 (standardSphere dim))
      (hg : EqOn (negativeBallDivergence A₀ v.1) g.1 (ball (0 : X dim) 1)) :
      ‖smoothBallSobolev 2 v‖ ≤ Inv*‖smoothBallSobolev 0 g‖ := by
    have hEq : EqOn (negativeBallDivergence (coefficientMatrixField 2 F₀) v.1) g.1 (ball (0 : X dim) 1) := by
      intro z hz
      have hGerm : coefficientMatrixField 2 F₀ =ᶠ[𝓝 z] A₀ := by
        filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hF₀unit hx
      exact (negativeBallDivergence_congr_germ hGerm EventuallyEq.rfl).trans (hg hz)
    exact (norm_smooth_zeroDirichlet_le_of_forcing F₀ hEllF₀ v g hv hEq).trans
      (mul_le_mul_of_nonneg_right hInvF₀ (norm_nonneg _))
  have hInvA (v g : SmoothData dim) (hv : EqOn v.1 0 (standardSphere dim))
      (hg : EqOn (negativeBallDivergence A v.1) g.1 (ball (0 : X dim) 1)) :
      ‖smoothBallSobolev 2 v‖ ≤ Inv*‖smoothBallSobolev 0 g‖ :=
    (norm_smooth_zeroDirichlet_le_of_forcing F hEll v g hv hg).trans
      (mul_le_mul_of_nonneg_right hInvF (norm_nonneg _))
  have hCoer₀ (v : FixedBallH1Zero dim) :
      c*‖v‖^2 ≤ fixedBallFlatEnergyL dim (v : FixedBallH1 dim) (v : FixedBallH1 dim) := by
    have h := fixedBallSmoothEnergy_zero_coercive continuous_const hEll₀ v
    change (1/5:ℝ)*‖v‖*‖v‖ ≤ fixedBallFlatEnergyL dim (v : FixedBallH1 dim) (v : FixedBallH1 dim) at h
    dsimp only [c]
    nlinarith [sq_nonneg ‖v‖]
  have hEntry₀ (z : X dim) (_ : z ∈ ball (0 : X dim) 1) (i j : Fin dim) :
      |A₀ z i j| ≤ 1 ∧ ‖fderiv ℝ (fun x => A₀ x i j) z‖ ≤ 1 := by
    classical
    simp [A₀,Matrix.one_apply]
    split <;> norm_num
  have hEntryD := coefficientEntry_bounds_of_eqOn_native (F-F₀) ((P+Q)*r) hD₁ hF_D
  have hEntryR := coefficientEntry_bounds_of_eqOn_native (F-F₀-r • F₁) (Q*r^2) hR₁ hF_R
  have hEntry₁ := coefficientEntry_bounds_of_eqOn_native F₁ P hP₁ hF₁
  have hEntryA (z : X dim) (hz : z ∈ ball (0 : X dim) 1) (i j : Fin dim) :
      |A z i j| ≤ 1+P+Q ∧ ‖fderiv ℝ (fun x => A x i j) z‖ ≤ 1+P+Q := by
    have hEq : (fun z => A z i j) = (fun z => A₀ z i j)+(fun z => D z i j) := by
      ext x
      change A x i j = A₀ x i j+(A x i j-A₀ x i j)
      ring
    have hR : (P+Q)*r ≤ P+Q := by nlinarith [mul_nonneg (add_nonneg hP hQ) (sub_nonneg.mpr hr₁)]
    have hDiff₀ : DifferentiableAt ℝ (fun z => A₀ z i j) z := differentiableAt_const _
    have hDiffD : DifferentiableAt ℝ (fun z => D z i j) z :=
      ((contDiff_pi.mp (contDiff_pi.mp hD i) j).differentiable (by simp)) z
    constructor
    · rw [congrFun hEq z]
      exact ((abs_add_le _ _).trans (add_le_add (hEntry₀ z hz i j).1 (hEntryD z hz i j).1)).trans
        (by linarith)
    · rw [hEq,fderiv_add hDiff₀ hDiffD]
      exact ((norm_add_le _ _).trans (add_le_add (hEntry₀ z hz i j).2 (hEntryD z hz i j).2)).trans
        (by linarith)
  have hCut (v : SmoothData dim) (b : ℝ) (hb : 0 ≤ b) {A' : X dim → Mat dim}
      (hA' : ContDiff ℝ ∞ A')
      (hEntry : ∀ z ∈ ball (0 : X dim) 1, ∀ i j,
        |A' z i j| ≤ b ∧ ‖fderiv ℝ (fun x => A' x i j) z‖ ≤ b) :
      ‖smoothBallSobolev 0 (smoothMultiplierForcing hA' m v)‖ ≤ (k*b*J)*‖smoothSobolev v‖ :=
    norm_smoothMultiplierForcing_le hA' m v b J hb hJ hEntry fun z hz => (hM z hz).1
  have hFin (f : HarmonicFiniteCoefficients dim) :
      let p := harmonicFiniteSmooth f
      ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num)
        (smoothSubtractData (T (smoothDataMul m p)) (smoothDataMul m (T p)))‖ ≤
        (L*J*r^2)*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
    dsimp only
    let p := harmonicFiniteSmooth f
    let U := S p
    let V' := S (smoothDataMul m p)
    have hFlat := eqOn_closedUnitBall_of_equal_ball_forcing hA₀ hEll₀ (fun _ _ => rfl) U.flat p
      (fun z hz => (U.flatEquation hz).trans (negativeBallDivergence_flat_harmonicFiniteSmooth f z).symm)
      U.flatTrace
    have hFlatN : ‖smoothSobolev U.flat‖ ≤ V*‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) p‖ := by
      change ‖smoothBallSobolev 1 U.flat‖ ≤ _
      rw [smoothBallSobolev_eq_of_eqOn_ball 1 U.flat p (fun z hz => hFlat (ball_subset_closedBall hz))]
      rw [smoothBoundarySobolev_harmonicFiniteSmooth]
      change ‖smoothSobolev p‖ ≤ _
      rw [← harmonicFirstOrderLift_finite_smooth f]
      exact norm_harmonicFirstOrderLift_le _
    obtain ⟨hFirst,hWeak⟩ := smoothPoisson_weakTaylor_bound hA F hEll U r c P_w Q_w G_w
      hr (by dsimp [c]; positivity) (by dsimp [P_w]; positivity)
      (by dsimp [Q_w]; positivity) (by dsimp [G_w]; positivity) hCoer hCoer₀ hDE hRE hG
    let w := smoothMultiplierDefect m U.actual V'.actual
    let w₀ := smoothMultiplierDefect m U.flat V'.flat
    let w₁ := smoothMultiplierDefect m U.first V'.first
    let e : SmoothData dim := ⟨w.1-w₀.1-r • w₁.1,(w.2.sub w₀.2).sub (w₁.2.const_smul r)⟩
    let E' : SmoothData dim := ⟨U.actual.1-U.flat.1-r • U.first.1,
      (U.actual.2.sub U.flat.2).sub (U.first.2.const_smul r)⟩
    have hWeakE : ‖smoothSobolev E'‖ ≤ q_R*r^2*‖smoothSobolev U.flat‖ := by
      let B : smoothBallDataSubmodule dim := ⟨U.actual.1,U.actual.2⟩
      let U₀ : smoothBallDataSubmodule dim := ⟨U.flat.1,U.flat.2⟩
      let U₁ : smoothBallDataSubmodule dim := ⟨U.first.1,U.first.2⟩
      let N := smoothBallSobolevLinear dim 1
      change ‖N (B-U₀-r • U₁)‖ ≤ _
      rw [map_sub,map_sub,map_smul]
      exact hWeak
    have hBulk := norm_multiplier_defect_bulk_taylor hA hSym' m U V' r hr Inv Inv
      (jA*J) (j₀*J) (j₁*J) (jD*J) (jR*J) a₁ a_D a_R q₁ q_R hInv hInv
      (by dsimp [jA,k]; positivity) (by dsimp [j₀,k]; positivity) (by dsimp [j₁,k]; positivity)
      (by dsimp [jD,k]; positivity) (by dsimp [jR,k]; positivity)
      (by dsimp [a₁,a]; positivity) (by dsimp [a_D,a]; positivity) (by dsimp [a_R,a]; positivity)
      (by dsimp [q₁,G_w,c]; positivity) (by dsimp [q_R,q₁,Q_w,P_w,G_w,c]; positivity)
      hInv₀ hInvA (fun v => hCut v _ (by positivity) hA hEntryA)
      (fun v => (hCut v 1 zero_le_one hA₀ hEntry₀).trans_eq (by dsimp [j₀]; ring))
      (fun v => hCut v P hP hA₁ hEntry₁)
      (fun v => (hCut v _ (by positivity) hD hEntryD).trans_eq (by dsimp [jD]; ring))
      (fun v => (hCut v _ (by positivity) hR hEntryR).trans_eq (by dsimp [jR]; ring))
      (fun v => norm_smoothDivergenceForcing_le_of_native_bound F₁ hA₁ P hP₁ hF₁ v)
      (fun v => (norm_smoothDivergenceForcing_le_of_native_bound (F-F₀) hD _ hD₁ hF_D v).trans_eq
        (by dsimp [a_D,a]; ring))
      (fun v => (norm_smoothDivergenceForcing_le_of_native_bound (F-F₀-r • F₁) hR _ hR₁ hF_R v).trans_eq
        (by dsimp [a_R,a]; ring)) hFirst hWeakE
    have h₀ : ‖smoothBallSobolev 2 w₀‖ ≤ (C₀*J)*‖smoothSobolev U.flat‖ :=
      hBulk.1.trans_eq (by dsimp [C₀]; ring)
    have h₁ : ‖smoothBallSobolev 2 w₁‖ ≤ (C₁*J)*‖smoothSobolev U.flat‖ :=
      hBulk.2.1.trans_eq (by dsimp [C₁,C₀]; ring)
    have h_e : ‖smoothBallSobolev 2 e‖ ≤ (C_e*J)*r^2*‖smoothSobolev U.flat‖ :=
      hBulk.2.2.trans_eq (by dsimp [C_e,C₁,C₀]; ring)
    obtain ⟨Z,hZ,hZN⟩ := norm_multiplier_conormal_half_bound hn hA W D_W R_W hW m U V' r C J
      (C₀*J*V) (C₁*J*V) (C_e*J*V) hr hC hJ
      (by positivity) (by positivity) (by positivity) hD_W hR_W
      (fun z hz => ⟨(hWeight z hz).1,(hWeight z hz).2.1,(hWeight z hz).2.2,(hM z hz).2⟩)
      (h₀.trans ((mul_le_mul_of_nonneg_left hFlatN (by positivity)).trans_eq (by ring)))
      (h₁.trans ((mul_le_mul_of_nonneg_left hFlatN (by positivity)).trans_eq (by ring)))
      (h_e.trans ((mul_le_mul_of_nonneg_left hFlatN (by positivity)).trans_eq (by ring)))
    have hEq : EqOn
        (smoothSubtractData (T (smoothDataMul m p)) (smoothDataMul m (T p))).1 Z.1 (standardSphere dim) :=
      fun z hz => (hZ hz).symm
    rw [smoothBoundarySobolev_eq_of_eqOn hn (1/2 : ℝ) (by norm_num) _ _ hEq,
      ← smoothBoundarySobolev_harmonicFiniteSmooth hn (1/2 : ℝ) (by norm_num) f]
    exact hZN.trans_eq (by dsimp [L,L₀,L₁]; ring)
  exact norm_smooth_multiplier_commutator_half_of_finite hn m T
    (fun f g => conormalTaylorSolutions_remainder_symmetric hn hA hSym (S f) (S g) r)
    (L*J*r^2) (by positivity) hFin u

end CalderonN
