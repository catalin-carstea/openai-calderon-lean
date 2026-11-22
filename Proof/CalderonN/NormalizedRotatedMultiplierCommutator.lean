module

public import Proof.CalderonN.LinearizedPoissonWeakBounds
public import Proof.CalderonN.RotatedMultiplierHalfBound

import Mathlib.Tactic

/-! The rotated conormal multiplication commutator on finite harmonic
inputs. The elliptic estimates use the actual lifts of both the input
and its product with the smooth multiplier. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_normalized_rotated_multiplier_commutator_finite (hn : 3 ≤ dim)
    (i j : I dim) {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ z ∈ ball (0:X dim) 1,(A z).IsSymm)
    (ell : X dim →L[ℝ] ℝ) (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (m W D V E : SmoothData dim) (r C G F J : ℝ)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hC : 0 ≤ C) (hG : 1 ≤ G) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (hW : ∀ v : SmoothData dim, EqOn (smoothBallConormal A v.1)
      (fun z => W.1 z*fderiv ℝ v.1 z z) (standardSphere dim))
    (hD : EqOn D.1 (fun z => W.1 z-1) (standardSphere dim))
    (hV : EqOn V.1 (sphereRotationDerivative i j W.1) (standardSphere dim))
    (hE : EqOn E.1 (fun z => V.1 z-r*(ell.comp (ballRotationGeneratorL i j)) z) (standardSphere dim))
    (hWeight : ∀ z ∈ ball (0 : X dim) 1,
      (|W.1 z| ≤ F ∧ ‖fderiv ℝ W.1 z‖ ≤ F) ∧
      (|D.1 z| ≤ F*r ∧ ‖fderiv ℝ D.1 z‖ ≤ F*r) ∧
      (|V.1 z| ≤ F*r ∧ ‖fderiv ℝ V.1 z‖ ≤ F*r) ∧
      (|E.1 z| ≤ F*r^2 ∧ ‖fderiv ℝ E.1 z‖ ≤ F*r^2))
    (hm : SmoothMultiplierJetBound m J) :
    let A₀ : X dim → Mat dim := fun _ => 1
    let B := ballRotationCoefficient i j A
    let L : X dim → Mat dim := fun z => (ell.comp (ballRotationGeneratorL i j)) z • 1
    let W₁ := C*G
    let H := 1+W₁*(2+2*W₁)
    let T := W₁*(W₁+1+H)
    let C_e := W₁*(W₁+3*T+4*H)
    let N := Real.sqrt (unitSphereArea dim)
    let U := 2*Real.sqrt ((dim:ℝ)+3)
    let SR := Real.sqrt ((((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2)/(unitSphereArea dim))
    let K := U*F*SR*((W₁+2*T+C_e)*N)+U^2*F
    SmoothCoefficientC1Bound A G → SmoothCoefficientC1Bound (A-A₀) (G*r) →
    SmoothCoefficientC1Bound B (G*r) → SmoothCoefficientC1Bound (B-r • L) (G*r^2) →
    SmoothCoefficientC1Bound L G →
    SmoothDirichletDivergenceBudget A₀ (fun v => ‖smoothSobolev v‖) C →
    SmoothDirichletDivergenceBudget A (fun v => ‖smoothSobolev v‖) C →
    DirichletMultiplierForcingBudget A₀ m J C → DirichletMultiplierForcingBudget A m J C →
    ∀ f : HarmonicFiniteCoefficients dim,
      let u := harmonicFiniteSmooth f
      let R := rotatedConormalRemainderData i j hA S r
      ‖smoothBoundarySobolev hn (1/2:ℝ) (by norm_num)
        (smoothSubtractData (R (smoothDataMul m u)) (smoothDataMul m (R u)))‖ ≤
        K*J*r^2*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖ := by
  dsimp only
  intro hC_A hC_D hC_B hC_R hC_L hWeak₀ hWeak hStrong₀ hStrong f
  let u := harmonicFiniteSmooth f
  let v := smoothDataMul m u
  let A₀ : X dim → Mat dim := fun _ => 1
  let B := ballRotationCoefficient i j A
  let ell' := ell.comp (ballRotationGeneratorL i j)
  let L : X dim → Mat dim := fun z => ell' z • 1
  let U := S u
  let V₀ := S v
  let U' := S (smoothRotationData i j u)
  let V' := S (smoothRotationData i j v)
  let p := angularBallCorrection i j U.actual U'.actual
  let p' := angularBallCorrection i j V₀.actual V'.actual
  let q := angularBallCorrection i j U.first U'.first
  let q' := angularBallCorrection i j V₀.first V'.first
  let w := smoothMultiplierDefect m U.actual V₀.actual
  let w₀ := smoothMultiplierDefect m U.flat V₀.flat
  let t := smoothMultiplierDefect m p p'
  let t₁ := smoothMultiplierDefect m q q'
  let dw := smoothSubtractData w w₀
  let e := smoothSubtractData t ⟨r • t₁.1,t₁.2.const_smul r⟩
  let W₁ := C*G
  let H := 1+W₁*(2+2*W₁)
  let T := W₁*(W₁+1+H)
  let C_e := W₁*(W₁+3*T+4*H)
  let N := Real.sqrt (unitSphereArea dim)
  let U₀ := 2*Real.sqrt ((dim:ℝ)+3)
  let SR := Real.sqrt ((((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2)/(unitSphereArea dim))
  let K := U₀*F*SR*((W₁+2*T+C_e)*N)+U₀^2*F
  let hB := contDiff_ballRotationCoefficient i j hA
  let hL : ContDiff ℝ ∞ L := ell'.contDiff.smul contDiff_const
  let hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hSym₀ (z : X dim) : (A₀ z).IsSymm := Matrix.isSymm_one
  have hSym_B (z : X dim) (hz : z ∈ ball (0:X dim) 1) : (B z).IsSymm :=
    ballRotationCoefficient_isSymm i j hA isOpen_ball hSym hz
  have hSym_L (z : X dim) : (L z).IsSymm := Matrix.isSymm_one.smul (ell' z)
  have hpT : EqOn p.1 0 (standardSphere dim) :=
    angularBallCorrection_trace_zero i j U.actual U'.actual u U.actualTrace U'.actualTrace
  have hp'T : EqOn p'.1 0 (standardSphere dim) :=
    angularBallCorrection_trace_zero i j V₀.actual V'.actual v V₀.actualTrace V'.actualTrace
  have hpEq := negativeBallDivergence_angularBallCorrection i j hA U.actual U'.actual
    U.actualEquation U'.actualEquation
  have hp'Eq := negativeBallDivergence_angularBallCorrection i j hA V₀.actual V'.actual
    V₀.actualEquation V'.actualEquation
  obtain ⟨_,hqT,hqEq⟩ := rotated_affine_solution_equation i j U U'
  obtain ⟨_,hq'T,hq'Eq⟩ := rotated_affine_solution_equation i j V₀ V'
  have hFlatT : EqOn U.actual.1 U.flat.1 (standardSphere dim) := U.actualTrace.trans U.flatTrace.symm
  have ⟨hU,hdu,hq,heq⟩ := norm_linearized_poisson_weak_taylor hA hB hL U.actual U.flat p q
    r C G hr hr₁ hC (zero_le_one.trans hG) hC_D hC_B hC_R hC_L hWeak₀ hWeak hFlatT hpT hqT
    U.actualEquation U.flatEquation hpEq hqEq
  obtain ⟨hwT,hw₀T,_,hwEq,hw₀Eq,_⟩ :=
    conormalTaylorSolutions_multiplierDefects hA (fun z hz a b => (hSym z hz).apply b a) m U V₀
  have htT : EqOn t.1 0 (standardSphere dim) := fun z hz => by
    change p'.1 z-m.1 z*p.1 z = 0
    rw [show p.1 z = 0 from hpT hz,show p'.1 z = 0 from hp'T hz,mul_zero,sub_zero]
  have ht₁T : EqOn t₁.1 0 (standardSphere dim) := fun z hz => by
    change q'.1 z-m.1 z*q.1 z = 0
    rw [show q.1 z = 0 from hqT hz,show q'.1 z = 0 from hq'T hz,mul_zero,sub_zero]
  have htEq : EqOn (negativeBallDivergence A t.1)
      (fun z => -negativeBallDivergence B w.1 z-greenSourceCutoffError B m.1 U.actual.1 z-
        greenSourceCutoffError A m.1 p.1 z) (ball (0:X dim) 1) := fun z hz =>
    linearized_multiplier_defect_equation hA hB m U.actual V₀.actual p p' z
      (hSym z hz) (hSym_B z hz) (hpEq hz) (hp'Eq hz)
  have ht₁Eq : EqOn (negativeBallDivergence A₀ t₁.1)
      (fun z => -negativeBallDivergence L w₀.1 z-greenSourceCutoffError L m.1 U.flat.1 z-
        greenSourceCutoffError A₀ m.1 q.1 z) (ball (0:X dim) 1) := fun z hz =>
    linearized_multiplier_defect_equation hA₀ hL m U.flat V₀.flat q q' z
      (hSym₀ z) (hSym_L z) (hqEq hz) (hq'Eq hz)
  obtain ⟨hw₀,hdw,ht₁,he⟩ := norm_rotated_multiplier_bulk_of_weak hA hB hL
    m U.actual U.flat p q w w₀ t t₁ r C G H J hr hr₁ hC hG (by dsimp only [H,W₁]; positivity)
    hJ hC_A hC_D hC_R hC_L hStrong₀ hStrong hU hdu hq heq hwT hw₀T htT ht₁T hwEq hw₀Eq htEq ht₁Eq
  have hEll₀ := uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))
  have hFlat := eqOn_closedUnitBall_of_equal_ball_forcing hA₀ hEll₀ (fun _ _ => rfl) U.flat u
    (fun z hz => (U.flatEquation hz).trans (negativeBallDivergence_flat_harmonicFiniteSmooth f z).symm)
    U.flatTrace
  have hFlatN : ‖smoothSobolev U.flat‖ ≤ N*‖smoothBoundarySobolev hn (1/2:ℝ) (by norm_num) u‖ := by
    change ‖smoothBallSobolev 1 U.flat‖ ≤ _
    rw [smoothBallSobolev_eq_of_eqOn_ball 1 U.flat u (fun z hz => hFlat (ball_subset_closedBall hz)),
      smoothBoundarySobolev_harmonicFiniteSmooth]
    change ‖smoothSobolev u‖ ≤ _
    rw [← harmonicFirstOrderLift_finite_smooth f]
    exact norm_harmonicFirstOrderLift_le _
  have hW_pos : 0 ≤ W₁ := by dsimp [W₁]; positivity
  have hT_pos : 0 ≤ T := by dsimp [T,H,W₁]; positivity
  have hE_pos : 0 ≤ C_e := by dsimp [C_e,T,H,W₁]; positivity
  have hw₀' : ‖smoothBallSobolev 2 w₀‖ ≤ W₁*J*‖smoothSobolev U.flat‖ := hw₀
  have hdw' : ‖smoothBallSobolev 2 dw‖ ≤ T*J*r*‖smoothSobolev U.flat‖ := hdw
  have ht₁' : ‖smoothBallSobolev 2 t₁‖ ≤ T*J*‖smoothSobolev U.flat‖ := ht₁
  have he' : ‖smoothBallSobolev 2 e‖ ≤ C_e*J*r^2*‖smoothSobolev U.flat‖ := he
  obtain ⟨Z,hZ,hZN⟩ := norm_rotated_multiplier_boundary_half_bound hn W D V E m u w₀ dw t₁ e
    r F J (W₁*N) (T*N) (T*N) (C_e*N) hr hF hJ
    (by dsimp [W₁,N]; positivity) (by dsimp [T,H,W₁,N]; positivity)
    (by dsimp [T,H,W₁,N]; positivity) (by dsimp [C_e,T,H,W₁,N]; positivity)
    (fun z hz => ⟨(hWeight z hz).1,(hWeight z hz).2.1,(hWeight z hz).2.2.1,
      (hWeight z hz).2.2.2,(hm z hz).2⟩)
    (hw₀'.trans ((mul_le_mul_of_nonneg_left hFlatN (mul_nonneg hW_pos hJ)).trans_eq (by ring)))
    (hdw'.trans ((mul_le_mul_of_nonneg_left hFlatN (mul_nonneg (mul_nonneg hT_pos hJ) hr)).trans_eq (by ring)))
    (ht₁'.trans ((mul_le_mul_of_nonneg_left hFlatN (mul_nonneg hT_pos hJ)).trans_eq (by ring)))
    (he'.trans ((mul_le_mul_of_nonneg_left hFlatN (mul_nonneg (mul_nonneg hE_pos hJ) (sq_nonneg r))).trans_eq (by ring)))
  let R := rotatedConormalRemainderData i j hA S r
  have hb := rotated_conormal_multiplier_boundary i j hA W hW S m u r
  have hEq : EqOn (smoothSubtractData (R v) (smoothDataMul m (R u))).1 Z.1 (standardSphere dim) := by
    intro z hz
    change (R v).1 z-m.1 z*(R u).1 z = Z.1 z
    let W' := smoothRotationData i j W
    have hp : (R v).1 z-m.1 z*(R u).1 z = W.1 z*fderiv ℝ e.1 z z+
        r*(W.1 z-1)*fderiv ℝ t₁.1 z z+W'.1 z*fderiv ℝ dw.1 z z+
        (W'.1 z-r*ell' z)*fderiv ℝ w₀.1 z z+(W'.1 z-r*ell' z)*(fderiv ℝ m.1 z z*u.1 z) :=
      hb hz
    have hE' : E.1 z = V.1 z-r*ell' z := hE hz
    have hV' : V.1 z = W'.1 z := hV hz
    rw [hp,hZ]
    dsimp only
    rw [show D.1 z = W.1 z-1 from hD hz,hE',hV']
  change ‖smoothBoundarySobolev hn (1/2:ℝ) (by norm_num)
    (smoothSubtractData (R v) (smoothDataMul m (R u)))‖ ≤ K*J*r^2*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖
  rw [smoothBoundarySobolev_eq_of_eqOn hn _ (by norm_num) _ _ hEq,
    ← smoothBoundarySobolev_harmonicFiniteSmooth hn (1/2:ℝ) (by norm_num) f]
  exact hZN.trans_eq (by dsimp only [K,U₀,SR]; ring)

end CalderonN
