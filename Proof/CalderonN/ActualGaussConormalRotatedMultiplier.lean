module

public import Proof.CalderonN.ActualGaussConormalMultiplierBounds
public import Proof.CalderonN.ActualRotatedMultiplierBudgets
public import Proof.CalderonN.NormalizedRotatedMultiplierCommutator
public import Proof.CalderonN.SmoothTraceCommutatorBounds

import Proof.CalderonN.SmoothTraceLinearAdjunction
import Mathlib.Tactic

/-! The mixed rotation and multiplication estimate for the genuine
scaled conormal remainder on the common smooth sphere core. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actualGauss_scaledConormal_rotation_multiplier_bound (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ D : ActualGaussFiberData d y,
        ∀ (b : SmoothData dim) (J : ℝ), 0 ≤ J → SmoothMultiplierJetBound b J →
        ∀ (i j : I dim) (u : SmoothSphereTrace dim),
          let T := smoothTraceAngularComm i j (((d.radius y)^2)⁻¹ • D.conormalRemainder)
          let B := smoothSphereTraceMul b
          ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) ((T*B-B*T) u)‖ ≤
            C*J*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ := by
  obtain ⟨η,C,G,F,hη,hC,hG,hF,hBudgets⟩ :=
    uniform_actual_rotated_multiplier_budgets (Y:=Y) (by omega) hΩ hm K ρ c₀ M Cj hK hρ
  let W₁ := C*G
  let H := 1+W₁*(2+2*W₁)
  let T := W₁*(W₁+1+H)
  let C_e := W₁*(W₁+3*T+4*H)
  let N := Real.sqrt (unitSphereArea dim)
  let U := 2*Real.sqrt ((dim:ℝ)+3)
  let SR := Real.sqrt ((((dim:ℝ)+3)*‖ballRadialDerivativeL dim‖^2)/(unitSphereArea dim))
  let L := U*F*SR*((W₁+2*T+C_e)*N)+U^2*F
  have hL : 0 ≤ L := by dsimp only [L,U,SR,N,W₁,T,C_e,H]; positivity
  refine ⟨η,L,hη,hL,?_⟩
  intro floor hf ε he hs d yData y hy D b J hJ hM i j u
  dsimp only
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  obtain ⟨A,hA,S,W,Wd,hFA,hr,hr₁,hSym,hWeak₀,hWeak,hStrong,hCa,hCd,hW,hWD,hJetW,hRot⟩ :=
    hBudgets floor hf ε he hs d yData y hy
  obtain ⟨hCb,hCr,hCl,V,E,hV,hVE,hJetV⟩ := hRot i j
  obtain ⟨hStrong₀,hStrongA⟩ := hStrong b J hJ hM
  have hD : EqOn Wd.1 (fun z => W.1 z-1) (standardSphere dim) := by
    intro z _
    change Wd.1 z = W.1 z-1
    rw [hWD z]
    ring
  have hE : EqOn E.1 (fun z => V.1 z-r*(ell.comp (ballRotationGeneratorL i j)) z) (standardSphere dim) := by
    intro z _
    change E.1 z = V.1 z-r*(ell.comp (ballRotationGeneratorL i j)) z
    rw [hVE z]
    ring
  have hFinite := norm_normalized_rotated_multiplier_commutator_finite hn i j hA hSym ell S b W Wd V E
    r C G F J hr.le hr₁ hC hG hF hJ hW hD hV hE
    (fun z hz => ⟨(hJetW z hz).1,(hJetW z hz).2,(hJetV z hz).1,(hJetV z hz).2⟩) hM
    hCa hCd hCb hCr hCl hWeak₀ hWeak hStrong₀ hStrongA
  let P := D.conormalRemainder
  let B := smoothSphereTraceMul b
  let K₀ := smoothSphereTraceRotation i j
  let Q := K₀*P-P*K₀
  let R := rotatedConormalRemainderData i j hA S r
  have hAC : EqOn D.coefficient A (ball (0:X dim) 1) :=
    D.coefficientEq.trans ((hFA.mono (ball_subset_ball (by norm_num : (1:ℝ) ≤ 5/4))).symm)
  have hRC (f : SmoothData dim) : P (smoothSphereTrace f) = smoothSphereTrace ((S f).remainder hA r) := by
    dsimp only [P]
    rw [D.conormalRemainder_apply]
    exact (smoothSphereTrace_eq_iff _ _).mpr (conormalTaylorSolutions_remainder_eqOn_of_coefficientEq
      D.smoothCoefficient hA D.ellipticCoefficient (D.solve f) (S f) hAC (fun _ _ => rfl) r)
  have hRP (f : SmoothData dim) : Q (smoothSphereTrace f) = smoothSphereTrace (R f) := by
    have hRot₀ (g : SmoothData dim) :
      K₀ (smoothSphereTrace g) = smoothSphereTrace (smoothRotationData i j g) :=
      smoothSphereTraceRotation_apply i j g
    change K₀ (P (smoothSphereTrace f))-P (K₀ (smoothSphereTrace f)) = _
    rw [hRC,hRot₀,hRot₀,hRC]
    rfl
  have hSymD (z : X dim) (hz : z ∈ ball (0:X dim) 1) : (D.coefficient z).IsSymm := by
    rw [hAC hz]
    exact hSym z hz
  have hP : SmoothTraceAdjoint hn P P :=
    smoothSphereTrace_remainder_symmetric hn D.smoothCoefficient D.ellipticCoefficient hSymD
      D.solve D.weight D.weightConormal r
  have hQ := SmoothTraceAdjoint.rotation_commutator_symmetric hn i j P hP
  have hRS (f g : SmoothData dim) :
      ⟪smoothSphereLift (R f).1 (R f).2,smoothSphereLift g.1 g.2⟫_ℝ =
        ⟪smoothSphereLift f.1 f.2,smoothSphereLift (R g).1 (R g).2⟫_ℝ := by
    have h := hQ (smoothSphereTrace f) (smoothSphereTrace g)
    change ⟪smoothSphereTraceL2 hn (Q (smoothSphereTrace f)),_⟫_ℝ =
      ⟪_,smoothSphereTraceL2 hn (Q (smoothSphereTrace g))⟫_ℝ at h
    simpa only [hRP,smoothSphereTraceL2_apply] using h
  have hHalf := norm_smooth_multiplier_commutator_half_of_finite hn b R hRS
    (L*J*r^2) (by positivity) hFinite
  have hMul (f : SmoothData dim) :
      B (smoothSphereTrace f) = smoothSphereTrace (smoothDataMul b f) := by
    apply Subtype.ext
    funext z
    dsimp only [B]
    rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply]
    rfl
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let f₀ : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  let X₀ := smoothSubtractData (R (smoothDataMul b f₀)) (smoothDataMul b (R f₀))
  have hComm : (Q*B-B*Q) (smoothSphereTrace f₀) = smoothSphereTrace X₀ := by
    change Q (B (smoothSphereTrace f₀))-B (Q (smoothSphereTrace f₀)) = _
    rw [hMul,hRP,hRP,hMul]
    rfl
  have hScale : smoothTraceAngularComm i j ((r^2)⁻¹ • P) = (r^2)⁻¹ • Q := by
    ext f
    simp only [smoothTraceAngularComm,LinearMap.sub_apply,Module.End.mul_apply,LinearMap.smul_apply,
      map_smul,smul_sub,Q,K₀]
  change ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num)
      ((smoothTraceAngularComm i j ((r^2)⁻¹ • P)*B-B*smoothTraceAngularComm i j ((r^2)⁻¹ • P))
        (smoothSphereTrace f₀))‖ ≤
      L*J*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (smoothSphereTrace f₀)‖
  rw [hScale]
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,map_smul,← smul_sub]
  rw [show Q (B (smoothSphereTrace f₀))-B (Q (smoothSphereTrace f₀)) = smoothSphereTrace X₀ from hComm,
    norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hr))]
  simp only [smoothSphereTraceSobolev_apply]
  exact (mul_le_mul_of_nonneg_left (hHalf f₀) (by positivity)).trans_eq (by field_simp [hr.ne'] <;> dsimp only [r] <;> ring)

end CalderonN
