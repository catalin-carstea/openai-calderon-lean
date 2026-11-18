import Proof.ScalarSecondCovariantFirstForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open scoped InnerProductSpace
namespace ShrinkingSpheres

/-- The third-base scalar remainder is controlled by the energy after
its genuine Green reduction. Curvature is only applied as a first-order
angular operator; no derivative or endomorphism of curvature is used. -/
theorem scalar_curvature_triple_point_bound_of_value_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : F) (va vb vc : E) (Kab Kcb Kac : F →L[ℝ] E)
    (q qa qb qc μ Q Q0 CR ε β : ℝ)
    (hμ : 0 ≤ μ) (hQ : 0 ≤ Q) (hQ0 : 0 ≤ Q0) (hCR : 0 ≤ CR) (hβ : 1 ≤ β)
    (hKab : ‖Kab‖ ≤ CR) (hKcb : ‖Kcb‖ ≤ CR) (hKac : ‖Kac‖ ≤ CR)
    (hq : |q| ≤ μ*Q0*ε^2)
    (hqa : |qa| ≤ μ*Q*ε^2/β^2) (hqb : |qb| ≤ μ*Q*ε^2/β^2) (hqc : |qc| ≤ μ*Q*ε^2/β^2) :
    |-qa*⟪vb,vc⟫_ℝ-qb*⟪va,vc⟫_ℝ+qc*⟪va,vb⟫_ℝ+
      q*⟪Kab u,vc⟫_ℝ+q*⟪Kcb u,va⟫_ℝ-q*⟪Kac u,vb⟫_ℝ| ≤
    (3*Q+3*Q0*CR)*μ*ε^2*(β⁻¹*(‖va‖^2+‖vb‖^2+‖vc‖^2)+β*‖u‖^2) := by
  let G := ‖va‖^2+‖vb‖^2+‖vc‖^2
  let En := β⁻¹*G+β*‖u‖^2
  let A := μ*Q*ε^2*En
  let B := μ*Q0*CR*ε^2*En
  have hβ0 : 0 < β := zero_lt_one.trans_le hβ
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hva : ‖va‖^2 ≤ G := by dsimp only [G];nlinarith only [sq_nonneg ‖vb‖,sq_nonneg ‖vc‖]
  have hvb : ‖vb‖^2 ≤ G := by dsimp only [G];nlinarith only [sq_nonneg ‖va‖,sq_nonneg ‖vc‖]
  have hvc : ‖vc‖^2 ≤ G := by dsimp only [G];nlinarith only [sq_nonneg ‖va‖,sq_nonneg ‖vb‖]
  have hPair (v w : E) (hv : ‖v‖^2 ≤ G) (hw : ‖w‖^2 ≤ G) : |⟪v,w⟫_ℝ| ≤ G := by
    apply (abs_real_inner_le_norm v w).trans
    nlinarith only [hv,hw,sq_nonneg (‖v‖-‖w‖)]
  have hGrad (z : ℝ) (hz : |z| ≤ μ*Q*ε^2/β^2) (v w : E)
      (hv : ‖v‖^2 ≤ G) (hw : ‖w‖^2 ≤ G) : |z*⟪v,w⟫_ℝ| ≤ A := by
    rw [abs_mul]
    calc
      _ ≤ (μ*Q*ε^2/β^2)*G := mul_le_mul hz (hPair v w hv hw) (abs_nonneg _) (by positivity)
      _ ≤ (μ*Q*ε^2/β)*G := by gcongr;nlinarith only [hβ]
      _ = (μ*Q*ε^2)*(β⁻¹*G) := by ring
      _ ≤ A := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg hβ0.le (sq_nonneg ‖u‖))) (by positivity)
  have hCurv (K : F →L[ℝ] E) (hK : ‖K‖ ≤ CR) (v : E) (hv : ‖v‖^2 ≤ G) :
      |q*⟪K u,v⟫_ℝ| ≤ B := by
    have hN : |⟪K u,v⟫_ℝ| ≤ CR*‖u‖*‖v‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        ((K.le_opNorm u).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg u))) (norm_nonneg v))
    rw [abs_mul]
    calc
      _ ≤ (μ*Q0*ε^2)*(CR*‖u‖*‖v‖) := mul_le_mul hq hN (abs_nonneg _) (by positivity)
      _ = (μ*Q0*CR*ε^2)*(‖v‖*‖u‖) := by ring
      _ ≤ (μ*Q0*CR*ε^2)*(β⁻¹*‖v‖^2+β*‖u‖^2) :=
        mul_le_mul_of_nonneg_left (weighted_product_le ‖v‖ ‖u‖ β hβ0) (by positivity)
      _ ≤ B := by dsimp only [B,En];gcongr
  have h1 := hGrad qa hqa vb vc hvb hvc
  have h2 := hGrad qb hqb va vc hva hvc
  have h3 := hGrad qc hqc va vb hva hvb
  have h4 := hCurv Kab hKab vc hvc
  have h5 := hCurv Kcb hKcb va hva
  have h6 := hCurv Kac hKac vb hvb
  have hAbs : |-qa*⟪vb,vc⟫_ℝ-qb*⟪va,vc⟫_ℝ+qc*⟪va,vb⟫_ℝ+
      q*⟪Kab u,vc⟫_ℝ+q*⟪Kcb u,va⟫_ℝ-q*⟪Kac u,vb⟫_ℝ| ≤ 3*A+3*B := by
    apply abs_le.mpr
    constructor <;> linarith only [(abs_le.mp h1).1,(abs_le.mp h1).2,(abs_le.mp h2).1,(abs_le.mp h2).2,
      (abs_le.mp h3).1,(abs_le.mp h3).2,(abs_le.mp h4).1,(abs_le.mp h4).2,
      (abs_le.mp h5).1,(abs_le.mp h5).2,(abs_le.mp h6).1,(abs_le.mp h6).2]
  exact hAbs.trans_eq (by dsimp only [A,B,En,G];ring)

/-- Original beta-cubed curvature specialization; public statement preserved. -/
theorem scalar_curvature_triple_point_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : F) (va vb vc : E) (Kab Kcb Kac : F →L[ℝ] E)
    (q qa qb qc μ Q Q0 CR ε β : ℝ)
    (hμ : 0 ≤ μ) (hQ : 0 ≤ Q) (hQ0 : 0 ≤ Q0) (hCR : 0 ≤ CR) (hβ : 1 ≤ β)
    (hKab : ‖Kab‖ ≤ CR) (hKcb : ‖Kcb‖ ≤ CR) (hKac : ‖Kac‖ ≤ CR)
    (hq : |q| ≤ μ*Q0*ε^2/β^3)
    (hqa : |qa| ≤ μ*Q*ε^2/β^2) (hqb : |qb| ≤ μ*Q*ε^2/β^2) (hqc : |qc| ≤ μ*Q*ε^2/β^2) :
    |-qa*⟪vb,vc⟫_ℝ-qb*⟪va,vc⟫_ℝ+qc*⟪va,vb⟫_ℝ+
      q*⟪Kab u,vc⟫_ℝ+q*⟪Kcb u,va⟫_ℝ-q*⟪Kac u,vb⟫_ℝ| ≤
    (3*Q+3*Q0*CR)*μ*ε^2*(β⁻¹*(‖va‖^2+‖vb‖^2+‖vc‖^2)+β*‖u‖^2) := by
  have hq0 : |q| ≤ μ*Q0*ε^2 := hq.trans (div_le_self (by positivity) (one_le_pow₀ hβ))
  exact scalar_curvature_triple_point_bound_of_value_bound u va vb vc Kab Kcb Kac
    q qa qb qc μ Q Q0 CR ε β hμ hQ hQ0 hCR hβ hKab hKcb hKac hq0 hqa hqb hqc

end ShrinkingSpheres
