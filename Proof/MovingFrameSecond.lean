import Proof.MovingDerivativeRules
import Proof.HorizontalFiberBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres

def movingDerivativeBaseL (g : MetricField) (A : TraceAdjoint) (φ : Field) (y w : X) : X →L[ℝ] ℂ :=
  ∑ k : I,(EuclideanSpace.proj (𝕜:=ℝ) k).smulRight (traceDerivative g A k φ (y,w))

theorem movingDerivativeBaseL_apply (g : MetricField) (A : TraceAdjoint) (φ : Field) (y w a : X) :
    movingDerivativeBaseL g A φ y w a = ∑ k : I,a k • traceDerivative g A k φ (y,w) := by
  simp only [movingDerivativeBaseL,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]

def frameTraceDerivative (g : MetricField) (A : TraceAdjoint) (e : Frame) (i : I) (φ : Field) : Field :=
  fun p => movingDerivativeBaseL g A φ p.1 p.2 (e p.1 i)

theorem frameTraceDerivative_apply (g : MetricField) (A : TraceAdjoint) (e : Frame) (i : I) (φ : Field) (p : X × X) :
    frameTraceDerivative g A e i φ p = ∑ k : I,e p.1 i k • traceDerivative g A k φ p := by
  exact movingDerivativeBaseL_apply g A φ p.1 p.2 (e p.1 i)

theorem coordDeriv_vector_component (F : X → X) {y : X} (hF : DifferentiableAt ℝ F y) (a b : I) :
    coordDeriv a (fun x => F x b) y = (fderiv ℝ F y (axis a)) b := by
  have h := (EuclideanSpace.proj (𝕜:=ℝ) b).hasFDerivAt.comp y hF.hasFDerivAt
  have hEq : (fun x => F x b)=(EuclideanSpace.proj (𝕜:=ℝ) b) ∘ F := by
    funext x
    simp only [Function.comp_apply,PiLp.proj_apply]
  unfold coordDeriv
  rw [hEq,h.fderiv]
  rfl

theorem frame_derivative_component (e : Frame) {y : X}
    (he : ∀ j,DifferentiableAt ℝ (fun x => e x j) y) (i j b : I) :
    (∑ a : I,e y i a*coordDeriv a (fun x => e x j b) y) =
      (fderiv ℝ (fun x => e x j) y (e y i)) b := by
  have h := linear_axis_expansion ((EuclideanSpace.proj (𝕜:=ℝ) b).comp
    (fderiv ℝ (fun x => e x j) y)) (e y i)
  simpa only [ContinuousLinearMap.comp_apply,PiLp.proj_apply,
    coordDeriv_vector_component _ (he j)] using h.symm

theorem frame_connection_reconstruct (g : MetricField) (e : Frame) (y a : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (j : I) :
    (∑ k : I,frameConnectionCoefficient g e y a j k • e y k) =
      covariantFrameVector g e y a j := by
  simpa only [frameBasis_apply,frameBasis_repr,frameConnectionCoefficient] using
    (frameBasis g e y hframe).sum_repr (covariantFrameVector g e y a j)

theorem Admissible.frameTraceDerivative_second_expansion {Y Ω : Set X} (hY : IsOpen Y)
    (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ)) (i j : I)
    {y : X} (hy : y ∈ Y) {w : X} (hw : w ∈ sphereAt d.γ y) :
    frameTraceDerivative d.γ d.adjoint d.frame i (frameTraceDerivative d.γ d.adjoint d.frame j φ) (y,w) =
      movingDerivativeBaseL d.γ d.adjoint φ y w (fderiv ℝ (fun x => d.frame x j) y (d.frame y i)) +
      ∑ a : I,∑ b : I,(d.frame y i a*d.frame y j b) •
        traceDerivative d.γ d.adjoint a (traceDerivative d.γ d.adjoint b φ) (y,w) := by
  have h : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y :=
    fun j => (hd.1.2.2.2.2.2.2.1 j).mono hSub
  have hc (j b : I) : ContDiffOn ℝ ∞ (fun x => d.frame x j b) Y :=
    (EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.comp_contDiffOn (he j)
  have hW (b : I) := smoothNear_traceDerivative hY h hK hd.2.2.2.1 hφ b
  have hTerms (b : I) : smoothNear (fun p : X × X => d.frame p.1 j b •
      traceDerivative d.γ d.adjoint b φ p) (bundle Y d.γ) := (hW b).smul_base hY (hc j b)
  have hInner : frameTraceDerivative d.γ d.adjoint d.frame j φ =
      (fun p => ∑ b : I,d.frame p.1 j b • traceDerivative d.γ d.adjoint b φ p) := by
    funext p
    exact frameTraceDerivative_apply _ _ _ _ _ _
  have hEach (a : I) : traceDerivative d.γ d.adjoint a
      (frameTraceDerivative d.γ d.adjoint d.frame j φ) (y,w) =
      ∑ b : I,(coordDeriv a (fun x => d.frame x j b) y •
        traceDerivative d.γ d.adjoint b φ (y,w)+d.frame y j b •
        traceDerivative d.γ d.adjoint a (traceDerivative d.γ d.adjoint b φ) (y,w)) := by
    rw [hInner,hd.traceDerivative_finset_sum hY Finset.univ _ (fun b _ => hTerms b) a hy hw]
    apply Finset.sum_congr rfl
    intro b _
    exact hd.traceDerivative_base_smul hY (hc j b) (hW b) a hy hw
  rw [frameTraceDerivative_apply]
  simp_rw [hEach,Finset.smul_sum,smul_add,smul_smul,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul,movingDerivativeBaseL_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [frame_derivative_component d.frame (fun j =>
    ((he j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i j b]

theorem movingDerivativeBaseL_connection (g : MetricField) (A : TraceAdjoint) (φ : Field)
    (y w a v : X) :
    movingDerivativeBaseL g A φ y w (connection g y a v) =
      ∑ i : I,∑ j : I,(a i*v j) •
        (∑ k : I,christoffel g y k i j • traceDerivative g A k φ (y,w)) := by
  conv_lhs => rw [← connectionBilinear_apply,← axis_expansion a,← axis_expansion v]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    connectionBilinear_apply,Finset.smul_sum,smul_smul]
  simp only [movingDerivativeBaseL_apply,connection_axis_components]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ring

def covariantTraceSecond (g : MetricField) (A : TraceAdjoint) (i j : I) (φ : Field) : Field :=
  fun p => traceDerivative g A i (traceDerivative g A j φ) p -
    ∑ k : I,christoffel g p.1 k i j • traceDerivative g A k φ p

def frameCovariantTraceSecond (g : MetricField) (A : TraceAdjoint) (e : Frame)
    (i j : I) (φ : Field) : Field :=
  fun p => frameTraceDerivative g A e i (frameTraceDerivative g A e j φ) p -
    ∑ k : I,frameConnectionCoefficient g e p.1 (e p.1 i) j k • frameTraceDerivative g A e k φ p

/-- All derivatives of the arbitrary frame cancel with its actual connection.
    No estimate or additional regularity budget for the frame is used. -/
theorem Admissible.frameCovariantTraceSecond_eq {Y Ω : Set X} (hY : IsOpen Y)
    (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ)) (i j : I)
    {y : X} (hy : y ∈ Y) {w : X} (hw : w ∈ sphereAt d.γ y) :
    frameCovariantTraceSecond d.γ d.adjoint d.frame i j φ (y,w) =
      ∑ a : I,∑ b : I,(d.frame y i a*d.frame y j b) • covariantTraceSecond d.γ d.adjoint a b φ (y,w) := by
  have hframe := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hConn := congrArg (movingDerivativeBaseL d.γ d.adjoint φ y w)
    (frame_connection_reconstruct d.γ d.frame y (d.frame y i) hframe j)
  simp only [map_sum,map_smul] at hConn
  change (∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
      frameTraceDerivative d.γ d.adjoint d.frame k φ (y,w)) =
    movingDerivativeBaseL d.γ d.adjoint φ y w (covariantFrameVector d.γ d.frame y (d.frame y i) j) at hConn
  unfold frameCovariantTraceSecond
  rw [hd.frameTraceDerivative_second_expansion hY hSub hK hφ i j hy hw,hConn,
    covariantFrameVector,map_add]
  calc
    _ = (∑ a : I,∑ b : I,(d.frame y i a*d.frame y j b) •
        traceDerivative d.γ d.adjoint a (traceDerivative d.γ d.adjoint b φ) (y,w)) -
        movingDerivativeBaseL d.γ d.adjoint φ y w (connection d.γ y (d.frame y i) (d.frame y j)) := by abel
    _ = _ := by
      rw [movingDerivativeBaseL_connection]
      simp only [covariantTraceSecond,smul_sub,Finset.sum_sub_distrib]

end ShrinkingSpheres
