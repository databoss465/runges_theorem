import Mathlib
import Runge.Basic
import Runge.GridContour

open Complex Set Finset Metric RatFunc

-- For any compact Set K and Disjoint set U, ∃ x₀ ∈ K, ∀ x ∈ K infDist x₀ U ≤ infDist x U
lemma point_of_least_sep {K U : Set ℂ} (hK : IsCompact K) (hKU : Disjoint K U) :
  ∃ x₀ ∈ K, ∀ x ∈ K, infDist x₀ U ≤ infDist x U := by sorry

lemma square_dist {z x y : ℂ} {δ : ℝ} (hδ : 0 < δ) (hx : x ∈ closed_square z δ) (hy : y ∈ closed_square z δ) :
  dist x y ≤ 2 * δ := by
  sorry

lemma grid_contour_sep (K : Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) :
  ∀ x ∈ (GridContourSet K hδ), ∃ y ∈ K, dist x y < 2 * δ := by
  intro x hx
  let ε := 2 * δ
  have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
  let V := (Mesh (Box K hε) hδ).filter (fun v ↦ ((closed_square v δ) ∩ K).Nonempty)
  let edges := (DirectedEdgeSetOriented K hδ V)
  have h : GridContourSet K hδ = ⋃ e ∈ edges, edgeInterval e := by rfl
  rw [h, mem_iUnion] at hx
  obtain ⟨⟨z,w⟩, interval, he', hx⟩ := hx
  simp at he'
  let ⟨h, he⟩ := he'
  rw [←he] at hx
  -- A shit ton of by_cases to show that they share a square. Then slap the above lemma on it.
  by_cases h₁ : z.re = w.re
  · apply mem_directed_edge_set at h
    let ⟨ha, hb⟩ := h
    simp [ContourGraph] at h
    unfold edgeInterval at hx
    simp [h₁] at hx
    by_cases h₂ : z.im < w.im
    · have hzw : w.im = z.im + δ := by
        rw [norm_def (z -w), normSq_apply, sub_re, h₁] at ha
        simp at ha
        rw [Real.sqrt_mul_self_eq_abs, abs_eq] at ha
        cases ha
        · linarith
        · linarith
        exact LT.lt.le hδ
      rw [min_eq_left_of_lt h₂, max_eq_right_of_lt h₂] at hx
      unfold one_common_square at hb
      simp [ha] at hb
      sorry
    · sorry

  · by_cases h₂ : z.im = w.im
    · unfold edgeInterval at hx
      simp [h₁, h₂] at hx
      sorry
    · sorry


-- CIF_GridContour
lemma DifferentiableOn.grid_contour_integral_sub_inv_smul {Ω K : Set ℂ} {f : ℂ → ℂ}
  (hΩ : IsOpen Ω) (hΩK : K ⊆ Ω) [Gridable K] (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∀ a ∈ K, GridContourIntegral (fun z ↦ (z - a)⁻¹ • f z) K hδ = (2 * π * I) • f a := by sorry


/-- **Separation Lemma**: Given a compact set `K` and a function `f : ℂ → ℂ` that is complex differentiable on
an open set `Ω`, containing `K`, there exists a `δ > 0` such that the integral of `(z - a)⁻¹ • f(z)` over the
grid contour of `K` is equal to `2 * π * I * f(a)`, where `a` is a point in `K` and the grid contour is
contained in `Ω \ K`.
-/
theorem separation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} (hΩ : IsOpen Ω) (hΩ₁ : Ωᶜ.Nonempty) (hΩK : K ⊆ Ω) [Gridable K]
  (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∃ (δ : ℝ) (hδ : 0 < δ), (∀ a ∈ K, GridContourIntegral (fun z ↦ (z - a)⁻¹ • f z) K hδ = (2 * π * I) • f a) ∧
  (GridContourSet K hδ ⊆ Ω \ K) := by
  have hΩK' : Disjoint K Ωᶜ := disjoint_compl_right_iff_subset.mpr hΩK
  obtain ⟨x₀, hx₀, hKx₀⟩ := point_of_least_sep Gridable.hK hΩK'
  let d : ℝ := infDist x₀ Ωᶜ / 2
  have hd : 0 < d := by
    apply half_pos
    rw [← IsClosed.not_mem_iff_infDist_pos (isClosed_compl_iff.mpr hΩ) hΩ₁, not_mem_compl_iff]
    exact mem_of_subset_of_mem hΩK hx₀

  have hΓK : Disjoint K (GridContourSet K hd) := by
        rw [disjoint_iff_inter_eq_empty, inter_comm]
        let ε := 2 * d
        have hε : 0 < ε := by apply mul_pos; linarith; exact hd
        let V := (Mesh (Box K hε) hd).filter (fun v ↦ ((closed_square v d) ∩ K).Nonempty)
        let edges := (DirectedEdgeSetOriented K hd V)
        have h : GridContourSet K hd = ⋃ e ∈ edges, edgeInterval e := by rfl
        rw [h, iUnion_inter K, iUnion_eq_empty]
        intro (z,w)
        rw [iUnion_inter, iUnion_eq_empty]
        have h' {z w : ℂ} (hzw : (z,w) ∈ edges) : edgeInterval (z,w) ∩ K = ∅ := by
          unfold edges at hzw
          apply mem_directed_edge_set at hzw
          simp [ContourGraph] at hzw
          apply (edge_interval_inter_empty K hd hzw.2)
        exact h'

  have hΓδ : ∀ x ∈ (GridContourSet K hd), ∃ y ∈ K, dist x y < infDist x₀ Ωᶜ := by
    have h2d : infDist x₀ Ωᶜ = 2 * d := by unfold d; ring
    rw [h2d]
    exact grid_contour_sep K hd

  use d, hd
  constructor
  -- CIF Statement
  · exact DifferentiableOn.grid_contour_integral_sub_inv_smul hΩ hΩK hf

  -- Contour Set Statement
  · rw [diff_eq, Set.subset_inter_iff, and_comm]
    constructor

    -- Γ ⊆ Kᶜ
    · exact subset_compl_iff_disjoint_left.mpr hΓK

    -- Γ ⊆ Ω
    · rw [Set.subset_def]
      intro x hx
      rw [←compl_compl Ω, Set.mem_compl_iff]
      by_contra h_contra
      obtain ⟨y, hy, hxy⟩ := hΓδ x hx
      have h : infDist x₀ Ωᶜ ≤ dist x y := by
        specialize hKx₀ y hy
        have h : infDist y Ωᶜ ≤ dist y x := infDist_le_dist_of_mem h_contra
        rw [dist_comm] at h
        linarith
      linarith [hxy, h]

-- Two approaches to prove separation theorem
-- TODO: Every connected component of GridContour is a cycle => need this to show that GridContour is a "Path"
-- TODO: Every GridContour is a union of squares => need this for CIF on GridContour

-- TODO : Show that every edge is contained in `Ω` => The argument is that `d(K, Γ)` is less than  `d(K, Ωᶜ)`

-- Needs work!
theorem approximation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} {δ : ℝ} (hΩ : IsOpen Ω)
  (hΩK : K ⊆ Ω) [Gridable K] (hδ : 0 < δ) (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∃ (R : RatFunc ℂ), (only_poles_in' (GridContourSet K hδ) R) ∧
  (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε) := by sorry
