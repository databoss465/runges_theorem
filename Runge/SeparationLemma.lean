import Mathlib
import Runge.GridContour

open Complex Set Finset SimpleGraph



/-- **Separation Lemma**: Given a compact set `K` and a function `f : ℂ → ℂ` that is complex differentiable on
an open set `Ω`, containing `K`, there exists a `δ > 0` such that the integral of `(z - a)⁻¹ • f(z)` over the
grid contour of `K` is equal to `2 * π * I * f(a)`, where `a` is a point in `K` and the grid contour is
contained in `Ω \ K`.
-/
theorem separation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} (hΩ : IsOpen Ω) (hΩK : K ⊆ Ω) [Gridable K]
  (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∃ (δ : ℝ) (hδ : 0 < δ), (∀ a ∈ K, GridContourIntegral (fun z ↦ (z - a)⁻¹ • f z) K hδ = 2 * π * I * f a) ∧
  (GridContourSet K hδ ⊆ Ω \ K) := by
  let d : ℝ := sorry
  have hd : 0 < d := sorry
  use d, hd
  constructor
  -- CIF Statement
  · intro a ha
    sorry

  -- Contour Set Statement
  · rw [diff_eq, subset_inter_iff]
    constructor
    · rw [←compl_compl Ω, subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
      -- d(x, K) < d(K, Ωᶜ) => 0 < d(x, Ωᶜ)
      -- Triangle inequality => d(K, Ωᶜ) ≤ d(x, Ωᶜ) + d(x, K)
      sorry
    · rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
      let ε := 2 * d
      have hε : 0 < ε := by apply mul_pos; linarith; exact hd
      let V := (Mesh (Box K hε) hd).filter (fun v ↦ ((closed_square v d) ∩ K).Nonempty)
      let edges := (DirectedEdgeSetOriented K hd V)
      have h : GridContourSet K hd = ⋃ e ∈ edges, edgeInterval e := by rfl
      rw [h, iUnion_inter K, iUnion_eq_empty]
      intro (z,w)
      rw [iUnion_inter, iUnion_eq_empty]
      have h' {z w : ℂ} (hzw : (z,w) ∈ edges) : edgeInterval (z,w) ∩ K = ∅ := by
        sorry
      exact h'


-- Two approaches to prove separation theorem
-- TODO: Every connected component of GridContour is a cycle => need this to show that GridContour is a "Path"
-- TODO: Every GridContour is a union of squares => need this for CIF on GridContour

-- TODO : Show that every edge is contained in `Ω` => The argument is that `d(K, Γ)` is less than  `d(K, Ωᶜ)`
