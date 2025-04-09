-- This module serves as the root of the `Runge` library.
-- Import modules here that should be built as part of the library.
import Mathlib
import Runge.Basic
import Runge.GridContour
import Runge.SeparationLemma

/-- **Runge's Theorem**
Suppose `Ω` is an open set in ℂ, `K` is a compact subset and `E` is set which intersects every connected component of
`ℂ_infty \ K`. If `f` is a function which is complex differentiable on `Ω`, then for every `ε > 0` there exists a
rational function `R` such that `∀ x ∈ Ω, |f(x) - R(x)| < ε`.
-/
theorem runges_theorem {Ω K : Set ℂ} {E : Set (OnePoint ℂ)} {f : ℂ → ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hE : ∀ z ∈  (↑K)ᶜ, connectedComponentIn (↑K)ᶜ z ∩ E ≠ ∅) (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) : ∀ ε > 0,
    ∃ R : RatFunc ℂ, (only_poles_in' E R) ∧ (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε) := by

    intro ε hε
    have hε' : ε / 2 > 0 := by
        apply div_pos
        · exact hε
        · exact zero_lt_two

    /-obtain ⟨rγ, hγ⟩ := separation_lemma hK kΩ hf
    h_total:= approximation_lemma γ K f
    specialize h_total ε/2 hε'
    Then h_total becomes ∃ R : RatFunc ℂ, (only_poles_in' (bdry γ)) ∧ (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε/2
    obtain ⟨R, ⟨_, hR₁⟩ := hR
    -/

    obtain R : RatFunc ℂ := by sorry
    have hR₁ : ∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε / 2 := by sorry

    -- TODO: Define B E K
    /-Define B E K := {f : ℂ → ℂ | (ContinuousOn f K) ∧ ( ∀ ε > 0, ∃ R : RatFunc ℂ, (only_poles_in' E R) ∧ (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε)
    Show that B E K is a closed subalgebra ?
    Show that ∀ a ∈ ℂ \ K, (z - a)⁻¹ ∈ B E K

    Show that R ∈ B E K since it is a closed subalgebra
    R ∈ B E K ↔ hR'
    Show that R ∈ B E K → f ∈ B E K

    Do I need to??
    -/

    have hR' : ∀ ε > 0, ∃ R' : RatFunc ℂ, (only_poles_in' E R') ∧
            (∀ x ∈ K, ‖R.eval (RingHom.id ℂ) x - R'.eval (RingHom.id ℂ) x‖ < ε) := by sorry

    specialize hR' (ε / 2) hε'
    obtain ⟨R', hR'₁⟩ := hR'
    use R'
    constructor
    · exact hR'₁.1
    · have hR'' : ∀ x ∈ K, ‖f x - R'.eval (RingHom.id ℂ) x‖ < ε := by
        intro x hx
        calc
        ‖f x - RatFunc.eval (RingHom.id ℂ) x R'‖
            = ‖f x - R.eval (RingHom.id ℂ) x + R.eval (RingHom.id ℂ) x - R'.eval (RingHom.id ℂ) x‖ := by
            rw [←sub_add_sub_cancel (f x) (R.eval (RingHom.id ℂ) x) (R'.eval (RingHom.id ℂ) x), ←add_sub_assoc]
        _  ≤ ‖f x - R.eval (RingHom.id ℂ) x‖ + ‖R.eval (RingHom.id ℂ) x - R'.eval (RingHom.id ℂ) x‖ := by
            rw [add_sub_assoc]
            apply norm_add_le
        _ < ε / 2 + ε / 2 := by
            apply add_lt_add
            · exact hR₁ x hx
            · exact hR'₁.2 x hx
        _ = ε := by apply add_halves
      exact hR''
