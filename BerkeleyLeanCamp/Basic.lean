import Mathlib

open Topology Set

noncomputable section

def ZeroDimModel : Type := (Fin 0 → ℝ)
    deriving TopologicalSpace, Unique, Subsingleton

section

variable {M : Type} [TopologicalSpace M] [ChartedSpace ZeroDimModel M]

lemma exists_chart_at (x : M) : ∃ (U : Set M) (_ : U ≃ₜ ZeroDimModel),
  IsOpen U ∧ x ∈ U := by
  let chart := chartAt ZeroDimModel x
  use chart.source
  let g := PartialHomeomorph.toHomeomorphSourceTarget chart
  let y : Unique chart.target := {
    default := ⟨chart x, by exact mem_chart_target ZeroDimModel x⟩
    uniq := by
      intro a
      ext
      apply Subsingleton.elim
  }
  let h : chart.target ≃ₜ ZeroDimModel := Homeomorph.homeomorphOfUnique chart.target ZeroDimModel

  let φ := g.trans h
  constructor
  · constructor
    · exact chart.open_source
    · exact ChartedSpace.mem_chart_source x
  · exact φ

theorem zero_dim_manifold_discrete : DiscreteTopology M := by
  rw [← singletons_open_iff_discrete]
  intro a
  have : Unique ZeroDimModel := inferInstance
  obtain ⟨U, φ, h1, h2⟩ := exists_chart_at a
  have : Unique U := φ.unique
  suffices {a} = U by rwa [this]
  apply Set.eq_of_subset_of_card_le
  exact Set.singleton_subset_iff.mpr h2
  simp only [Set.card_singleton]
  exact Nat.factorial_eq_one.mp rfl

variable [SecondCountableTopology M]

theorem zero_dim_manifold_countable : Countable M := by
  have h : DiscreteTopology M := zero_dim_manifold_discrete
  exact countable_of_Lindelof_of_discrete

end

section

variable {M : Type} [TopologicalSpace M] [DiscreteTopology M] [Countable M]

open PUnit

def zeroDimMfd : ChartedSpace ZeroDimModel M :=
{ atlas       := Set.univ,
  chartAt     := λ x ↦
  { toFun              := λ _ ↦ (default : ZeroDimModel),
    invFun             := λ _ ↦ x,
    source             := {x},
    target             := Set.univ,
    continuousOn_toFun := by
      simp,
    continuousOn_invFun := by
      exact continuousOn_const,
    left_inv'          := by
      intro y hy; rcases hy with rfl; rfl,
    right_inv'         := by
      intro u hu; simpa using Subsingleton.elim (default : ZeroDimModel) u,
    open_source        := isOpen_discrete _,
    open_target        := isOpen_univ,
    map_source'        := by
      intro y hy; simp,
    map_target'        := by
      intro u hu; simp  },
  mem_chart_source := by
    intro x; simp,
  chart_mem_atlas := by
    intro x; simp }

end
