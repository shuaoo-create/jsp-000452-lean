import MinimumExposure

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- A witnessed edge partition into a matching and a graph of maximum degree at most j-1. -/
def admits_matching_remainder (H : SimpleGraph X) (j : ℕ) : Prop :=
  ∃ M : H.Subgraph, M.IsMatching ∧
    ∀ v, Nat.card ((H \ M.spanningCoe).neighborSet v) ≤ j-1


/-- The red graph is the matching's complement, and its own complement recovers
the very same matching as a spanning graph. -/
theorem admits_matching_remainder_iff_partition (H : SimpleGraph X) (j : ℕ) :
    admits_matching_remainder H j ↔
      ∃ R : SimpleGraph X, R ≤ H ∧ (∀ v, Nat.card (R.neighborSet v) ≤ j-1) ∧
        ∃ M : H.Subgraph, M.IsMatching ∧ H \ R = M.spanningCoe := by
  have invol (C : SimpleGraph X) (h : C ≤ H) : H \ (H \ C) = C := by
    ext v w
    simp only [sdiff_adj]
    have incl : C.Adj v w → H.Adj v w := fun e => h e
    tauto
  constructor
  · rintro ⟨M,hm,cap⟩
    exact ⟨_,sdiff_le,cap,M,hm,invol M.spanningCoe M.spanningCoe_le⟩
  · rintro ⟨R,hR,cap,M,hm,eq⟩
    refine ⟨M,hm,?_⟩
    rwa [← eq,invol R hR]

/-- Cardinalities of actual vertex deletions admitting the required partition off the cut. -/
def feasibleDeletionCounts (G : SimpleGraph X) (j : ℕ) : Set ℕ :=
  {k | ∃ U : Set X, admits_matching_remainder (G.induce Uᶜ) j ∧ U.ncard = k}

noncomputable def deletionBudget (G : SimpleGraph X) (j : ℕ) : ℕ :=
  sInf (feasibleDeletionCounts G j)

private theorem feasibleDeletionCounts_nonempty (G : SimpleGraph X) (j : ℕ) :
    (feasibleDeletionCounts G j).Nonempty := by
  let U := (Set.univ : Set X)
  refine ⟨_,U,?_,rfl⟩
  refine ⟨⊥,?_,?_⟩
  · intro v hv
    exact False.elim hv
  · intro v
    exact False.elim (v.property (Set.mem_univ _))

theorem deletionBudget_attained (G : SimpleGraph X) (j : ℕ) :
    ∃ U : Set X, admits_matching_remainder (G.induce Uᶜ) j ∧ U.ncard = deletionBudget G j :=
  Nat.sInf_mem (feasibleDeletionCounts_nonempty G j)

theorem deletionBudget_le_of_witness (G : SimpleGraph X) (j : ℕ) (U : Set X)
    (witness : admits_matching_remainder (G.induce Uᶜ) j) :
    deletionBudget G j ≤ U.ncard :=
  Nat.sInf_le (show U.ncard ∈ feasibleDeletionCounts G j from ⟨U,witness,rfl⟩)

/-- Deleting the matching edges strictly lowers the degree at every covered vertex. -/
theorem admits_remainder_of_full_cover [Finite X] (H : SimpleGraph X) (D : ℕ) (pos : 1≤D)
    (bound : ∀ v, Nat.card (H.neighborSet v) ≤ D)
    (M : H.Subgraph) (hm : M.IsMatching) (covers : ∀ v, Nat.card (H.neighborSet v) = D → v∈M.verts) :
    admits_matching_remainder H D := by
  refine ⟨M,hm,fun v => ?_⟩
  have sub : (H \ M.spanningCoe).neighborSet v ⊆ H.neighborSet v := fun _ h => h.1
  have lt : Nat.card ((H \ M.spanningCoe).neighborSet v) < D := by
    by_cases eq : Nat.card (H.neighborSet v) = D
    · obtain ⟨w,edge,_⟩ := hm (covers v eq)
      have strict : (H \ M.spanningCoe).neighborSet v ⊂ H.neighborSet v :=
        ⟨sub, fun back => (back (M.adj_sub edge)).2 edge⟩
      exact (show Nat.card ((H \ M.spanningCoe).neighborSet v) < Nat.card (H.neighborSet v) from
        Set.ncard_lt_ncard strict).trans_eq eq
    · have le : Nat.card ((H \ M.spanningCoe).neighborSet v) ≤ Nat.card (H.neighborSet v) :=
        Set.ncard_le_ncard sub
      exact le.trans_lt (lt_of_le_of_ne (bound v) eq)
  have atLeast : D-1+1=D := Nat.sub_add_cancel pos
  omega

theorem matching_remainder_off_exposed [Finite X] (G : SimpleGraph X) (M : G.Subgraph)
    (hm : M.IsMatching) (D : ℕ) (pos : 1≤D) (bound : ∀ v, Nat.card (G.neighborSet v) ≤ D) :
    admits_matching_remainder (G.induce (exposedFull G M D)ᶜ) D := by
  obtain ⟨N,hN,covers⟩ := exposed_compl_cover G M hm D bound
  exact admits_remainder_of_full_cover _ D pos
    (fun v => (induced_neighbor_count_le G _ v).trans (bound v.val)) N hN covers

/-- Liu's deletion reserve kappa_D is bounded by minimum full-degree exposure. -/
theorem deletionBudget_le_minimumExposure [Finite X] (G : SimpleGraph X) (D : ℕ) (pos : 1≤D)
    (bound : ∀ v, Nat.card (G.neighborSet v) ≤ D) :
    deletionBudget G D ≤ minimumExposure G D := by
  obtain ⟨M,hm,_,attained⟩ := minimumExposure_attained G D
  exact (deletionBudget_le_of_witness G D (exposedFull G M D)
    (matching_remainder_off_exposed G M hm D pos bound)).trans_eq attained

#print axioms admits_matching_remainder_iff_partition
#print axioms deletionBudget_attained
#print axioms admits_remainder_of_full_cover
#print axioms matching_remainder_off_exposed
#print axioms deletionBudget_le_minimumExposure
end JSP452Audit.StarHost
