import CriticalPeak
import RowEnergy
import FiniteRowDeletion

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A live strict row whose every one-vertex descendant already pays the
    next-row budget has exactly one missing edge and a sharp degree ceiling. -/
theorem strict_local_normal {X : Type*} [Finite X] {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    (G : SimpleGraph X) (r : ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (strict : G.edgeSet.ncard < rowEnergy n m r)
    (allNext : ∀ v : X, rowEnergy n m (r+1) ≤ (G.induce {x | x≠v}).edgeSet.ncard) :
    2 ≤ rowCount s t r ∧ G.edgeSet.ncard+1 = rowEnergy n m r ∧
    matchingEdges G < rowCount s t r ∧
    (∀ v : X, Nat.card (G.neighborSet v) ≤ diagonal n m (r+2)-1) ∧
    (∃ v : X, Nat.card (G.neighborSet v) = diagonal n m (r+2)-1) ∧
    ∀ (i : Fin s) (j : Fin t), i.val+j.val=r → diagonal n m (r+2)=n i+m j-1 →
      2≤n i ∧ 2≤m j := by
  have nonzero : 0 < rowCount s t r := by
    by_contra! bad
    have z : rowCount s t r=0 := by omega
    simp [rowEnergy,z] at strict
  have live : r<s+t-1 := by unfold rowCount at nonzero; omega
  have rank : 2 ≤ rowCount s t r := by
    by_contra! h
    exact (not_lt_of_ge (row_energy_last hs ht n m pn pm G r (by omega) row)) strict
  have energyStep := rowEnergy_succ n m r nonzero
  have edges (v : X) := card_neighbor_add_induce_edge_ncard G v
  have upper (v : X) : Nat.card (G.neighborSet v) < diagonal n m (r+2) := by
    have := allNext v
    have := edges v
    omega
  obtain ⟨v,peak⟩ := vertex_at_row_peak G hs ht n m pn pm live row
  have top := upper v
  have energy := allNext v
  have ed := edges v
  have pay := row_energy_budget hs ht n m hn hm pn pm G r row
  refine ⟨rank,by omega,by omega,(fun w => by have := upper w; omega),⟨v,by omega⟩,?_⟩
  intro i j ij att
  by_contra! fail
  have one : n i=1 ∨ m j=1 := by have := pn i; have := pm j; omega
  obtain ⟨w,hi⟩ := vertex_at_unit_peak G n m pn pm row i j ij att one
  exact (not_lt_of_ge hi) (upper w)

/-- No global minimal-counterexample choice is necessary for these
    restrictions: take the largest deleted subset that still has a strict row. -/
theorem maximal_strict_deletion {X : Type*} [Finite X] {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (G : SimpleGraph X) (r : ℕ) (strict : G.edgeSet.ncard < rowEnergy n m r) :
    ∃ U : Finset X, let Y := G.induce {x | x∉U}; let j := r+U.card
      Y.edgeSet.ncard < rowEnergy n m j ∧
      ∀ v, rowEnergy n m (j+1) ≤ (Y.induce {x | x≠v}).edgeSet.ncard := by
  classical
  let _ := Fintype.ofFinite X
  let bad (U : Finset X) := (G.induce {x | x∉U}).edgeSet.ncard < rowEnergy n m (r+U.card)
  let family := (Finset.univ : Finset (Finset X)).filter bad
  have mem (U : Finset X) : U∈family ↔ bad U := by simp [family]
  have empty : bad ∅ := by
    have eq : G.edgeSet.ncard=(G.induce {x | x∉(∅ : Finset X)}).edgeSet.ncard :=
      Nat.card_congr (induce_delete_empty_iso G).mapEdgeSet
    simpa only [bad,Finset.card_empty,Nat.add_zero,← eq] using strict
  obtain ⟨U,hU,most⟩ := Finset.exists_max_image family Finset.card ⟨∅,(mem ∅).mpr empty⟩
  refine ⟨U,(mem U).mp hU,?_⟩
  intro v
  have notBad : ¬bad (insert v.val U) := by
    intro h
    have hcard := most _ ((mem _).mpr h)
    rw [Finset.card_insert_of_notMem v.property] at hcard
    omega
  have eq := Nat.card_congr (induce_delete_insert_iso G U v.val v.property).mapEdgeSet
  change ((G.induce {x | x∉U}).induce {x | x≠v}).edgeSet.ncard =
    (G.induce {x | x∉insert v.val U}).edgeSet.ncard at eq
  change rowEnergy n m (r+U.card+1) ≤ _
  rw [eq]
  change ¬ _ < _ at notBad
  simpa only [Finset.card_insert_of_notMem v.property,Nat.add_assoc] using (le_of_not_gt notBad)

#print axioms strict_local_normal
#print axioms maximal_strict_deletion
end JSP452Audit.StarHost
