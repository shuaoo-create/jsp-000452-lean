import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Each chosen vertex removes itself and at most D neighbors from the
available set. It suffices to bound original degrees at vertices of U. -/
theorem greedy_independent_of_local_cap {X : Type*} [Finite X] (G : SimpleGraph X) (D k : ℕ)
    (U : Set X) (cap : ∀ x ∈ U, Nat.card (G.neighborSet x) ≤ D)
    (enough : (D+1)*k < U.ncard) :
    ∃ I : Set X, I ⊆ U ∧ G.IsIndepSet I ∧ I.ncard = k+1 := by
  classical
  induction k generalizing U with
  | zero =>
      have pos : 0 < U.ncard := by simpa only [Nat.mul_zero] using enough
      obtain ⟨x,mem⟩ := (Set.ncard_pos U.toFinite).mp pos
      exact ⟨{x},Set.singleton_subset_iff.mpr mem,Set.pairwise_singleton _ _,Set.ncard_singleton _⟩
  | succ k ih =>
      obtain ⟨x,mem⟩ := (Set.ncard_pos U.toFinite).mp (Nat.zero_lt_of_lt enough)
      let closed := insert x (G.neighborSet x)
      let rest := U \ closed
      have cost : closed.ncard ≤ D+1 := (Set.ncard_insert_le x _).trans (Nat.add_le_add_right (cap x mem) 1)
      have available : U.ncard ≤ rest.ncard + closed.ncard := Set.ncard_le_ncard_sdiff_add_ncard U closed
      rw [Nat.mul_succ] at enough
      obtain ⟨I,sub,ind,size⟩ := ih rest (fun v hv => cap v hv.1) (by omega)
      have fresh : x ∉ I := fun hx => (sub hx).2 (Set.mem_insert _ _)
      have unionInd : G.IsIndepSet (insert x I) := by
        apply Set.Pairwise.insert ind
        intro y hy _
        have nonedge : ¬ G.Adj x y := fun e => (sub hy).2 (Set.mem_insert_of_mem _ e)
        exact ⟨nonedge,fun e => nonedge e.symm⟩
      exact ⟨insert x I,Set.insert_subset mem (fun _ h => (sub h).1),unionInd,
        by rw [Set.ncard_insert_of_notMem fresh,size]⟩

/-- Choose an exact prescribed number of original available vertices, all
pairwise nonadjacent in the original graph. Includes b=0 and k=0. -/
theorem greedy_independent_exact {X : Type*} [Finite X] (G : SimpleGraph X) (D k b : ℕ)
    (U : Set X) (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D)
    (enough : (D+1)*k < U.ncard) (count : b ≤ k+1) :
    ∃ I : Set X, I ⊆ U ∧ G.IsIndepSet I ∧ I.ncard = b := by
  obtain ⟨J,sub,ind,size⟩ := greedy_independent_of_local_cap G D k U (fun x _ => cap x) enough
  obtain ⟨I,inJ,card⟩ := Set.exists_subset_card_eq (count.trans_eq size.symm)
  exact ⟨I,inJ.trans sub,Set.Pairwise.mono inJ ind,card⟩

#print axioms greedy_independent_of_local_cap
#print axioms greedy_independent_exact
end JSP452Audit.StarHost
