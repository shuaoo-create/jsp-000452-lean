import OriginalBoundaryOfPositivePiece
namespace JSP452Audit.StarHost
open SimpleGraph

theorem independent_supply_with_short_vertex {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ)
    (conn:G.Preconnected) (cap:∀v,Nat.card (G.neighborSet v)≤D) (v:X)
    (short:Nat.card (G.neighborSet v)<D) :
    ∃I:Set X,G.IsIndepSet I ∧ Nat.card X≤D*I.ncard := by
  let N := insert v (G.neighborSet v)
  have size : N.ncard≤D := (Set.ncard_insert_le v _).trans (by change (G.neighborSet v).ncard+1≤D;exact short)
  obtain ⟨I,sub,ind,enough⟩ := independent_supply_proper_subset G D conn cap v Nᶜ (by simp [N])
  have fresh : v∉I := fun h => sub h (Set.mem_insert _ _)
  have newInd : G.IsIndepSet (insert v I) := by
    apply Set.Pairwise.insert ind
    intro y hy _
    have no : ¬G.Adj v y := fun e => sub hy (Set.mem_insert_of_mem _ e)
    exact ⟨no,fun e => no e.symm⟩
  have add := Set.ncard_add_ncard_compl N
  refine ⟨insert v I,newInd,?_⟩
  rw [Set.ncard_insert_of_notMem fresh,Nat.mul_succ]
  omega

theorem independent_supply_in_odd_component {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ)
    (conn:G.Preconnected) (cap:∀v,Nat.card (G.neighborSet v)≤D) (oddCap:Odd D) (oddOrder:Odd (Nat.card X)) :
    ∃I:Set X,G.IsIndepSet I ∧ Nat.card X≤D*I.ncard := by
  have existsLow : ∃v,Nat.card (G.neighborSet v)<D := by
    by_contra! none
    have even := regular_even_on_odd G D oddOrder (fun x => le_antisymm (cap x) (none x))
    exact (Nat.not_even_iff_odd.mpr oddCap) even
  obtain ⟨v,short⟩ := existsLow
  exact independent_supply_with_short_vertex G D conn cap v short

#print axioms independent_supply_with_short_vertex
#print axioms independent_supply_in_odd_component
end JSP452Audit.StarHost
