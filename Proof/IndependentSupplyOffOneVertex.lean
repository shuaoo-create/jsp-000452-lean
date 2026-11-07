import StrictIsolatedSevenCliqueExcluded
namespace JSP452Audit.StarHost
open SimpleGraph

theorem proper_set_exit {X:Type*} [Finite X] (G:SimpleGraph X) (conn:G.Preconnected)
    (T:Set X) (inside:T.Nonempty) (a:X) (outside:a∉T) :
    ∃v∈T,∃w,G.Adj v w ∧ w∉T := by
  by_contra! trapped
  obtain ⟨v,hv⟩ := inside
  have closed := cubic_closed_component G T v hv (fun x hx y edge => trapped x hx y edge)
  have same : a∈(G.connectedComponentMk v).supp := ConnectedComponent.sound (conn a v)
  exact outside (closed same)

theorem independent_supply_proper_subset {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ)
    (conn:G.Preconnected) (cap:∀v,Nat.card (G.neighborSet v)≤D) (a:X)
    (T:Set X) (outside:a∉T) :
    ∃I:Set X,I⊆T ∧ G.IsIndepSet I ∧ T.ncard≤D*I.ncard := by
  classical
  suffices go : ∀k:ℕ,∀U:Set X,U.ncard=k → a∉U → ∃I:Set X,I⊆U ∧ G.IsIndepSet I ∧ U.ncard≤D*I.ncard from
    go _ T rfl outside
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro U size away
    rcases U.eq_empty_or_nonempty with rfl|non
    · exact ⟨∅,Set.Subset.rfl,Set.pairwise_empty _,by simp⟩
    obtain ⟨v,hv,w,edge,out⟩ := proper_set_exit G conn U non a away
    let N := G.neighborSet v∩U
    let L := insert v N
    let R := U\L
    have strict : N⊂G.neighborSet v :=
      ⟨Set.inter_subset_left,fun back => out (back edge).2⟩
    have localCount := Set.ncard_lt_ncard strict
    have degree : (G.neighborSet v).ncard≤D := cap v
    have loss : L.ncard≤D := by have add := Set.ncard_insert_le v N;change (insert v N).ncard≤D;omega
    have smaller : R⊂U := ⟨Set.sdiff_subset,fun back => (back hv).2 (Set.mem_insert _ _)⟩
    have fewer : R.ncard<k := (Set.ncard_lt_ncard smaller).trans_eq size
    obtain ⟨I,sub,ind,ample⟩ := ih _ fewer R rfl (fun mem => away mem.1)
    have fresh : v∉I := fun mem => (sub mem).2 (Set.mem_insert _ _)
    have independent : G.IsIndepSet (insert v I) := by
      apply Set.Pairwise.insert ind
      intro y hy _
      have no : ¬G.Adj v y := fun e => (sub hy).2 (Set.mem_insert_of_mem _ ⟨e,(sub hy).1⟩)
      exact ⟨no,fun e => no e.symm⟩
    have cost : U.ncard≤R.ncard+L.ncard := Set.ncard_le_ncard_sdiff_add_ncard U L
    refine ⟨insert v I,Set.insert_subset hv (fun _ h => (sub h).1),independent,?_⟩
    rw [Set.ncard_insert_of_notMem fresh,Nat.mul_succ]
    omega

#print axioms proper_set_exit
#print axioms independent_supply_proper_subset
end JSP452Audit.StarHost
