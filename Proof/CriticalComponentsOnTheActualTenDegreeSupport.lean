import AnOptimalBarrierContainingThePrescribedRoots
namespace JSP452Audit.StarHost.TenOuterCut
open SimpleGraph JSP452Audit.Padded
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

def sourceInside : Set ↥K.support := {x|x.val∈K.S}

structure InnerBarrier where
  roots : Set ↥K.support
  contains : K.sourceInside⊆roots
  tight : IsTightBarrier (G.induce K.support) roots
  critical : ∀c:((G.induce K.support).induce rootsᶜ).ConnectedComponent,
    Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph

theorem inner_barrier_exists (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) : Nonempty K.InnerBarrier := by
  let A := K.sourceInside
  let W := G.induce K.support
  let lift : A ≃ K.S := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,Or.inl (Or.inl x.property)⟩,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let iso : W.induce Aᶜ ≃g G.induce (K.support\K.S) := {
    toFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
    invFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }
  have rank := (K.exact_support_matching_rank cap M hm attained).2.2 K.S Set.Subset.rfl
  have order : A.ncard=K.S.ncard := Nat.card_congr lift
  have eq : matchingEdges W=A.ncard+matchingEdges (W.induce Aᶜ) := by rw [order,rank_eq_of_graph_iso iso];exact rank
  obtain ⟨B,inc,tight,crit⟩ := critical_barrier_after_prescribed_rank_loss W A eq
  exact ⟨⟨B,inc,tight,crit⟩⟩

theorem inner_barrier_component_account (B:K.InnerBarrier) (cap:∀x,Nat.card (G.neighborSet x)≤10)
    (M:G.Subgraph) (hm:M.IsMatching) (attained:(exposedFull G M 10).ncard=K.score+2) :
    let W := G.induce K.support
    let Q := W.induce B.rootsᶜ
    (Set.univ:Set Q.ConnectedComponent).ncard=B.roots.ncard+K.score+2+K.rootDefect K.T+K.targetPorts ∧
    matchingEdges W=B.roots.ncard+matchingEdges Q := by
  intro W Q
  have rank := tight_deletes_rank W B.roots B.roots B.tight Set.Subset.rfl
  have size := (K.exact_support_matching_rank cap M hm attained).2.1
  have base := minUnmatched_add_twice_matching W
  change minUnmatched W+2*matchingEdges W=K.support.ncard at base
  change 2*matchingEdges W+K.score+2+K.rootDefect K.T+K.targetPorts=K.support.ncard at size
  have all : Q.oddComponents=Set.univ := Set.eq_univ_of_forall (fun c => (B.critical c).1)
  have tight := B.tight
  change Q.oddComponents.ncard=B.roots.ncard+minUnmatched W at tight
  rw [all] at tight
  exact ⟨by omega,rank⟩

#print axioms inner_barrier_exists
#print axioms inner_barrier_component_account
end JSP452Audit.StarHost.TenOuterCut
